#!/usr/bin/env python3
"""Fill BrickStore's price-guide cache using your own BrickLink API keys.

Quit BrickStore before running. The cache file stays open while the app
is running, and BrickStore's Update button still uses the shared affiliate
key and will overwrite rows this script wrote.

Prices are stored in USD, excluding VAT. In BrickStore, set the price guide
to VAT excluded. That view reads cache ids ending in @B0.

Setup:
  cp bricklink.env.example bricklink.env
  # paste the four keys from your BrickLink API consumer

Try one item, then the whole file:
  python3 priceguide.py --limit 1 /path/to/store.bsx
  python3 priceguide.py /path/to/store.bsx
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import hmac
import json
import os
import sqlite3
import struct
import subprocess
import sys
import time
import urllib.error
import urllib.request
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import quote

API_ORIGIN = "https://api.bricklink.com"
BLOB_STRUCT = struct.Struct("<4i4i16d")
BLOB_SIZE = BLOB_STRUCT.size  # 160, matches BrickStore's PriceGuide::Data
VAT_EXCLUDED = 0
RETRIEVER_ID = "B"

# BrickStore single-letter type -> catalog path segment used by the store API.
TYPE_TO_API = {
    "P": "part",
    "S": "set",
    "M": "minifig",
    "B": "book",
    "G": "gear",
    "C": "catalog",
    "I": "instruction",
    "O": "original_box",
    "U": "unsorted_lot",
}

# (guide_type, new_or_used, time index, condition index)
# time: 0 = last 6 months, 1 = current. condition: 0 = new, 1 = used.
SLICES = (
    ("sold", "N", 0, 0),
    ("sold", "U", 0, 1),
    ("stock", "N", 1, 0),
    ("stock", "U", 1, 1),
)

ENV_NAMES = (
    "BRICKLINK_CONSUMER_KEY",
    "BRICKLINK_CONSUMER_SECRET",
    "BRICKLINK_TOKEN",
    "BRICKLINK_TOKEN_SECRET",
)

DEFAULT_CACHE = Path.home() / "Library/Caches/BrickStore/priceguide_cache.sqlite"
STATE_PATH = Path(__file__).resolve().parent / ".priceguide-state.json"


class BrickLinkError(Exception):
    """A price-guide call failed for one item."""


class BrickLinkStop(Exception):
    """Stop the run. Credentials or the daily cap will not succeed on retry."""


@dataclass(frozen=True)
class Lot:
    type_id: str
    item_id: str
    color_id: int

    @property
    def api_type(self) -> str:
        return TYPE_TO_API[self.type_id]

    @property
    def cache_id(self) -> str:
        # Same text key BrickStore writes: type + item + @color + @retriever + vat.
        return f"{self.type_id}{self.item_id}@{self.color_id}@{RETRIEVER_ID}{VAT_EXCLUDED}"

    @property
    def label(self) -> str:
        return f"{self.type_id} {self.item_id} color {self.color_id}"


@dataclass
class Document:
    lot_count: int
    unique: list[Lot]
    warnings: list[str]


@dataclass(frozen=True)
class Credentials:
    consumer_key: str
    consumer_secret: str
    token: str
    token_secret: str


def percent_encode(value: str) -> str:
    # RFC 3986 unreserved characters stay literal. quote() already leaves "~".
    return quote(str(value), safe="")


def signature_base(method: str, base_url: str, params: list[tuple[str, str]]) -> str:
    encoded = sorted((percent_encode(key), percent_encode(value)) for key, value in params)
    param_string = "&".join(f"{key}={value}" for key, value in encoded)
    return "&".join((method.upper(), percent_encode(base_url), percent_encode(param_string)))


def oauth_signature(
    method: str,
    base_url: str,
    params: list[tuple[str, str]],
    credentials: Credentials,
) -> str:
    base = signature_base(method, base_url, params)
    key = percent_encode(credentials.consumer_secret) + "&" + percent_encode(credentials.token_secret)
    digest = hmac.new(key.encode("utf-8"), base.encode("utf-8"), hashlib.sha1).digest()
    return base64.b64encode(digest).decode("ascii")


def authorization_header(
    method: str,
    base_url: str,
    query: list[tuple[str, str]],
    credentials: Credentials,
    timestamp: str,
    nonce: str,
) -> str:
    oauth_params = [
        ("oauth_consumer_key", credentials.consumer_key),
        ("oauth_nonce", nonce),
        ("oauth_signature_method", "HMAC-SHA1"),
        ("oauth_timestamp", timestamp),
        ("oauth_token", credentials.token),
        ("oauth_version", "1.0"),
    ]
    signature = oauth_signature(method, base_url, query + oauth_params, credentials)
    header_params = oauth_params + [("oauth_signature", signature)]
    rendered = ", ".join(
        f'{name}="{percent_encode(value)}"' for name, value in header_params
    )
    return f'OAuth realm="", {rendered}'


def _local(tag: str) -> str:
    return tag.rsplit("}", 1)[-1]


def _child_text(elem: ET.Element, name: str) -> str | None:
    for child in list(elem):
        if _local(child.tag) == name:
            return (child.text or "").strip()
    return None


def _lot_from_item(elem: ET.Element) -> tuple[Lot | None, str | None]:
    item_id = _child_text(elem, "ItemID")
    type_id = _child_text(elem, "ItemTypeID")
    color_text = _child_text(elem, "ColorID")
    if not item_id or not type_id or color_text is None or color_text == "":
        return None, "skipped a lot missing ItemID, ItemTypeID, or ColorID"
    type_id = type_id.upper()
    if type_id not in TYPE_TO_API:
        return None, f"skipped {type_id} {item_id}: unsupported item type"
    try:
        color_id = int(color_text)
    except ValueError:
        return None, f"skipped {type_id} {item_id}: ColorID {color_text!r} is not an integer"
    return Lot(type_id, item_id, color_id), None


def parse_document(path: Path) -> Document:
    unique: list[Lot] = []
    seen: set[tuple[str, str, int]] = set()
    warnings: list[str] = []
    lot_count = 0
    stack: list[ET.Element] = []
    for event, elem in ET.iterparse(path, events=("start", "end")):
        if event == "start":
            stack.append(elem)
            continue
        is_lot = (
            _local(elem.tag) == "Item"
            and len(stack) >= 2
            and _local(stack[-2].tag) == "Inventory"
        )
        if is_lot:
            lot_count += 1
            lot, warning = _lot_from_item(elem)
            if warning:
                warnings.append(warning)
            elif lot is not None:
                key = (lot.type_id, lot.item_id, lot.color_id)
                if key not in seen:
                    seen.add(key)
                    unique.append(lot)
        stack.pop()
        if _local(elem.tag) == "Item":
            elem.clear()
    if lot_count == 0:
        raise BrickLinkError(f"{path} has no Inventory lots")
    return Document(lot_count, unique, warnings)


def pack_guide(slices: dict[tuple[int, int], dict]) -> bytes:
    """Pack the four price slices the way BrickStore stores them.

    quantities[] receives unit_quantity and lots[] receives total_quantity,
    matching the affiliate retriever. Price order is lowest, average,
    quantity-weighted average, highest.
    """
    quantities = [0, 0, 0, 0]
    lots = [0, 0, 0, 0]
    prices = [0.0] * 16
    for time_index, condition_index in ((0, 0), (0, 1), (1, 0), (1, 1)):
        data = slices.get((time_index, condition_index))
        if not data:
            continue
        slot = time_index * 2 + condition_index
        quantities[slot] = int(data.get("unit_quantity") or 0)
        lots[slot] = int(data.get("total_quantity") or 0)
        base = slot * 4
        prices[base] = _number(data.get("min_price"))
        prices[base + 1] = _number(data.get("avg_price"))
        prices[base + 2] = _number(data.get("qty_avg_price"))
        prices[base + 3] = _number(data.get("max_price"))
    blob = BLOB_STRUCT.pack(*quantities, *lots, *prices)
    if len(blob) != BLOB_SIZE:
        raise BrickLinkError(f"price blob is {len(blob)} bytes, BrickStore expects {BLOB_SIZE}")
    return blob


def _number(value) -> float:
    if value is None or value == "":
        return 0.0
    return float(value)


class PriceCache:
    def __init__(self, path: Path, read_only: bool):
        self.path = path
        if read_only:
            uri = path.resolve().as_uri() + "?mode=ro"
            self.conn = sqlite3.connect(uri, uri=True, timeout=2)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            self.conn = sqlite3.connect(path, timeout=2)
            self.conn.execute("PRAGMA journal_mode=WAL")
            self.conn.execute(
                """
                CREATE TABLE IF NOT EXISTS pg (
                    id TEXT NOT NULL PRIMARY KEY,
                    updated INTEGER,
                    accessed INTEGER NOT NULL,
                    data BLOB
                ) WITHOUT ROWID
                """
            )
            version = self.conn.execute("PRAGMA user_version").fetchone()[0]
            if version == 0:
                self.conn.execute("PRAGMA user_version=1")
            self.conn.commit()

    def updated_at(self, cache_id: str) -> int | None:
        row = self.conn.execute(
            "SELECT updated, length(data) FROM pg WHERE id = ?",
            (cache_id,),
        ).fetchone()
        if row is None or row[0] is None or row[1] != BLOB_SIZE:
            return None
        return int(row[0])

    def write(self, cache_id: str, blob: bytes, now_ms: int) -> None:
        self.conn.execute(
            """
            INSERT INTO pg(id, updated, accessed, data)
            VALUES (?, ?, ?, ?)
            ON CONFLICT(id) DO UPDATE SET
                updated = excluded.updated,
                accessed = excluded.accessed,
                data = excluded.data
            """,
            (cache_id, now_ms, now_ms, blob),
        )
        self.conn.commit()

    def close(self) -> None:
        try:
            self.conn.execute("PRAGMA wal_checkpoint(TRUNCATE)")
        except sqlite3.DatabaseError:
            pass
        self.conn.close()


def is_fresh(updated_ms: int | None, now_ms: int, max_age_hours: float) -> bool:
    if updated_ms is None:
        return False
    age_hours = (now_ms - updated_ms) / 3_600_000
    return age_hours < max_age_hours


class CallBudget:
    def __init__(self, path: Path, max_calls: int, today: str | None = None):
        self.path = path
        self.max_calls = max_calls
        self.today = today or datetime.now(timezone.utc).date().isoformat()
        self.calls = 0
        if path.exists():
            try:
                saved = json.loads(path.read_text())
            except (OSError, json.JSONDecodeError):
                saved = {}
            if saved.get("date") == self.today:
                self.calls = int(saved.get("calls") or 0)

    @property
    def remaining(self) -> int:
        return self.max_calls - self.calls

    def consume(self) -> None:
        if self.calls >= self.max_calls:
            raise BrickLinkStop(
                f"daily call cap of {self.max_calls} is already used ({self.calls} today, UTC)"
            )
        self.calls += 1
        self.path.write_text(json.dumps({"date": self.today, "calls": self.calls}))


class BrickLinkClient:
    def __init__(self, credentials: Credentials, currency: str, delay: float):
        self.credentials = credentials
        self.currency = currency
        self.delay = delay

    def price_slice(self, lot: Lot, guide_type: str, condition: str) -> dict:
        base_url = (
            f"{API_ORIGIN}/api/store/v1/items/{lot.api_type}/"
            f"{percent_encode(lot.item_id)}/price"
        )
        query = [
            ("color_id", str(lot.color_id)),
            ("currency_code", self.currency),
            ("guide_type", guide_type),
            ("new_or_used", condition),
        ]
        timestamp = str(int(time.time()))
        nonce = hashlib.sha1(f"{timestamp}-{time.time_ns()}".encode()).hexdigest()[:16]
        header = authorization_header("GET", base_url, query, self.credentials, timestamp, nonce)
        query_string = "&".join(f"{percent_encode(k)}={percent_encode(v)}" for k, v in query)
        request = urllib.request.Request(
            base_url + "?" + query_string,
            headers={
                "Authorization": header,
                "Accept": "application/json",
                "User-Agent": "ganora-priceguide/1.0",
            },
            method="GET",
        )
        try:
            with urllib.request.urlopen(request, timeout=30) as response:
                status = response.status
                raw = response.read()
        except urllib.error.HTTPError as error:
            status = error.code
            raw = error.read()
        except urllib.error.URLError as error:
            raise BrickLinkError(f"network error: {error.reason}") from error
        if self.delay:
            time.sleep(self.delay)
        return _parse_response(status, raw, lot, guide_type, condition)


def _parse_response(status: int, raw: bytes, lot: Lot, guide_type: str, condition: str) -> dict:
    text = raw.decode("utf-8", errors="replace")
    try:
        payload = json.loads(text) if text else {}
    except json.JSONDecodeError as error:
        raise BrickLinkError(f"HTTP {status}, response was not JSON: {text[:200]}") from error
    meta = payload.get("meta") if isinstance(payload, dict) else None
    if not isinstance(meta, dict):
        meta = payload if isinstance(payload, dict) else {}
    code = _meta_code(meta, status)
    message = str(meta.get("message") or "")
    description = str(meta.get("description") or "")
    detail = " ".join(part for part in (message, description) if part).strip()
    where = f"{lot.label} {guide_type} {condition}"
    if code in (401, 403):
        raise BrickLinkStop(f"BrickLink rejected the API keys ({code} {detail})".strip())
    if code == 429 or "TOO_MANY" in message.upper():
        raise BrickLinkStop(f"BrickLink rate limit reached ({code} {detail})".strip())
    if code == 404:
        raise BrickLinkError(f"{where}: not in the BrickLink catalog")
    if code < 200 or code >= 300:
        raise BrickLinkError(f"{where}: HTTP {status} {detail}".strip())
    data = payload.get("data") if isinstance(payload, dict) else None
    if not isinstance(data, dict):
        raise BrickLinkError(f"{where}: response had no price data")
    return data


def _meta_code(meta: dict, status: int) -> int:
    raw = meta.get("code", status)
    try:
        return int(raw)
    except (TypeError, ValueError):
        return status


def brickstore_is_running() -> bool:
    try:
        result = subprocess.run(
            ["pgrep", "-x", "BrickStore"],
            check=False,
            capture_output=True,
        )
    except OSError:
        return False
    return result.returncode == 0


def load_env_file(path: Path) -> None:
    if not path.is_file():
        return
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        name, value = line.split("=", 1)
        name = name.strip()
        value = value.strip()
        if len(value) >= 2 and value[0] == value[-1] and value[0] in {'"', "'"}:
            value = value[1:-1]
        if name and value and not os.environ.get(name):
            os.environ[name] = value


def load_credentials() -> Credentials:
    script_dir = Path(__file__).resolve().parent
    explicit = os.environ.get("BRICKLINK_ENV")
    if explicit:
        load_env_file(Path(explicit))
    load_env_file(Path.cwd() / "bricklink.env")
    load_env_file(script_dir / "bricklink.env")
    values = {name: os.environ.get(name, "").strip() for name in ENV_NAMES}
    missing = [name for name, value in values.items() if not value]
    if missing:
        raise BrickLinkError(
            "missing "
            + ", ".join(missing)
            + ". Copy bricklink.env.example to bricklink.env and paste your four API values."
        )
    return Credentials(
        values["BRICKLINK_CONSUMER_KEY"],
        values["BRICKLINK_CONSUMER_SECRET"],
        values["BRICKLINK_TOKEN"],
        values["BRICKLINK_TOKEN_SECRET"],
    )


def update_prices(
    document: Document,
    cache: PriceCache,
    client: BrickLinkClient,
    budget: CallBudget,
    max_age_hours: float,
    limit: int | None,
    dry_run: bool,
) -> int:
    now_ms = int(time.time() * 1000)
    fresh = 0
    updated = 0
    failed = 0
    considered = 0
    for warning in document.warnings[:20]:
        print(f"warning: {warning}")
    extra = len(document.warnings) - 20
    if extra > 0:
        print(f"warning: {extra} more parse warnings")

    for lot in document.unique:
        updated_at = None
        try:
            updated_at = cache.updated_at(lot.cache_id)
        except sqlite3.DatabaseError as error:
            raise BrickLinkError(
                f"could not read {cache.path}. Quit BrickStore and run this again. ({error})"
            ) from error
        if is_fresh(updated_at, now_ms, max_age_hours):
            fresh += 1
            continue
        if limit is not None and considered >= limit:
            print(f"stopped after --limit {limit}")
            break
        calls_needed = len(SLICES)
        if budget.remaining < calls_needed:
            print(
                f"stopped: {budget.remaining} calls left today and each item needs "
                f"{calls_needed}. Cap is {budget.max_calls} (UTC day)."
            )
            break
        considered += 1
        if dry_run:
            print(f"would update {lot.cache_id}  ({lot.label})")
            continue
        print(f"fetching {lot.label}")
        slices: dict[tuple[int, int], dict] = {}
        try:
            for guide_type, condition, time_index, condition_index in SLICES:
                budget.consume()
                slices[(time_index, condition_index)] = client.price_slice(lot, guide_type, condition)
        except BrickLinkError as error:
            failed += 1
            print(f"  failed: {error}")
            continue
        blob = pack_guide(slices)
        try:
            cache.write(lot.cache_id, blob, now_ms)
        except sqlite3.DatabaseError as error:
            raise BrickLinkError(
                f"could not write {cache.path}. Quit BrickStore and run this again. ({error})"
            ) from error
        updated += 1
        current_new = slices[(1, 0)]
        sold_new = slices[(0, 0)]
        print(
            f"  wrote {lot.cache_id}  "
            f"6mo new avg {_number(sold_new.get('avg_price')):.4f}  "
            f"current new avg {_number(current_new.get('avg_price')):.4f}"
        )

    action = "would update" if dry_run else "updated"
    print(
        f"\n{document.lot_count} lots, {len(document.unique)} unique item/colors\n"
        f"fresh cache: {fresh}\n"
        f"{action}: {considered if dry_run else updated}\n"
        f"failed: {failed}\n"
        f"calls today: {budget.calls} / {budget.max_calls} (UTC)"
    )
    if failed and updated == 0 and not dry_run:
        return 1
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Write BrickLink price guides into BrickStore's local cache using your own API keys.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Quit BrickStore first. Prices are USD and exclude VAT; set BrickStore to VAT excluded.\n\n"
            "  cp bricklink.env.example bricklink.env\n"
            "  python3 priceguide.py --limit 1 /path/to/store.bsx\n"
            "  python3 priceguide.py /path/to/store.bsx"
        ),
    )
    parser.add_argument("document", nargs="?", type=Path, help="BrickStore .bsx file")
    parser.add_argument("--cache", type=Path, default=DEFAULT_CACHE, help=f"default: {DEFAULT_CACHE}")
    parser.add_argument("--max-age-hours", type=float, default=24, help="skip cache rows newer than this (0 refreshes all)")
    parser.add_argument("--max-calls", type=int, default=4500, help="stop before this many calls in the current UTC day")
    parser.add_argument("--limit", type=int, default=None, help="update at most this many item/colors")
    parser.add_argument("--delay", type=float, default=0.25, help="seconds to wait between API calls")
    parser.add_argument("--currency", default="USD", help="currency_code sent to BrickLink (default USD)")
    parser.add_argument("--dry-run", action="store_true", help="show what would be fetched without calling BrickLink")
    parser.add_argument("--self-test", action="store_true", help="check the signer, parser, and cache blob locally")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.self_test:
        run_self_test()
        print("self-test ok")
        return 0
    if args.document is None:
        build_parser().error("a .bsx file is required")
    if not args.document.is_file():
        print(f"file not found: {args.document}", file=sys.stderr)
        return 2
    if args.limit is not None and args.limit < 1:
        print("--limit must be at least 1", file=sys.stderr)
        return 2
    same_cache = args.cache.expanduser().resolve() == DEFAULT_CACHE.resolve()
    if same_cache and brickstore_is_running():
        print("Quit BrickStore first. It has the price-guide cache open.", file=sys.stderr)
        return 1
    cache_path = args.cache.expanduser().resolve()
    try:
        document = parse_document(args.document)
        if args.dry_run:
            client: BrickLinkClient = _DryRunClient()
        else:
            client = BrickLinkClient(load_credentials(), args.currency.upper(), args.delay)
        if args.dry_run and not cache_path.exists():
            print(f"cache does not exist yet: {cache_path}")
            print(
                f"{document.lot_count} lots, {len(document.unique)} unique item/colors would be fetched"
            )
            return 0
        cache = PriceCache(cache_path, read_only=args.dry_run)
    except (BrickLinkError, ET.ParseError, sqlite3.DatabaseError, OSError) as error:
        print(str(error), file=sys.stderr)
        return 1
    budget = CallBudget(STATE_PATH, args.max_calls)
    try:
        return update_prices(
            document,
            cache,
            client,
            budget,
            args.max_age_hours,
            args.limit,
            args.dry_run,
        )
    except BrickLinkStop as error:
        print(str(error), file=sys.stderr)
        return 1
    finally:
        cache.close()


class _DryRunClient(BrickLinkClient):
    def __init__(self):
        pass

    def price_slice(self, lot: Lot, guide_type: str, condition: str) -> dict:
        raise BrickLinkError("dry-run tried to call BrickLink")


def run_self_test() -> None:
    _test_rfc_signature()
    _test_parse_and_cache()
    _test_budget_and_skip()


def _test_rfc_signature() -> None:
    params = [
        ("b5", "=%3D"),
        ("a3", "a"),
        ("c@", ""),
        ("a2", "r b"),
        ("c2", ""),
        ("a3", "2 q"),
        ("oauth_consumer_key", "9djdj82h48djs9d2"),
        ("oauth_token", "kkk9d7dh3k39sjv7"),
        ("oauth_signature_method", "HMAC-SHA1"),
        ("oauth_timestamp", "137131201"),
        ("oauth_nonce", "7d8f3e4a"),
    ]
    credentials = Credentials("9djdj82h48djs9d2", "j49sk3j29djd", "kkk9d7dh3k39sjv7", "dh893hdasih9")
    base = signature_base("POST", "http://example.com/request", params)
    # RFC 5849 section 3.4.1. The printed example signature in the RFC is wrong;
    # the HMAC of this base string is the value recorded in erratum 2557.
    expected_base = (
        "POST&http%3A%2F%2Fexample.com%2Frequest&a2%3Dr%2520b%26a3%3D2%2520q"
        "%26a3%3Da%26b5%3D%253D%25253D%26c%2540%3D%26c2%3D%26oauth_consumer_key"
        "%3D9djdj82h48djs9d2%26oauth_nonce%3D7d8f3e4a%26oauth_signature_method"
        "%3DHMAC-SHA1%26oauth_timestamp%3D137131201%26oauth_token%3Dkkk9d7dh3k39sjv7"
    )
    if base != expected_base:
        raise AssertionError(f"signature base string mismatch:\n{base}")
    signature = oauth_signature("POST", "http://example.com/request", params, credentials)
    expected = "r6/TJjbCOr97/+UU0NsvSne7s5g="
    if signature != expected:
        raise AssertionError(f"OAuth signature {signature} != {expected}")
    if BLOB_SIZE != 160:
        raise AssertionError(f"blob size {BLOB_SIZE} != 160")


def _test_parse_and_cache() -> None:
    import tempfile

    xml = """<?xml version="1.0" encoding="UTF-8"?>
    <BrickStoreXML>
      <Inventory Currency="USD">
        <Item>
          <ItemID>3001</ItemID>
          <ItemTypeID>P</ItemTypeID>
          <ColorID>5</ColorID>
          <Qty>10</Qty>
          <DifferenceBaseValues ItemID="3001old" ItemTypeID="P" ColorID="4"/>
        </Item>
        <Item>
          <ItemID>3001</ItemID>
          <ItemTypeID>P</ItemTypeID>
          <ColorID>5</ColorID>
        </Item>
        <Item>
          <ItemID>7644-1</ItemID>
          <ItemTypeID>S</ItemTypeID>
          <ColorID>0</ColorID>
        </Item>
      </Inventory>
    </BrickStoreXML>
    """
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        document_path = root / "store.bsx"
        document_path.write_text(xml)
        document = parse_document(document_path)
        if document.lot_count != 3 or len(document.unique) != 2:
            raise AssertionError(f"parse counts {document.lot_count} {len(document.unique)}")
        if document.unique[0].cache_id != "P3001@5@B0":
            raise AssertionError(document.unique[0].cache_id)
        if document.unique[1].cache_id != "S7644-1@0@B0":
            raise AssertionError(document.unique[1].cache_id)

        cache = PriceCache(root / "priceguide_cache.sqlite", read_only=False)
        client = _FakeClient()
        budget = CallBudget(root / "state.json", max_calls=4500, today="2026-11-13")
        code = update_prices(document, cache, client, budget, 24, limit=1, dry_run=False)
        if code != 0 or budget.calls != 4 or client.calls != 4:
            raise AssertionError(f"update code={code} calls={budget.calls} client={client.calls}")
        row = cache.conn.execute(
            "SELECT updated, data FROM pg WHERE id = ?",
            ("P3001@5@B0",),
        ).fetchone()
        if row is None or len(row[1]) != 160:
            raise AssertionError("cache row missing")
        unpacked = BLOB_STRUCT.unpack(row[1])
        # Past-six new is the first slot: unit_quantity, then lots at index 4, avg at price index 1.
        if unpacked[0] != 9 or unpacked[4] != 20 or abs(unpacked[9] - 0.25) > 1e-9:
            raise AssertionError(f"blob fields {unpacked[:12]}")
        cache.close()


def _test_budget_and_skip() -> None:
    import tempfile

    xml = """<BrickStockXML><Inventory>
      <Item><ItemID>3001</ItemID><ItemTypeID>P</ItemTypeID><ColorID>1</ColorID></Item>
    </Inventory></BrickStockXML>"""
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        path = root / "one.bsx"
        path.write_text(xml)
        document = parse_document(path)
        cache = PriceCache(root / "cache.sqlite", read_only=False)
        now_ms = int(time.time() * 1000)
        cache.write(document.unique[0].cache_id, pack_guide({}), now_ms)
        client = _FakeClient()
        budget = CallBudget(root / "state.json", max_calls=4, today="2026-11-13")
        update_prices(document, cache, client, budget, 24, limit=None, dry_run=False)
        if client.calls != 0:
            raise AssertionError("fresh row was fetched")
        client2 = _FakeClient()
        update_prices(document, cache, client2, budget, 0, limit=None, dry_run=False)
        if client2.calls != 4:
            raise AssertionError("stale refresh did not fetch")
        cache.close()


class _FakeClient(BrickLinkClient):
    def __init__(self):
        self.calls = 0

    def price_slice(self, lot: Lot, guide_type: str, condition: str) -> dict:
        self.calls += 1
        return {
            "min_price": "0.10",
            "max_price": "0.40",
            "avg_price": "0.25",
            "qty_avg_price": "0.22",
            "unit_quantity": 9,
            "total_quantity": 20,
        }


if __name__ == "__main__":
    sys.exit(main())
