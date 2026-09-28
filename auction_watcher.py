#!/usr/bin/env python3
"""
RealAuction watcher (realtaxdeed / realforeclose).

Pulls the auction list for upcoming sale dates, filters it, and sends a
Telegram and/or email alert for items it hasn't seen before.

Usage:
    python auction_watcher.py                   # live run
    python auction_watcher.py --sample x.json   # parse a saved response (no network, no alerts)
    python auction_watcher.py --dry-run         # live fetch, print instead of alerting
    python auction_watcher.py --folio 28-2202-029-2320   # test the land-use lookup

Alerts: one when a listing first appears, then reminders REMIND_DAYS before the sale (default 7 and 1).

Config comes from environment variables (see CONFIG below).
"""
import argparse
import html
import json
import os
import re
import smtplib
import sys
import time
from datetime import date, datetime, timedelta
from email.message import EmailMessage
from pathlib import Path

import requests

# ----------------------------------------------------------------------------
# CONFIG (environment variables)
# ----------------------------------------------------------------------------
# One or more RealAuction sites, comma-separated. Tax deeds by default; add
# https://www.miamidade.realforeclose.com to also watch foreclosure sales.
BASE_URLS = [u.strip().rstrip("/") for u in os.getenv("BASE_URL", "https://miamidade.realtaxdeed.com").split(",") if u.strip()]
# How the site works: opening a sale date's PREVIEW page stores that date in the
# session, then the LOAD call returns that date's items (the date is not in the LOAD URL).
PREVIEW_PATH = os.getenv("PREVIEW_PATH", "/index.cfm?zaction=AUCTION&Zmethod=PREVIEW&AUCTIONDATE={date}")
LOAD_PATH = os.getenv(
    "LOAD_PATH",
    "/index.cfm?zaction=AUCTION&Zmethod=UPDATE&FNC=LOAD&AREA=W&PageDir={page_dir}&doR=1&bypassPage=1&test=1",
)
MAX_PAGES = int(os.getenv("MAX_PAGES", "10"))
DATE_FORMAT = os.getenv("DATE_FORMAT", "%m/%d/%Y")
DAYS_AHEAD = int(os.getenv("DAYS_AHEAD", "45"))

AUCTION_TYPES = {t.strip().upper() for t in os.getenv("AUCTION_TYPES", "TAXDEED").split(",") if t.strip()}
MAX_BID = float(os.getenv("MAX_BID", "0") or 0)          # 0 = no limit
ZIPS = {z.strip() for z in os.getenv("ZIPS", "").split(",") if z.strip()}  # empty = any

SEEN_FILE = Path(os.getenv("SEEN_FILE", "seen.json"))
# Reminder alerts: days before the sale (default: a week before and a day before).
REMIND_DAYS = sorted({int(d) for d in os.getenv("REMIND_DAYS", "7,1").split(",") if d.strip()}, reverse=True)

TELEGRAM_TOKEN = os.getenv("TELEGRAM_TOKEN", "")
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "")
SMTP_USER = os.getenv("SMTP_USER", "")        # e.g. you@gmail.com
SMTP_PASS = os.getenv("SMTP_PASS", "")        # Gmail app password
EMAIL_TO = os.getenv("EMAIL_TO", SMTP_USER)

# Land-use lookup (Miami-Dade parcel layer, public ArcGIS REST, no key needed)
PA_LAYER_URL = os.getenv(
    "PA_LAYER_URL",
    "https://gisweb.miamidade.gov/arcgis/rest/services/MD_LandInformation/MapServer/26",
)
# Alert only if the land-use description contains one of these words.
# Empty = no land-use filter. Parcels whose land use can't be found are still alerted.
LAND_USE_KEYWORDS = [k.strip().upper() for k in os.getenv("LAND_USE_KEYWORDS", "VACANT").split(",") if k.strip()]

HEADERS = {"User-Agent": "Mozilla/5.0 (personal auction watcher; 1 run/day)"}

# ----------------------------------------------------------------------------
# PARSING
# The site ships compressed HTML: tokens like @A @B @F @G stand in for tags and
# are expanded client-side. We don't expand them; we read label/value pairs.
#   "Parcel ID:@F tabindex="0" @CAD_DTA">28-2202-029-2320@G"
# ----------------------------------------------------------------------------
ITEM_SPLIT = re.compile(r'id="AITEM_(\d+)"')
FIELD_RE = re.compile(r'>\s*([^<>@:]+?):@F[^>]*?@CAD_DTA[^"]*">(.*?)@G', re.S)
CITY_RE = re.compile(r'scope="row">@F[^>]*?@CAD_DTA[^"]*">(.*?)@G', re.S)
TAG_RE = re.compile(r"<[^>]+>")
MONEY_RE = re.compile(r"[-\d,]+\.?\d*")


def clean(s: str) -> str:
    return html.unescape(TAG_RE.sub("", s)).strip()


def money(s: str | None) -> float | None:
    if not s:
        return None
    m = MONEY_RE.search(s.replace("$", ""))
    try:
        return float(m.group().replace(",", "")) if m else None
    except ValueError:
        return None


def parse_response(text: str, sale_date: str = "") -> list[dict]:
    data = json.loads(text, strict=False)  # strict=False tolerates raw newlines
    body = data.get("retHTML", "")
    parts = ITEM_SPLIT.split(body)
    # parts = [prefix, id1, chunk1, id2, chunk2, ...]
    items = []
    for i in range(1, len(parts) - 1, 2):
        aid, chunk = parts[i], parts[i + 1]
        fields = {k.strip(): clean(v) for k, v in FIELD_RE.findall(chunk)}
        city = CITY_RE.search(chunk)
        city_line = clean(city.group(1)) if city else ""
        zip_m = re.search(r"\b(\d{5})\b", city_line)
        items.append({
            "id": aid,
            "sale_date": sale_date,
            "type": fields.get("Auction Type", "").upper(),
            "case": fields.get("Case #", ""),
            "parcel": fields.get("Parcel ID", ""),
            "address": fields.get("Property Address", ""),
            "city": city_line,
            "zip": zip_m.group(1) if zip_m else "",
            # tax deed lists show Opening Bid; foreclosures show Final Judgment Amount
            "bid": money(fields.get("Opening Bid")) or money(fields.get("Final Judgment Amount")),
            "assessed": money(fields.get("Assessed Value")),
            "raw": fields,
        })
    return items


# ----------------------------------------------------------------------------
# FILTERING
# ----------------------------------------------------------------------------
def keep(item: dict) -> bool:
    if AUCTION_TYPES and item["type"].replace(" ", "") not in {t.replace(" ", "") for t in AUCTION_TYPES}:
        return False
    if MAX_BID and item["bid"] is not None and item["bid"] > MAX_BID:
        return False
    if ZIPS and item["zip"] and item["zip"] not in ZIPS:
        return False
    return True


def tags(item: dict) -> list[str]:
    t = []
    if not item["address"]:
        t.append("no street address (often vacant land)")
    if item["parcel"].upper().startswith("MULTIPLE"):
        t.append("multiple parcels")
    if item["assessed"] is not None and item["assessed"] < 5000:
        t.append("very low assessed value (possible sliver)")
    return t


# ----------------------------------------------------------------------------
# FETCHING
# ----------------------------------------------------------------------------
def sale_dates(days: int):
    d = date.today()
    for _ in range(days):
        d += timedelta(days=1)
        if d.weekday() < 5:  # sales run Mon-Fri
            yield d


def load_date(s: requests.Session, base: str, ds: str) -> list[dict]:
    """Open the preview page for one sale date, then pull its items page by page."""
    s.get(base + PREVIEW_PATH.format(date=ds), timeout=30).raise_for_status()
    items, seen_ids = [], set()
    for page in range(MAX_PAGES):
        ms = int(time.time() * 1000)
        url = base + LOAD_PATH.format(page_dir=0 if page == 0 else 1) + f"&tx={ms}&_={ms}"
        r = s.get(url, timeout=30, headers={"X-Requested-With": "XMLHttpRequest"})
        r.raise_for_status()
        if '"retHTML"' not in r.text:
            break
        batch = [i for i in parse_response(r.text, ds) if i["id"] not in seen_ids]
        if not batch:  # empty day, or the "next page" returned what we already have
            break
        seen_ids.update(i["id"] for i in batch)
        items.extend(batch)
        time.sleep(2)
    return items


def fetch_all() -> list[dict]:
    items = []
    for base in BASE_URLS:
        s = requests.Session()
        s.headers.update(HEADERS)
        try:
            s.get(base, timeout=30).raise_for_status()  # session cookies
        except Exception as e:  # one unreachable site shouldn't stop the others
            print(f"[error] {base}: {e}", file=sys.stderr)
            continue
        for d in sale_dates(DAYS_AHEAD):
            ds = d.strftime(DATE_FORMAT)
            try:
                items.extend(load_date(s, base, ds))
            except Exception as e:  # one bad date shouldn't kill the run
                print(f"[warn] {base} {ds}: {e}", file=sys.stderr)
            time.sleep(2)  # be polite
    return items


# ----------------------------------------------------------------------------
# LAND USE (Property Appraiser parcel data)
# ----------------------------------------------------------------------------
def folio_of(item: dict) -> str:
    digits = re.sub(r"\D", "", item["parcel"])
    return digits if len(digits) == 13 else ""


def lookup_land_use(session: requests.Session, folio: str) -> dict | None:
    """Return the parcel's attributes from the county layer, or None if not found."""
    r = session.get(
        f"{PA_LAYER_URL}/query",
        params={"where": f"FOLIO='{folio}'", "outFields": "*", "returnGeometry": "false", "f": "json"},
        timeout=30,
    )
    r.raise_for_status()
    data = r.json()
    if "error" in data:
        raise RuntimeError(data["error"])
    feats = data.get("features") or []
    return feats[0]["attributes"] if feats else None


def lot_size(attrs: dict) -> str:
    """Field names for lot size aren't documented, so look for likely ones."""
    for k, v in attrs.items():
        ku = k.upper()
        if v not in (None, "", 0) and ("LOT" in ku and ("SIZE" in ku or "SQ" in ku) or "ACRE" in ku):
            return f"{v} ({k})"
    return ""


def enrich(items: list[dict]) -> None:
    s = requests.Session()
    s.headers.update(HEADERS)
    for item in items:
        item["land_use"] = None
        folio = folio_of(item)
        if not folio:
            continue
        try:
            a = lookup_land_use(s, folio)
        except Exception as e:
            print(f"[warn] land use {folio}: {e}", file=sys.stderr)
            continue
        if a:
            item["land_use"] = {
                "code": a.get("DOR_CODE_CUR"),
                "desc": (a.get("DOR_DESC") or "").strip(),
                "land_val": a.get("LAND_VAL_CUR"),
                "total_val": a.get("TOTAL_VAL_CUR"),
                "lot": lot_size(a),
            }
        time.sleep(1)


def land_use_ok(item: dict) -> bool:
    lu = item.get("land_use")
    if not LAND_USE_KEYWORDS or not lu or not lu["desc"]:
        return True  # no filter, or unknown land use -> let a human look
    return any(k in lu["desc"].upper() for k in LAND_USE_KEYWORDS)


# ----------------------------------------------------------------------------
# STATE + ALERTS
# ----------------------------------------------------------------------------
def load_seen() -> dict:
    """State per auction item id: {"sale_date", "ok" (passed land-use filter), "land_use", "reminded": [days]}."""
    try:
        data = json.loads(SEEN_FILE.read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        return {}
    if isinstance(data, list):  # old format: plain list of ids -> treat as seen, no reminders sent yet
        return {i: {"sale_date": "", "ok": True, "land_use": None, "reminded": []} for i in data}
    return data


def save_seen(seen: dict) -> None:
    today = date.today()
    # drop items whose sale date has passed so the file doesn't grow forever
    keep_ = {k: v for k, v in seen.items() if (days_until(v.get("sale_date", ""), today) or 0) >= 0}
    SEEN_FILE.write_text(json.dumps(keep_, indent=1, sort_keys=True))


def days_until(sale_date: str, today: date) -> int | None:
    try:
        return (datetime.strptime(sale_date, DATE_FORMAT).date() - today).days
    except ValueError:
        return None


def fmt(item: dict) -> str:
    bid = f"${item['bid']:,.2f}" if item["bid"] is not None else "n/a"
    assessed = f"${item['assessed']:,.0f}" if item["assessed"] is not None else "n/a"
    lines = [
        f"{item['sale_date']}  {item['type']}  #{item['case']}",
        f"Parcel: {item['parcel']}",
        f"Address: {item['address'] or '(none)'} {item['city']}".rstrip(),
        f"Bid: {bid}   Assessed: {assessed}",
    ]
    lu = item.get("land_use")
    if lu:
        lines.append(f"Land use: {lu['code']} {lu['desc']}".rstrip())
        vals = []
        if lu["land_val"] is not None:
            vals.append(f"land ${lu['land_val']:,.0f}")
        if lu["total_val"] is not None:
            vals.append(f"total ${lu['total_val']:,.0f}")
        if lu["lot"]:
            vals.append(f"lot {lu['lot']}")
        if vals:
            lines.append("PA values: " + ", ".join(vals))
    elif folio_of(item):
        lines.append("Land use: not found, check manually")
    if t := tags(item):
        lines.append("Note: " + "; ".join(t))
    if folio := folio_of(item):
        lines.append(f"Property Search (folio {folio}): https://apps.miamidadepa.gov/PropertySearch/")
    return "\n".join(lines)


def send_telegram(text: str) -> None:
    for i in range(0, len(text), 3900):  # Telegram message limit is 4096
        requests.post(
            f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage",
            data={"chat_id": TELEGRAM_CHAT_ID, "text": text[i:i + 3900], "disable_web_page_preview": True},
            timeout=30,
        ).raise_for_status()


def send_email(subject: str, text: str) -> None:
    msg = EmailMessage()
    msg["Subject"], msg["From"], msg["To"] = subject, SMTP_USER, EMAIL_TO
    msg.set_content(text)
    with smtplib.SMTP_SSL("smtp.gmail.com", 465) as smtp:
        smtp.login(SMTP_USER, SMTP_PASS)
        smtp.send_message(msg)


def notify(items: list[dict], subject: str, dry_run: bool) -> None:
    body = "\n\n".join(fmt(i) for i in items)
    if dry_run or not (TELEGRAM_TOKEN or SMTP_USER):
        print(f"--- {subject} ---\n{body}")
        return
    if TELEGRAM_TOKEN and TELEGRAM_CHAT_ID:
        send_telegram(f"{subject}\n\n{body}")
    if SMTP_USER and SMTP_PASS:
        send_email(subject, body)


# ----------------------------------------------------------------------------
def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--sample", help="parse a saved JSON response instead of fetching")
    ap.add_argument("--dry-run", action="store_true", help="print alerts instead of sending")
    ap.add_argument("--folio", help="test the land-use lookup for one folio and exit")
    args = ap.parse_args()

    if args.folio:
        s = requests.Session()
        s.headers.update(HEADERS)
        a = lookup_land_use(s, re.sub(r"\D", "", args.folio))
        print(json.dumps(a, indent=2, default=str) if a else "not found")
        return

    if args.sample:
        items = parse_response(Path(args.sample).read_text(), "sample")
        for i in items:
            print(json.dumps({k: v for k, v in i.items() if k != "raw"}), "KEEP" if keep(i) else "skip")
        return

    items = [i for i in fetch_all() if keep(i)]
    seen = load_seen()
    today = date.today()

    # 1) New listings: look up land use once, alert if they pass the filter
    new = [i for i in items if i["id"] not in seen]
    enrich(new)  # only look up parcels we haven't seen, to keep requests low
    new_alerts = [i for i in new if land_use_ok(i)]
    for i in new:
        d = days_until(i["sale_date"], today)
        seen[i["id"]] = {
            "sale_date": i["sale_date"],
            "ok": land_use_ok(i),
            "land_use": i.get("land_use"),
            # a listing first found inside a reminder window already got the "new" alert
            "reminded": [r for r in REMIND_DAYS if d is not None and d <= r],
        }

    # 2) Reminders: still-listed items (so cancelled sales drop out) whose sale is N days away
    reminders: dict[int, list[dict]] = {r: [] for r in REMIND_DAYS}
    for i in items:
        st = seen.get(i["id"])
        if not st or not st.get("ok") or i["id"] in {n["id"] for n in new}:
            continue
        st["sale_date"] = i["sale_date"]  # the sale may have been rescheduled
        i["land_use"] = st.get("land_use")
        d = days_until(i["sale_date"], today)
        if d is None:
            continue
        # smallest window reached that hasn't been sent (a missed run still gets caught up)
        due = [r for r in REMIND_DAYS if d <= r and r not in st["reminded"]]
        if due:
            reminders[min(due)].append(i)
            st["reminded"] = sorted(set(st["reminded"]) | set(due), reverse=True)

    print(f"{len(items)} matching, {len(new)} new, {len(new_alerts)} new alerts, "
          + ", ".join(f"{len(v)} reminders at {k}d" for k, v in reminders.items()))

    if new_alerts:
        notify(new_alerts, f"🆕 {len(new_alerts)} new auction listing(s)", args.dry_run)
    for r, group in sorted(reminders.items(), reverse=True):
        if group:
            when = "tomorrow" if r == 1 else f"in {r} days"
            notify(group, f"⏰ {len(group)} auction(s) {when}", args.dry_run)

    if not args.dry_run:
        save_seen(seen)

if __name__ == "__main__":
    main()
