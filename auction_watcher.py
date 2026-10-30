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
import csv
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
# RealAuction sites, comma-separated. Miami-Dade's tax deeds are on its realforeclose calendar.
# Miami-Dade tax deeds are listed on its realforeclose site; Broward uses realtaxdeed.
BASE_URLS = [u.strip().rstrip("/") for u in os.getenv(
    "BASE_URL", "https://www.miamidade.realforeclose.com,https://broward.realtaxdeed.com").split(",") if u.strip()]
# The site's "quick search" report: FilterData sets the date range in the session, LoadData returns rows.
# Links to open in your browser: the listing itself ({aid} = auction item id), and its sale-date page.
DETAIL_PATH = os.getenv("DETAIL_PATH", "/index.cfm?zaction=AUCTION&Zmethod=DETAILS&AID={aid}&bypassPage=1")
PREVIEW_PATH = "/index.cfm?zaction=AUCTION&Zmethod=PREVIEW&AUCTIONDATE={date}"
# Public calendar + per-day listing (no login needed)
CALENDAR_PATH = os.getenv("CALENDAR_PATH", "/index.cfm?zaction=USER&zmethod=CALENDAR")
# How to ask the calendar for a given month ({m}, {y}); confirm from the site's "next month" link.
# The site's own "next month" link uses a ColdFusion timestamp: selCalDate={ts '2026-10-01 00:00:00'}
CALENDAR_MONTH_PARAM = os.getenv("CALENDAR_MONTH_PARAM",
                                 "&selCalDate=%7Bts%20%27{y}%2D{m:02d}%2D01%2000%3A00%3A00%27%7D")
# Page 1: PageDir=0&doR=1&bypassPage=1. Next pages: PageDir=1&doR=0&bypassPage=0
# (with bypassPage=1 the site just returns page 1 again).
# AREA: W = waiting (upcoming), R = running, C = closed (sold / redeemed / canceled).
DAY_LOAD_PATH = ("/index.cfm?zaction=AUCTION&Zmethod=UPDATE&FNC=LOAD&AREA={area}&PageDir={page_dir}"
                 "&doR={dor}&bypassPage={bypass}&test=1&tx={ms}&_={ms}")
# Status of the items on the current page (sold amount, sold to, redeemed, canceled...)
STATUS_PATH = "/index.cfm?zaction=AUCTION&ZMETHOD=UPDATE&FNC=UPDATE&ref={ids},&tx={ms}"


def day_page_url(area: str, page: int, ms: int) -> str:
    if page == 0:
        return DAY_LOAD_PATH.format(area=area, page_dir=0, dor=1, bypass=1, ms=ms)
    return DAY_LOAD_PATH.format(area=area, page_dir=1, dor=0, bypass=0, ms=ms)

SKIP_STATUSES = {s.strip().upper() for s in os.getenv("SKIP_STATUSES", "CANCELED,CANCELLED").split(",") if s.strip()}
MAX_PAGES = int(os.getenv("MAX_PAGES", "10"))
DATE_FORMAT = os.getenv("DATE_FORMAT", "%m/%d/%Y")
DAYS_AHEAD = int(os.getenv("DAYS_AHEAD", "45"))

AUCTION_TYPES = {t.strip().upper() for t in os.getenv("AUCTION_TYPES", "TAXDEED").split(",") if t.strip()}
MAX_BID = float(os.getenv("MAX_BID", "0") or 0)          # max opening bid for vacant lots; 0 = no limit
# Second search: any non-condo property (houses, townhouses, duplexes, lots, commercial...)
# with an opening bid at or under this. 0 = turn this search off.
PROPERTY_MAX_BID = float(os.getenv("PROPERTY_MAX_BID", "100000") or 0)
ZIPS = {z.strip() for z in os.getenv("ZIPS", "").split(",") if z.strip()}  # empty = any

SEEN_FILE = Path(os.getenv("SEEN_FILE", "seen.json"))
# Sale results (one row per tax deed listing, every listing, not just alerted ones)
RESULTS_FILE = Path(os.getenv("RESULTS_FILE", "results.csv"))
# Send a short Telegram/email summary of the day's results (sold items) after collecting them
RESULTS_NOTIFY = os.getenv("RESULTS_NOTIFY", "1") not in ("0", "", "false", "no")
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
# Broward (and any non-Miami-Dade county): Florida DOR statewide parcel layer.
STATEWIDE_LAYER_URL = os.getenv(
    "STATEWIDE_LAYER_URL",
    "https://services9.arcgis.com/Gh9awoU677aKree0/arcgis/rest/services/Florida_Statewide_Cadastral/FeatureServer/0",
)
# FDOR county numbers used by the statewide layer.
FDOR_COUNTY_NO = {"miamidade": 23, "broward": 16}
# Standard Florida DOR land-use codes (the statewide layer gives codes, not descriptions).
DOR_CODES = {
    0: "VACANT RESIDENTIAL", 1: "SINGLE FAMILY", 2: "MOBILE HOMES", 3: "MULTI-FAMILY 10+ UNITS",
    4: "CONDOMINIUM", 5: "COOPERATIVES", 8: "MULTI-FAMILY <10 UNITS", 9: "RESIDENTIAL COMMON AREAS",
    10: "VACANT COMMERCIAL", 40: "VACANT INDUSTRIAL", 70: "VACANT INSTITUTIONAL", 80: "VACANT GOVERNMENTAL",
}

# Comparable sales (from the statewide layer): vacant residential lots sold nearby.
COMP_RADIUS_FT = float(os.getenv("COMP_RADIUS_FT", "2640"))   # half a mile
COMP_YEARS = int(os.getenv("COMP_YEARS", "3"))                 # sales in the last N years
COMP_MIN = int(os.getenv("COMP_MIN", "3"))                     # widen to 2x radius if fewer found
COMP_MIN_PRICE = float(os.getenv("COMP_MIN_PRICE", "5000"))    # ignore token/family transfers

# Comma = OR, plus = AND. Default: vacant land zoned/used residential (i.e. land to build a house on).
LAND_USE_KEYWORDS = [
    [w.strip().upper() for w in k.split("+") if w.strip()]
    for k in os.getenv("LAND_USE_KEYWORDS", "VACANT+RESIDENTIAL").split(",") if k.strip()
]
# Never alert on these land uses (matched anywhere in the land-use description).
EXCLUDE_LAND_USE = [k.strip().upper() for k in os.getenv("EXCLUDE_LAND_USE", "CONDOMINIUM,CONDO").split(",") if k.strip()]
# Minimum lot size in square feet (0 = no minimum). Screens out slivers and too-small lots.
MIN_LOT_SQFT = float(os.getenv("MIN_LOT_SQFT", "5000") or 0)
# Florida East State Plane (US survey feet), so geometry areas come back in sq ft.
AREA_SR = os.getenv("AREA_SR", "2236")

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
    limit = max(MAX_BID, PROPERTY_MAX_BID) if MAX_BID else 0  # 0 = lots have no limit, so none here
    if limit and item["bid"] is not None and item["bid"] > limit:
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


def county_of(base: str) -> str:
    """'https://broward.realtaxdeed.com' -> 'broward'"""
    host = re.sub(r"^https?://(www\.)?", "", base)
    return host.split(".")[0].lower()


def calendar_day_wanted(box: str) -> bool:
    """Keep a calendar day if it has sales scheduled of a type we watch (tax deed by default)."""
    text = re.sub(r"<[^>]+>", " ", box).upper()
    sch = re.search(r'CALSCH[^>]*>\s*(\d+)', box, re.I)
    if sch and int(sch.group(1)) == 0:
        return False
    kinds = {"TAXDEED": ("TAX DEED", "TAXDEED", " TD"), "FORECLOSURE": ("FORECLOSURE", " FC")}
    watched = [w for t in AUCTION_TYPES for w in kinds.get(t.replace(" ", ""), (t,))]
    if not watched or not any(k in " " + text for k in watched):
        # unknown label: keep the day rather than miss sales (listings are filtered by type anyway)
        return not any(k in " " + text for ks in kinds.values() for k in ks)
    return True


def auction_days(s: requests.Session, base: str) -> list[str]:
    """Days with auctions, from the public calendar. Falls back to every weekday if it can't be read."""
    start, end = date.today(), date.today() + timedelta(days=DAYS_AHEAD)
    found = set()
    try:
        # the calendar shows a month at a time; look at this month and the next ones in range
        months = {(start.year, start.month)}
        d = start
        while d <= end:
            months.add((d.year, d.month)); d += timedelta(days=28)
        for y, m in sorted(months):
            r = s.get(base + CALENDAR_PATH + CALENDAR_MONTH_PARAM.format(m=m, y=y), timeout=30)
            r.raise_for_status()
            shown = {(int(y2), int(m2)) for m2, _, y2 in re.findall(r'dayid="(\d{2})/(\d{2})/(\d{4})"', r.text)}
            if shown and (y, m) not in shown:
                print(f"[warn] {county_of(base)}: asked the calendar for {m}/{y} but it showed "
                      f"{sorted(shown)}; the month parameter isn't right yet", file=sys.stderr)
            # each day: <div class="CALBOX ..." dayid="09/01/2026"> ... Foreclosure ... CALSCH">4</span> FC ...</div>
            for ds, box in re.findall(r'dayid="(\d{2}/\d{2}/\d{4})"(.*?)</div>', r.text, re.I | re.S):
                try:
                    dd = datetime.strptime(ds, "%m/%d/%Y").date()
                except ValueError:
                    continue
                if not (start <= dd <= end) or not calendar_day_wanted(box):
                    continue
                found.add(dd)
            time.sleep(2)
    except Exception as e:
        print(f"[warn] {county_of(base)}: calendar: {e}", file=sys.stderr)
    if found:
        print(f"[fetch] {county_of(base)}: calendar has {len(found)} auction day(s) in range")
        return [d.strftime(DATE_FORMAT) for d in sorted(found)]
    print(f"[warn] {county_of(base)}: couldn't read auction days from the calendar; checking every weekday",
          file=sys.stderr)
    return [d.strftime(DATE_FORMAT) for d in sale_dates(DAYS_AHEAD)]


def fetch_site(site: str) -> list[dict]:
    base = site.split("|")[0].rstrip("/")
    county = county_of(base)
    s = requests.Session()
    s.headers.update(HEADERS)
    s.get(base, timeout=30).raise_for_status()  # session cookies

    items, ids = [], set()
    for ds in auction_days(s, base):
        try:
            time.sleep(2)
            s.get(base + PREVIEW_PATH.format(date=ds), timeout=30).raise_for_status()  # select the day
            day_new = 0
            for page in range(MAX_PAGES):
                time.sleep(2)
                ms = int(time.time() * 1000)
                r = s.get(base + day_page_url("W", page, ms),
                          timeout=30, headers={"X-Requested-With": "XMLHttpRequest"})
                r.raise_for_status()
                if '"retHTML"' not in r.text:
                    break
                batch = parse_response(r.text, ds)
                fresh = [i for i in batch if f"{county}:{i['id']}" not in ids]
                if not fresh:  # nothing new: empty day, last page, or a repeat of an earlier day
                    break
                for i in fresh:
                    aid = i["id"]
                    i.update({"id": f"{county}:{aid}", "aid": aid, "county": county,
                              "link": base + DETAIL_PATH.format(aid=aid),
                              "day_link": base + PREVIEW_PATH.format(date=ds)})
                    ids.add(i["id"])
                items.extend(fresh)
                day_new += len(fresh)
            print(f"[fetch] {county} {ds}: {day_new} listing(s)")
        except Exception as e:  # one bad day shouldn't kill the run
            print(f"[warn] {county} {ds}: {e}", file=sys.stderr)
    return items


def fetch_all() -> list[dict]:
    items = []
    for site in BASE_URLS:
        try:
            items.extend(fetch_site(site))
        except Exception as e:  # one unreachable site shouldn't stop the others
            print(f"[error] {site}: {e}", file=sys.stderr)
    active = [i for i in items if i.get("status", "").upper() not in SKIP_STATUSES]
    print(f"[fetch] {len(items)} total, {len(items) - len(active)} skipped (canceled)")
    return active


# ----------------------------------------------------------------------------
# LAND USE (Property Appraiser parcel data)
# ----------------------------------------------------------------------------
def folio_of(item: dict) -> str:
    digits = re.sub(r"\D", "", item["parcel"])
    return digits if len(digits) == 13 else ""


def lookup_land_use(session: requests.Session, folio: str) -> dict | None:
    """Return the parcel's attributes (plus _geom_sqft) from the county layer, or None."""
    r = session.get(
        f"{PA_LAYER_URL}/query",
        params={"where": f"FOLIO='{folio}'", "outFields": "*", "returnGeometry": "true",
                "outSR": AREA_SR, "f": "json"},
        timeout=30,
    )
    r.raise_for_status()
    data = r.json()
    if "error" in data:
        raise RuntimeError(data["error"])
    feats = data.get("features") or []
    if not feats:
        return None
    attrs = dict(feats[0].get("attributes") or {})
    attrs["_geom_sqft"] = polygon_area(feats[0].get("geometry") or {})
    attrs["_centroid"] = centroid(feats[0].get("geometry") or {})
    return attrs


def lookup_statewide(session: requests.Session, county: str, parcel: str) -> dict | None:
    """Look up a parcel in the Florida DOR statewide layer and map it to the same keys
    the Miami-Dade layer uses, so the rest of the script doesn't care which county it is."""
    co = FDOR_COUNTY_NO.get(county)
    pid = re.sub(r"[^0-9A-Za-z]", "", parcel).upper()
    if co is None or not pid:
        return None
    feats, last_err = [], None
    for co_expr in (f"CO_NO={co}", f"CO_NO='{co}'"):  # field may be numeric or text
        r = session.get(
            f"{STATEWIDE_LAYER_URL}/query",
            params={"where": f"{co_expr} AND PARCEL_ID='{pid}'", "outFields": "*",
                    "returnGeometry": "true", "outSR": AREA_SR, "f": "json"},
            timeout=30,
        )
        r.raise_for_status()
        data = r.json()
        if "error" in data:
            last_err = data["error"]
            continue
        feats = data.get("features") or []
        break
    else:
        raise RuntimeError(last_err)
    if not feats:
        return None
    a = dict(feats[0].get("attributes") or {})
    try:
        code = int(str(a.get("DOR_UC")).strip())
    except (TypeError, ValueError):
        code = None
    return {
        "DOR_CODE_CUR": a.get("DOR_UC"),
        "DOR_DESC": DOR_CODES.get(code, f"DOR USE CODE {a.get('DOR_UC')}") if code is not None else "",
        "LAND_VAL_CUR": a.get("LND_VAL"),
        "TOTAL_VAL_CUR": a.get("JV"),
        "LND_SQFOOT": a.get("LND_SQFOOT"),  # land sq ft, if the layer carries it
        "_geom_sqft": polygon_area(feats[0].get("geometry") or {}),
        "_centroid": centroid(feats[0].get("geometry") or {}),
        "_pid": a.get("PARCEL_ID"),
    }


def polygon_area(geom: dict) -> float | None:
    """Area of an ArcGIS polygon in the units of its spatial reference (sq ft here).
    Outer rings and holes have opposite winding, so signed areas net out correctly."""
    rings = geom.get("rings") or []
    total = 0.0
    for ring in rings:
        a = 0.0
        for (x1, y1), (x2, y2) in zip(ring, ring[1:] + ring[:1]):
            a += x1 * y2 - x2 * y1
        total += a / 2
    return abs(total) or None


def centroid(geom: dict) -> tuple[float, float] | None:
    """Rough centre of a parcel (average of its outer ring's vertices); fine for a radius search."""
    rings = geom.get("rings") or []
    if not rings or not rings[0]:
        return None
    pts = rings[0][:-1] if rings[0][0] == rings[0][-1] else rings[0]
    return sum(p[0] for p in pts) / len(pts), sum(p[1] for p in pts) / len(pts)


def lot_sqft(attrs: dict) -> tuple[float | None, str]:
    """Lot size in sq ft: a lot-size field if the layer has one, else the parcel polygon's area."""
    for k, v in attrs.items():
        ku = k.upper()
        if not isinstance(v, (int, float)) or v <= 0:
            continue
        if "ACRE" in ku:
            return float(v) * 43560, k
        if ("LOT" in ku and ("SIZE" in ku or "SQ" in ku or "AREA" in ku)) or ku in ("LND_SQFOOT", "LAND_SQFT"):
            return float(v), k
    g = attrs.get("_geom_sqft")
    return (g, "parcel shape") if g else (None, "")


def query_statewide(session: requests.Session, wheres: list[str], extra: dict) -> list[dict]:
    """Try WHERE variants (numeric vs text fields differ between layers) until one is accepted."""
    last_err = None
    for where in wheres:
        r = session.get(f"{STATEWIDE_LAYER_URL}/query",
                        params={"where": where, "outFields": "*", "f": "json", **extra}, timeout=60)
        r.raise_for_status()
        data = r.json()
        if "error" in data:
            last_err = data["error"]
            continue
        return data.get("features") or []
    raise RuntimeError(last_err)


def find_comps(session: requests.Session, county: str, xy: tuple[float, float], exclude_pid: str = "") -> dict | None:
    """Vacant residential lots sold near a point. Returns a summary with median $/sq ft."""
    co = FDOR_COUNTY_NO.get(county)
    if co is None or not xy:
        return None
    since = date.today().year - COMP_YEARS + 1
    wheres = [
        f"{c} AND {u} AND SALE_YR1 >= {since} AND SALE_PRC1 >= {COMP_MIN_PRICE:.0f}"
        for c in (f"CO_NO={co}", f"CO_NO='{co}'")
        for u in ("DOR_UC IN ('000','00','0')", "DOR_UC=0")
    ]
    for radius in (COMP_RADIUS_FT, COMP_RADIUS_FT * 2):
        feats = query_statewide(session, wheres, {
            "geometry": f"{xy[0]},{xy[1]}", "geometryType": "esriGeometryPoint", "inSR": AREA_SR,
            "distance": radius, "units": "esriSRUnit_Foot", "spatialRel": "esriSpatialRelIntersects",
            "returnGeometry": "true", "outSR": AREA_SR,
        })
        sales = []
        for f in feats:
            a = f.get("attributes") or {}
            if exclude_pid and re.sub(r"[^0-9A-Za-z]", "", str(a.get("PARCEL_ID"))).upper() == exclude_pid.upper():
                continue
            price = a.get("SALE_PRC1") or 0
            if price < COMP_MIN_PRICE:
                continue
            sqft = a.get("LND_SQFOOT") or polygon_area(f.get("geometry") or {})
            if price and sqft and sqft > 500:
                sales.append({"price": float(price), "sqft": float(sqft), "ppsf": float(price) / float(sqft),
                              "year": a.get("SALE_YR1"), "month": a.get("SALE_MO1")})
        if len(sales) >= COMP_MIN or radius != COMP_RADIUS_FT:
            break
    if not sales:
        return {"n": 0, "radius_ft": radius}
    ppsf = sorted(x["ppsf"] for x in sales)
    mid = len(ppsf) // 2
    median = ppsf[mid] if len(ppsf) % 2 else (ppsf[mid - 1] + ppsf[mid]) / 2
    return {"n": len(sales), "radius_ft": radius, "median_ppsf": round(median, 2),
            "low_ppsf": round(ppsf[0], 2), "high_ppsf": round(ppsf[-1], 2)}


def enrich(items: list[dict]) -> None:
    s = requests.Session()
    s.headers.update(HEADERS)
    for item in items:
        item["land_use"] = None
        county = item.get("county", "miamidade")
        if county == "miamidade":
            folio = folio_of(item)
            if not folio:
                continue
        else:
            folio = re.sub(r"[^0-9A-Za-z]", "", item["parcel"]).upper()
            if not folio or item["parcel"].upper().startswith("MULTIPLE"):
                continue
        try:
            if county == "miamidade":
                a = lookup_land_use(s, folio)
            else:
                a = lookup_statewide(s, county, item["parcel"])
        except Exception as e:
            print(f"[warn] land use {county} {folio}: {e}", file=sys.stderr)
            continue
        if not a:
            print(f"[land use] {county} {folio}: not found")
        if a:
            sqft, src = lot_sqft(a)
            item["land_use"] = {
                "code": a.get("DOR_CODE_CUR"),
                "desc": (a.get("DOR_DESC") or "").strip(),
                "land_val": a.get("LAND_VAL_CUR"),
                "total_val": a.get("TOTAL_VAL_CUR"),
                "lot_sqft": round(sqft) if sqft else None,
                "lot_src": src,
            }
            # comparable sales only for lots that pass the filter (keeps requests low)
            if land_use_ok(item) and bid_under(item, MAX_BID):
                try:
                    item["land_use"]["comps"] = find_comps(s, county, a.get("_centroid"), a.get("_pid") or folio)
                except Exception as e:
                    print(f"[warn] comps {county} {folio}: {e}", file=sys.stderr)
            # shows in the Actions log so you can see the county's real descriptions
            print(f"[land use] {county} {folio}: {item['land_use']['code']} {item['land_use']['desc']!r}, "
                  f"lot {item['land_use']['lot_sqft']} sq ft ({src or 'unknown'})")
        time.sleep(1)


def is_excluded(item: dict) -> bool:
    desc = ((item.get("land_use") or {}).get("desc") or "").upper()
    return any(x in desc for x in EXCLUDE_LAND_USE)


def bid_under(item: dict, limit: float) -> bool:
    return not limit or item.get("bid") is None or item["bid"] <= limit


def category(item: dict) -> str | None:
    """'lot' = vacant residential lot to build on (the original search),
    'property' = any non-condo property under PROPERTY_MAX_BID, None = no alert."""
    if land_use_ok(item) and bid_under(item, MAX_BID):
        return "lot"
    if PROPERTY_MAX_BID and not is_excluded(item) and bid_under(item, PROPERTY_MAX_BID):
        return "property"
    return None


CAT_LABEL = {"lot": "🌱 Vacant lot", "property": f"🏠 Property under ${PROPERTY_MAX_BID:,.0f}"}


def land_use_ok(item: dict) -> bool:
    """Buildable-residential screen. Unknown values pass, so a human can take a look."""
    lu = item.get("land_use")
    if not lu:
        return True
    desc = (lu.get("desc") or "").upper()
    if any(x in desc for x in EXCLUDE_LAND_USE):
        return False
    if LAND_USE_KEYWORDS and desc and not any(all(w in desc for w in group) for group in LAND_USE_KEYWORDS):
        return False
    sqft = lu.get("lot_sqft")
    if MIN_LOT_SQFT and sqft and sqft < MIN_LOT_SQFT:
        return False
    return True


# ----------------------------------------------------------------------------
# SALE RESULTS
# Past auction days disappear from the site's calendar, so results are collected
# the same day, after the sale closes (the evening run: --results).
# ----------------------------------------------------------------------------
RESULT_FIELDS = [
    "sale_date", "county", "aid", "case", "certificate", "parcel", "address", "city", "zip",
    "land_use_code", "land_use", "lot_sqft", "pa_land_val", "pa_total_val", "assessed",
    "opening_bid", "status", "sold_to", "sold_amount", "sold_time", "x_opening",
    "comps_n", "comps_median_ppsf", "est_land_value", "x_est_value", "listing", "collected_at",
]


def parse_status(a: dict) -> dict | None:
    """One item from the site's status JSON -> {status, sold_to, sold_amount, sold_time}.
    None if the sale isn't final yet (not started / running)."""
    A, B = (a.get("A") or "").strip(), (a.get("B") or "").strip()
    if A == "Auction Sold":
        return {"status": "Sold", "sold_to": (a.get("ST") or "").strip(),
                "sold_amount": money(a.get("D")), "sold_time": B}
    if A == "B":  # template "Auction Status": B holds the status text (Redeemed, Canceled...)
        return {"status": B, "sold_to": "", "sold_amount": None, "sold_time": ""} if B else None
    if A in ("A", "Time Remaining", ""):  # "Auction Starts" / running
        return None
    return {"status": A, "sold_to": (a.get("ST") or "").strip(), "sold_amount": money(a.get("D")),
            "sold_time": B}


def auction_today(s: requests.Session, base: str, day: date) -> bool:
    """True if the calendar shows a sale of a watched type on this day."""
    r = s.get(base + CALENDAR_PATH + CALENDAR_MONTH_PARAM.format(m=day.month, y=day.year), timeout=30)
    r.raise_for_status()
    ds = day.strftime("%m/%d/%Y")
    for d, box in re.findall(r'dayid="(\d{2}/\d{2}/\d{4})"(.*?)</div>', r.text, re.I | re.S):
        if d == ds:
            return calendar_day_wanted(box)
    return False


def fetch_results_site(site: str, day: date) -> list[dict]:
    base = site.split("|")[0].rstrip("/")
    county = county_of(base)
    s = requests.Session()
    s.headers.update(HEADERS)
    s.get(base, timeout=30).raise_for_status()
    if not auction_today(s, base, day):
        print(f"[results] {county}: no sale on {day:%m/%d/%Y}")
        return []
    ds = day.strftime(DATE_FORMAT)
    time.sleep(2)
    s.get(base + PREVIEW_PATH.format(date=ds), timeout=30).raise_for_status()  # select the day
    out, ids, pending = [], set(), 0
    for page in range(MAX_PAGES * 3):
        time.sleep(2)
        ms = int(time.time() * 1000)
        r = s.get(base + day_page_url("C", page, ms), timeout=30,
                  headers={"X-Requested-With": "XMLHttpRequest"})
        r.raise_for_status()
        if '"retHTML"' not in r.text:
            break
        batch = [i for i in parse_response(r.text, ds) if f"{county}:{i['id']}" not in ids]
        if not batch:
            break
        time.sleep(1)
        st = s.get(base + STATUS_PATH.format(ids=",".join(i["id"] for i in batch), ms=int(time.time() * 1000)),
                   timeout=30, headers={"X-Requested-With": "XMLHttpRequest"})
        st.raise_for_status()
        status = {a.get("AID"): a for a in (json.loads(st.text.strip(), strict=False).get("ADATA") or {}).get("AITEM", [])}
        for i in batch:
            aid = i["id"]
            ids.add(f"{county}:{aid}")
            res = parse_status(status.get(aid) or {})
            if not res:
                pending += 1
                continue
            i.update({"id": f"{county}:{aid}", "aid": aid, "county": county,
                      "link": base + DETAIL_PATH.format(aid=aid), **res})
            out.append(i)
    print(f"[results] {county} {ds}: {len(out)} final, {pending} not final yet")
    return out


def load_results() -> dict:
    try:
        with RESULTS_FILE.open(newline="") as f:
            return {f"{r['county']}:{r['aid']}": r for r in csv.DictReader(f)}
    except FileNotFoundError:
        return {}


def result_row(i: dict) -> dict:
    lu = i.get("land_use") or {}
    c = lu.get("comps") or {}
    est = c.get("median_ppsf") * lu["lot_sqft"] if c.get("n") and lu.get("lot_sqft") else None
    amt, bid = i.get("sold_amount"), i.get("bid")
    r2 = lambda x: "" if x is None else round(x, 2)
    return {
        "sale_date": i["sale_date"], "county": i["county"], "aid": i["aid"], "case": i["case"],
        "certificate": i["raw"].get("Certificate #", ""), "parcel": i["parcel"], "address": i["address"],
        "city": i["city"], "zip": i["zip"],
        "land_use_code": lu.get("code", ""), "land_use": lu.get("desc", ""), "lot_sqft": lu.get("lot_sqft") or "",
        "pa_land_val": r2(lu.get("land_val")), "pa_total_val": r2(lu.get("total_val")), "assessed": r2(i.get("assessed")),
        "opening_bid": r2(bid), "status": i["status"], "sold_to": i["sold_to"], "sold_amount": r2(amt),
        "sold_time": i["sold_time"],
        "x_opening": r2(amt / bid) if amt and bid else "",
        "comps_n": c.get("n", ""), "comps_median_ppsf": c.get("median_ppsf", ""),
        "est_land_value": r2(est), "x_est_value": r2(amt / est) if amt and est else "",
        "listing": i["link"], "collected_at": datetime.now().isoformat(timespec="minutes"),
    }


def collect_results(day: date, dry_run: bool) -> None:
    rows = load_results()
    found = []
    for site in BASE_URLS:
        try:
            found.extend(fetch_results_site(site, day))
        except Exception as e:
            print(f"[error] results {site}: {e}", file=sys.stderr)
    types = {t.replace(" ", "") for t in AUCTION_TYPES}
    new = [i for i in found if i["id"] not in rows and (not types or i["type"].replace(" ", "") in types)]
    # land use: reuse what the morning run already looked up, look up the rest
    seen = load_seen()
    todo = []
    for i in new:
        lu = (seen.get(i["id"]) or {}).get("land_use")
        if lu:
            i["land_use"] = lu
        else:
            todo.append(i)
    enrich(todo)
    for i in new:
        rows[i["id"]] = result_row(i)
    print(f"[results] {len(new)} new result(s), {len(rows)} total in {RESULTS_FILE}")
    if not dry_run:
        ordered = sorted(rows.values(), key=lambda r: (datetime.strptime(r["sale_date"], DATE_FORMAT), r["county"], r["case"]))
        with RESULTS_FILE.open("w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=RESULT_FIELDS, extrasaction="ignore")
            w.writeheader()
            w.writerows(ordered)
    sold = [i for i in new if i["status"] == "Sold"]
    if new and RESULTS_NOTIFY:
        lines = []
        for county in sorted({i["county"] for i in new}):
            c_new = [i for i in new if i["county"] == county]
            c_sold = [i for i in sold if i["county"] == county]
            counts = {}
            for i in c_new:
                counts[i["status"]] = counts.get(i["status"], 0) + 1
            lines.append(f"{county.upper()}: " + ", ".join(f"{n} {k.lower()}" for k, n in sorted(counts.items(), key=lambda x: -x[1])))
            for i in sorted(c_sold, key=lambda x: -(x.get("sold_amount") or 0)):
                lu = (i.get("land_use") or {}).get("desc", "")
                x = f" ({i['sold_amount'] / i['bid']:.1f}x opening)" if i.get("sold_amount") and i.get("bid") else ""
                amt = f"${i['sold_amount']:,.0f}" if i.get("sold_amount") is not None else "n/a"
                lines.append(f"  #{i['case']} {i['address'] or 'no address'} {i['city']} · {lu.title()} · "
                             f"opened ${i['bid'] or 0:,.0f} → sold {amt}{x} to {i['sold_to']}")
        text = f"📊 Auction results {day:%m/%d}\n" + "\n".join(lines)
        if dry_run or not (TELEGRAM_TOKEN or SMTP_USER):
            print(text)
        else:
            if TELEGRAM_TOKEN and TELEGRAM_CHAT_ID:
                send_telegram(text)
            if SMTP_USER and SMTP_PASS:
                send_email(f"📊 Auction results {day:%m/%d}", text)


# ----------------------------------------------------------------------------
# WEEKLY REPORT (Saturdays): what sold this week, what it means for bidding,
# and which of your matches come up next week.
# ----------------------------------------------------------------------------
def _f(x) -> float | None:
    try:
        return float(x) if x not in (None, "") else None
    except ValueError:
        return None


def _median(v: list[float]) -> float | None:
    v = sorted(v)
    if not v:
        return None
    m = len(v) // 2
    return v[m] if len(v) % 2 else (v[m - 1] + v[m]) / 2


def _pct(v: list[float], q: float) -> float | None:
    v = sorted(v)
    if not v:
        return None
    k = (len(v) - 1) * q
    lo, hi = int(k), min(int(k) + 1, len(v) - 1)
    return v[lo] + (v[hi] - v[lo]) * (k - lo)


def _group(desc: str) -> str:
    d = (desc or "").upper()
    if "VACANT" in d and "RESIDENTIAL" in d:
        return "Vacant residential"
    if "VACANT" in d:
        return "Other vacant"
    if "CONDO" in d:
        return "Condo"
    if "SINGLE FAMILY" in d:
        return "Single family"
    if "MOBILE" in d:
        return "Mobile home"
    if "MULTI" in d:
        return "Multi-family"
    return "Other" if d else "Unknown"


def _city(r: dict) -> str:
    return (r.get("city") or "").split(",")[0].strip().title() or "?"


COUNTY_NAME = {"miamidade": "Miami-Dade", "broward": "Broward"}


def weekly_report(today: date) -> str:
    rows = list(load_results().values())
    for r in rows:
        r["_d"] = datetime.strptime(r["sale_date"], DATE_FORMAT).date()
        r["_amt"], r["_bid"] = _f(r.get("sold_amount")), _f(r.get("opening_bid"))
        r["_x"], r["_xe"] = _f(r.get("x_opening")), _f(r.get("x_est_value"))
        r["_g"] = _group(r.get("land_use"))
        r["_3p"] = "3RD PARTY" in (r.get("sold_to") or "").upper()
    start = today - timedelta(days=7)
    week = [r for r in rows if start <= r["_d"] < today]
    L = [f"📈 Weekly auction report · {start:%b %d} – {today - timedelta(days=1):%b %d}"]

    if not rows:
        L += ["", "No results saved yet. Check that the auction-results Action is running "
                  "(Actions tab) and that results.csv is being committed."]
        return "\n".join(L)

    # --- this week
    L.append("")
    if not week:
        L.append("No sales this week.")
    for county in sorted({r["county"] for r in week}):
        c = [r for r in week if r["county"] == county]
        sold = [r for r in c if r["status"] == "Sold"]
        third = [r for r in sold if r["_3p"]]
        red = sum(1 for r in c if r["status"].upper().startswith("REDEEM"))
        days = len({r["_d"] for r in c})
        line = (f"{COUNTY_NAME.get(county, county.title()).upper()}: {len(c)} listings over {days} sale day(s), {len(sold)} sold "
                f"({len(third)} to outside bidders), {red} redeemed ({red / len(c):.0%})")
        L.append(line)
        xs = [r["_x"] for r in third if r["_x"]]
        if xs:
            L.append(f"  Outside bidders paid a median {_median(xs):.1f}x the opening bid "
                     f"(range {min(xs):.1f}x–{max(xs):.1f}x)")

    # --- notable sales this week
    third_wk = sorted([r for r in week if r["status"] == "Sold" and r["_3p"] and r["_amt"]],
                      key=lambda r: -r["_amt"])
    lots_wk = [r for r in week if r["status"] == "Sold" and r["_g"] == "Vacant residential"]
    if third_wk:
        L += ["", "Top sales:"]
        for r in third_wk[:5]:
            lot = f", {int(_f(r['lot_sqft'])):,} sq ft" if _f(r.get("lot_sqft")) else ""
            L.append(f"  ${r['_amt']:,.0f} · {r['address'] or 'no address'}, {_city(r)} · {r['_g']}{lot}"
                     + (f" · {r['_x']:.1f}x opening" if r["_x"] else ""))
    if lots_wk:
        L += ["", "Vacant residential lots sold:"]
        for r in sorted(lots_wk, key=lambda r: -(r["_amt"] or 0))[:8]:
            sq = _f(r.get("lot_sqft"))
            ppsf = f", ${r['_amt'] / sq:,.2f}/sq ft" if r["_amt"] and sq else ""
            vs = f", {r['_xe']:.0%} of comps value" if r["_xe"] else ""
            who = "outside bidder" if r["_3p"] else "cert holder (no competition)"
            L.append(f"  {r['address'] or 'no address'}, {_city(r)}: opened ${r['_bid'] or 0:,.0f} → "
                     f"${r['_amt'] or 0:,.0f}{ppsf}{vs} · {who}")
    cheap_wk = [r for r in week if r["status"] == "Sold" and r["_g"] not in ("Condo", "Vacant residential")
                and r["_amt"] and r["_amt"] <= PROPERTY_MAX_BID]
    if cheap_wk:
        L += ["", f"Non-condo properties sold under ${PROPERTY_MAX_BID:,.0f}:"]
        for r in sorted(cheap_wk, key=lambda r: r["_amt"])[:8]:
            val = _f(r.get("pa_total_val"))
            v = f" (PA value ${val:,.0f}, {r['_amt'] / val:.0%})" if val else ""
            L.append(f"  ${r['_amt']:,.0f} · {r['address'] or 'no address'}, {_city(r)} · {r['_g']}{v}")

    # --- all data so far: bidding guide
    first = min(r["_d"] for r in rows)
    third_all = [r for r in rows if r["status"] == "Sold" and r["_3p"] and r["_x"]]
    L += ["", f"Bidding guide (all {len(rows)} results since {first:%b %d}):"]
    if len(third_all) < 5:
        L.append(f"  Only {len(third_all)} outside-bidder sale(s) so far; numbers get useful after ~20.")
    for g in ("Vacant residential", "Single family", "Multi-family", "Other vacant", "Other"):
        xs = [r["_x"] for r in third_all if r["_g"] == g]
        if len(xs) >= 3:
            L.append(f"  {g}: median {_median(xs):.1f}x opening, 75% sold at or below {_pct(xs, .75):.1f}x (n={len(xs)})")
    lot_ppsf = [r["_amt"] / _f(r["lot_sqft"]) for r in rows
                if r["status"] == "Sold" and r["_3p"] and r["_g"] == "Vacant residential"
                and r["_amt"] and _f(r.get("lot_sqft"))]
    if len(lot_ppsf) >= 3:
        L.append(f"  Vacant lots: median ${_median(lot_ppsf):,.2f}/sq ft paid at auction (n={len(lot_ppsf)})")
    xe = [r["_xe"] for r in third_all if r["_xe"] and r["_g"] == "Vacant residential"]
    if len(xe) >= 3:
        L.append(f"  Vacant lots sell for a median {_median(xe):.0%} of the comps value")
    by_city: dict[str, list[float]] = {}
    for r in third_all:
        by_city.setdefault(_city(r), []).append(r["_x"])
    hot = sorted(((c, _median(v), len(v)) for c, v in by_city.items() if len(v) >= 3), key=lambda t: -t[1])
    if hot:
        L.append("  Most competitive cities: " + ", ".join(f"{c} {m:.1f}x (n={n})" for c, m, n in hot[:4]))
    for county in sorted({r["county"] for r in rows}):
        c = [r for r in rows if r["county"] == county]
        red = sum(1 for r in c if r["status"].upper().startswith("REDEEM"))
        no_comp = sum(1 for r in c if r["status"] == "Sold" and not r["_3p"])
        L.append(f"  {COUNTY_NAME.get(county, county.title())}: {red / len(c):.0%} of listings are redeemed before the sale, "
                 f"{no_comp / len(c):.0%} go to the cert holder with no bids")

    # --- next week: your matches
    seen = load_seen()
    nxt = []
    for k, v in seen.items():
        if k.startswith("_") or not v.get("ok"):
            continue
        d = days_until(v.get("sale_date", ""), today)
        if d is not None and 0 <= d <= 7:
            nxt.append((d, k, v))
    L += ["", f"Your matches coming up in the next 7 days: {len(nxt)}"]
    for d, k, v in sorted(nxt, key=lambda t: t[0])[:10]:
        cat = "🌱" if v.get("cat") == "lot" else "🏠"
        desc = ((v.get("land_use") or {}).get("desc") or "").title()
        bid = f"opening ${v['bid']:,.0f}" if v.get("bid") else ""
        where = ", ".join(x for x in (v.get("address"), (v.get("city") or "").split(",")[0].title()) if x)
        L.append(f"  {cat} {v['sale_date'][:5]} {COUNTY_NAME.get(k.split(':')[0], k.split(':')[0]).upper()} · {where or v.get('parcel') or '#' + k.split(':')[-1]}"
                 + (f" · {desc}" if desc else "") + (f" · {bid}" if bid else ""))
        # what similar things sold for
        g = _group((v.get("land_use") or {}).get("desc"))
        xs = [r["_x"] for r in third_all if r["_g"] == g]
        if v.get("bid") and len(xs) >= 3:
            L.append(f"     similar {g.lower()} sales suggest ≈ ${v['bid'] * _median(xs):,.0f} "
                     f"(up to ${v['bid'] * _pct(xs, .75):,.0f})")
    return "\n".join(L)


def send_weekly(today: date, dry_run: bool) -> None:
    text = weekly_report(today)
    if dry_run or not (TELEGRAM_TOKEN or SMTP_USER):
        print(text)
        return
    if TELEGRAM_TOKEN and TELEGRAM_CHAT_ID:
        send_telegram(text)
    if SMTP_USER and SMTP_PASS:
        send_email(f"📈 Weekly auction report {today:%m/%d}", text)


# ----------------------------------------------------------------------------
# STATE + ALERTS
# ----------------------------------------------------------------------------
def load_seen() -> dict:
    """State per auction item id: {"sale_date", "ok" (passed land-use filter), "land_use", "reminded": [days]}."""
    try:
        data = json.loads(SEEN_FILE.read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        return {}
    if isinstance(data, dict):
        data.pop("_tg", None)  # leftover from the checklist version
    if isinstance(data, list):  # old format: plain list of ids -> treat as seen, no reminders sent yet
        return {i: {"sale_date": "", "ok": True, "land_use": None, "reminded": []} for i in data}
    return data


def save_seen(seen: dict) -> None:
    today = date.today()
    # drop items whose sale date has passed so the file doesn't grow forever
    keep_ = {k: v for k, v in seen.items()
             if k.startswith("_") or (days_until(v.get("sale_date", ""), today) or 0) >= 0}
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
        *([CAT_LABEL[item["cat"]]] if item.get("cat") in CAT_LABEL else []),
        f"{item['sale_date']}  {item.get('county', '').upper()}  {item['type']}  #{item['case']}"
        + (f"  [{item['status']}]" if item.get("status") else ""),
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
        if lu.get("lot_sqft"):
            acres = lu["lot_sqft"] / 43560
            vals.append(f"lot {lu['lot_sqft']:,} sq ft ({acres:.2f} ac)")
        if vals:
            lines.append("PA values: " + ", ".join(vals))
    elif folio_of(item):
        lines.append("Land use: not found, check manually")
    comps = (lu or {}).get("comps")
    if comps is not None:
        miles = comps["radius_ft"] / 5280
        if comps["n"]:
            line = (f"Comps: {comps['n']} vacant residential sales within {miles:.1f} mi "
                    f"(last {COMP_YEARS}y): median ${comps['median_ppsf']:,.2f}/sq ft "
                    f"(${comps['low_ppsf']:,.2f}-${comps['high_ppsf']:,.2f})")
            lines.append(line)
            if lu.get("lot_sqft"):
                est = comps["median_ppsf"] * lu["lot_sqft"]
                pct = f", bid = {item['bid'] / est:.0%} of that" if item.get("bid") and est else ""
                lines.append(f"Est. land value ≈ ${est:,.0f}{pct}")
        else:
            lines.append(f"Comps: no vacant residential sales within {miles:.1f} mi in the last {COMP_YEARS}y")
    if t := tags(item):
        lines.append("Note: " + "; ".join(t))
    for name, url in links_of(item):
        lines.append(f"{name}: {url}")
    return "\n".join(lines)


def links_of(item: dict) -> list[tuple[str, str]]:
    out = []
    if item.get("link"):
        out.append(("Listing", item["link"]))
    if item.get("day_link"):
        out.append(("Sale day", item["day_link"]))
    if item.get("county", "miamidade") == "miamidade":
        if folio := folio_of(item):
            out.append(("Property", f"https://apps.miamidadepa.gov/propertysearch/#/?folio={folio}"))
    elif item.get("county") == "broward" and item["parcel"] and not item["parcel"].upper().startswith("MULTIPLE"):
        folio = re.sub(r"\D", "", item["parcel"])  # 514119-06-0741 -> 514119060741
        if folio:
            out.append(("Property", f"https://bcpa.net/RecInfo.asp?URL_Folio={folio}"))
            out.append(("Map", f"https://gisweb-adapters.bcpa.net/bcpawebmap_ex/bcpawebmap.aspx?FOLIO={folio}"))
    return out


def fmt_html(item: dict) -> str:
    """Compact Telegram version of one listing (HTML)."""
    e = html.escape
    lu = item.get("land_use") or {}
    head = f"<b>{e(item['sale_date'][:5])} · {e(item.get('county', '').upper())} · #{e(item['case'])}</b>"
    if item.get("cat") == "property":
        head = "🏠 " + head
    elif item.get("cat") == "lot":
        head = "🌱 " + head
    addr = f"{item['address'] or 'no address'}, {item['city']}".strip(", ")
    bid = f"${item['bid']:,.0f}" if item.get("bid") is not None else "n/a"
    lines = [head, e(addr), f"Opening bid <b>{bid}</b> · parcel <code>{e(item['parcel'])}</code>"]
    bits = []
    if lu.get("desc"):
        bits.append(e(lu["desc"].title()))
    if lu.get("lot_sqft"):
        bits.append(f"{lu['lot_sqft']:,} sq ft")
    if bits:
        lines.append(" · ".join(bits))
    c = lu.get("comps")
    if c and c.get("n") and lu.get("lot_sqft"):
        est = c["median_ppsf"] * lu["lot_sqft"]
        pct = f" (bid {item['bid'] / est:.0%})" if item.get("bid") and est else ""
        lines.append(f"Comps: {c['n']} sales, ${c['median_ppsf']:,.2f}/sq ft → ≈${est:,.0f}{pct}")
    elif c is not None and not c.get("n"):
        lines.append("Comps: none nearby")
    if t := tags(item):
        lines.append("<i>" + e("; ".join(t)) + "</i>")
    ls = links_of(item)
    if ls:
        lines.append(" | ".join(f'<a href="{e(u, quote=True)}">{e(n)}</a>' for n, u in ls))
    return "\n".join(lines)


def tg(method: str, **payload) -> dict:
    r = requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/{method}", json=payload, timeout=30)
    data = r.json()
    if not data.get("ok"):
        raise RuntimeError(f"Telegram {method}: {data.get('description')}")
    return data.get("result")


def send_telegram_html(items: list[dict], subject: str) -> None:
    """Send listings as compact HTML messages (split to stay under Telegram's 4096-char limit)."""
    blocks = [fmt_html(i) for i in items]
    chunks, cur = [], []
    for b in blocks:
        if cur and (sum(len(x) for x in cur) + len(b) > 3500 or len(cur) >= 10):
            chunks.append(cur); cur = []
        cur.append(b)
    if cur:
        chunks.append(cur)
    for k, ch in enumerate(chunks, 1):
        subj = subject + (f" ({k}/{len(chunks)})" if len(chunks) > 1 else "")
        text = f"<b>{html.escape(subj)}</b>\n\n" + "\n\n".join(ch)
        tg("sendMessage", chat_id=TELEGRAM_CHAT_ID, text=text, parse_mode="HTML", disable_web_page_preview=True)


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


def notify(items: list[dict], subject: str, dry_run: bool, seen: dict | None = None) -> None:
    body = "\n\n".join(fmt(i) for i in items)
    if dry_run or not (TELEGRAM_TOKEN or SMTP_USER):
        print(f"--- {subject} ---\n{body}")
        return
    if TELEGRAM_TOKEN and TELEGRAM_CHAT_ID:
        send_telegram_html(items, subject)
    if SMTP_USER and SMTP_PASS:
        send_email(subject, body)


# ----------------------------------------------------------------------------
def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--sample", help="parse a saved JSON response instead of fetching")
    ap.add_argument("--dry-run", action="store_true", help="print alerts instead of sending")
    ap.add_argument("--folio", help="test the land-use lookup for one folio and exit")
    ap.add_argument("--weekly", action="store_true", help="send the weekly results report")
    ap.add_argument("--results", action="store_true",
                    help="collect today's sale results into results.csv (run after the sales close)")
    ap.add_argument("--date", help="with --results: sale date MM/DD/YYYY (default today); only "
                                   "works while the site still shows that day")
    args = ap.parse_args()

    if args.weekly:
        send_weekly(date.today(), args.dry_run)
        return

    if args.results:
        day = datetime.strptime(args.date, "%m/%d/%Y").date() if args.date else date.today()
        collect_results(day, args.dry_run)
        return

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

    # 1) New listings: look up land use once, alert if they fit a category.
    # Entries saved before categories existed ("cat" missing) that didn't match then
    # are checked again, since the under-$100K property search may match them now.
    new = [i for i in items if i["id"] not in seen
           or ("cat" not in seen[i["id"]] and not seen[i["id"]].get("ok"))]
    enrich(new)  # only look up parcels we haven't seen, to keep requests low
    for i in new:
        i["cat"] = category(i)
    new_alerts = [i for i in new if i["cat"]]
    for i in new:
        d = days_until(i["sale_date"], today)
        seen[i["id"]] = {
            "sale_date": i["sale_date"],
            "ok": bool(i["cat"]),
            "cat": i["cat"],
            "land_use": i.get("land_use"),
            # a listing first found inside a reminder window already got the "new" alert
            "reminded": [r for r in REMIND_DAYS if d is not None and d <= r],
            "bid": i.get("bid"), "address": i.get("address"), "city": i.get("city"),
            "parcel": i.get("parcel"), "link": i.get("link"),
        }

    # 2) Reminders: still-listed items (so cancelled sales drop out) whose sale is N days away
    reminders: dict[int, list[dict]] = {r: [] for r in REMIND_DAYS}
    for i in items:
        st = seen.get(i["id"])
        if not st or not st.get("ok") or i["id"] in {n["id"] for n in new}:
            continue
        st["sale_date"] = i["sale_date"]  # the sale may have been rescheduled
        i["land_use"] = st.get("land_use")
        if "cat" not in st:  # saved before categories existed: it matched the lot search
            st["cat"] = "lot"
        i["cat"] = st["cat"]
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

    def by_cat(group: list[dict]):
        for cat in ("lot", "property"):
            g = [i for i in group if i.get("cat") == cat]
            if g:
                yield cat, g

    for cat, g in by_cat(new_alerts):
        what = "vacant lot(s)" if cat == "lot" else f"non-condo propert{'y' if len(g) == 1 else 'ies'} under ${PROPERTY_MAX_BID:,.0f}"
        notify(g, f"🆕 {len(g)} new {what}", args.dry_run, seen)
    for r, group in sorted(reminders.items(), reverse=True):
        when = "tomorrow" if r == 1 else f"in {r} days"
        for cat, g in by_cat(group):
            what = "vacant lot" if cat == "lot" else "property"
            notify(g, f"⏰ {len(g)} {what} auction(s) {when}", args.dry_run, seen)

    if not args.dry_run:
        save_seen(seen)

if __name__ == "__main__":
    main()
