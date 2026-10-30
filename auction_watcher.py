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
RESULTS_NOTIFY = os.getenv("RESULTS_NOTIFY", "0") not in ("0", "", "false", "no")  # 0 = Saturday report only
# Each results run re-checks sale days this far back, so a missed run is caught up.
RESULTS_DAYS_BACK = int(os.getenv("RESULTS_DAYS_BACK", "7"))
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
            shown = {(int(y2), int(m2)) for m2, _, y2 in re.findall(r'dayid=["\'](\d{2})/(\d{2})/(\d{4})["\']', r.text)}
            if shown and (y, m) not in shown:
                print(f"[warn] {county_of(base)}: asked the calendar for {m}/{y} but it showed "
                      f"{sorted(shown)}; the month parameter isn't right yet", file=sys.stderr)
            # each day: <div class="CALBOX ..." dayid="09/01/2026"> ... Foreclosure ... CALSCH">4</span> FC ...</div>
            for ds, box in re.findall(r'dayid=["\'](\d{2}/\d{2}/\d{4})["\'](.*?)</div>', r.text, re.I | re.S):
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
    # Don't guess: opening a day with no sale makes the site show another day's list,
    # which would put the wrong sale date on listings.
    print(f"[warn] {county_of(base)}: no tax deed sale days found on the calendar in the next "
          f"{DAYS_AHEAD} days", file=sys.stderr)
    return []


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
    "comps_n", "comps_median_ppsf", "est_land_value", "x_est_value", "listing", "property_link", "collected_at",
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


def sale_days_between(s: requests.Session, base: str, start: date, end: date) -> list[date]:
    """Days between start and end (inclusive) that the calendar shows a watched sale on."""
    months, d = set(), start.replace(day=1)
    while d <= end:
        months.add((d.year, d.month))
        d = (d + timedelta(days=32)).replace(day=1)
    days = set()
    for y, m in sorted(months):
        r = s.get(base + CALENDAR_PATH + CALENDAR_MONTH_PARAM.format(m=m, y=y), timeout=30)
        r.raise_for_status()
        for ds, box in re.findall(r'dayid=["\'](\d{2}/\d{2}/\d{4})["\'](.*?)</div>', r.text, re.I | re.S):
            dd = datetime.strptime(ds, "%m/%d/%Y").date()
            if start <= dd <= end and calendar_day_wanted(box):
                days.add(dd)
        time.sleep(2)
    return sorted(days)


def fetch_results_site(site: str, start: date, end: date) -> list[dict]:
    base = site.split("|")[0].rstrip("/")
    county = county_of(base)
    s = requests.Session()
    s.headers.update(HEADERS)
    s.get(base, timeout=30).raise_for_status()
    days = sale_days_between(s, base, start, end)
    print(f"[results] {county}: sale days {start:%m/%d}–{end:%m/%d}: "
          + (", ".join(f"{d:%m/%d}" for d in days) or "none"))
    out = []
    for day in days:
        try:
            out.extend(fetch_results_day(s, base, county, day))
        except Exception as e:
            print(f"[warn] results {county} {day:%m/%d/%Y}: {e}", file=sys.stderr)
    return out


def fetch_results_day(s: requests.Session, base: str, county: str, day: date) -> list[dict]:
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
        "listing": i["link"],
        "property_link": next((u for n, u in property_links(i["county"], i["parcel"]) if n == "Property"), ""),
        "collected_at": datetime.now().isoformat(timespec="minutes"),
    }


def collect_results(start: date, end: date, dry_run: bool) -> None:
    rows = load_results()
    found = []
    for site in BASE_URLS:
        try:
            found.extend(fetch_results_site(site, start, end))
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
            for r in ordered:  # rows saved before this column existed
                if not r.get("property_link"):
                    r["property_link"] = next((u for n, u in property_links(r["county"], r["parcel"]) if n == "Property"), "")
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
        text = f"📊 Auction results {end:%m/%d}\n" + "\n".join(lines)
        if dry_run or not (TELEGRAM_TOKEN or SMTP_USER):
            print(text)
        else:
            if TELEGRAM_TOKEN and TELEGRAM_CHAT_ID:
                send_telegram(text)
            if SMTP_USER and SMTP_PASS:
                send_email(f"📊 Auction results {end:%m/%d}", text)


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


def property_links(county: str, parcel: str) -> list[tuple[str, str]]:
    """Property Appraiser links for a parcel (Miami-Dade: property search; Broward: record + map)."""
    parcel = parcel or ""
    if not parcel or parcel.upper().startswith("MULTIPLE"):
        return []
    digits = re.sub(r"\D", "", parcel)
    if county == "miamidade" and len(digits) == 13:
        return [("Property", f"https://apps.miamidadepa.gov/propertysearch/#/?folio={digits}")]
    if county == "broward" and digits:
        return [("Property", f"https://bcpa.net/RecInfo.asp?URL_Folio={digits}"),
                ("Map", f"https://gisweb-adapters.bcpa.net/bcpawebmap_ex/bcpawebmap.aspx?FOLIO={digits}")]
    return []


# Chart colors (validated reference palette, light mode): fixed slots, never cycled.
C_BLUE, C_ORANGE, C_AQUA = "#2a78d6", "#eb6834", "#1baf7a"
C_GRAY, C_GRAY_DARK = "#c3c2b7", "#8a8983"
C_SURFACE, C_TEXT, C_TEXT2, C_GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#e7e6e1"


def weekly_data(today: date) -> dict:
    rows = list(load_results().values())
    for r in rows:
        r["_d"] = datetime.strptime(r["sale_date"], DATE_FORMAT).date()
        r["_amt"], r["_bid"] = _f(r.get("sold_amount")), _f(r.get("opening_bid"))
        r["_x"], r["_xe"] = _f(r.get("x_opening")), _f(r.get("x_est_value"))
        r["_sq"] = _f(r.get("lot_sqft"))
        r["_g"] = _group(r.get("land_use"))
        r["_3p"] = "3RD PARTY" in (r.get("sold_to") or "").upper()
        r["_sold"] = r["status"] == "Sold"
        r["_links"] = property_links(r["county"], r.get("parcel"))
    start = today - timedelta(days=7)
    d = {"today": today, "start": start, "end": today - timedelta(days=1), "rows": rows,
         "week": [r for r in rows if start <= r["_d"] < today]}
    d["third_all"] = [r for r in rows if r["_sold"] and r["_3p"] and r["_x"]]

    # per county, this week
    d["counties"] = []
    for county in sorted({r["county"] for r in d["week"]}):
        c = [r for r in d["week"] if r["county"] == county]
        sold = [r for r in c if r["_sold"]]
        third = [r["_x"] for r in sold if r["_3p"] and r["_x"]]
        red = sum(1 for r in c if r["status"].upper().startswith("REDEEM"))
        d["counties"].append({"name": COUNTY_NAME.get(county, county.title()), "n": len(c),
                              "days": len({r["_d"] for r in c}), "sold": len(sold),
                              "third": sum(1 for r in sold if r["_3p"]), "redeemed": red,
                              "median_x": _median(third)})
    w = d["week"]
    xs_w = [r["_x"] for r in w if r["_sold"] and r["_3p"] and r["_x"]]
    d["kpi"] = {"listings": len(w), "sold": sum(1 for r in w if r["_sold"]),
                "third": sum(1 for r in w if r["_sold"] and r["_3p"]),
                "median_x": _median(xs_w),
                "redeemed_pct": (sum(1 for r in w if r["status"].upper().startswith("REDEEM")) / len(w)) if w else None,
                "volume": sum(r["_amt"] or 0 for r in w if r["_sold"])}
    d["sold_week"] = sorted([r for r in w if r["_sold"]], key=lambda r: -(r["_amt"] or 0))

    # bidding guide (all data)
    guide = []
    for g in ("Vacant residential", "Single family", "Multi-family", "Mobile home", "Other vacant", "Other"):
        xs = [r["_x"] for r in d["third_all"] if r["_g"] == g]
        if not xs:
            continue
        ppsf = [r["_amt"] / r["_sq"] for r in d["third_all"] if r["_g"] == g and r["_amt"] and r["_sq"]]
        guide.append({"type": g, "n": len(xs), "median": _median(xs), "p75": _pct(xs, .75),
                      "ppsf": _median(ppsf) if g == "Vacant residential" and ppsf else None})
    d["guide"] = guide
    d["guide_by_type"] = {g["type"]: g for g in guide if g["n"] >= 3}
    xe = [r["_xe"] for r in d["third_all"] if r["_xe"] and r["_g"] == "Vacant residential"]
    d["lot_vs_comps"] = (_median(xe), len(xe)) if len(xe) >= 3 else None
    by_city: dict[str, list[float]] = {}
    for r in d["third_all"]:
        by_city.setdefault(_city(r), []).append(r["_x"])
    d["cities"] = sorted(((c, _median(v), len(v)) for c, v in by_city.items() if len(v) >= 3),
                         key=lambda t: -t[1])[:5]
    d["county_rates"] = []
    for county in sorted({r["county"] for r in rows}):
        c = [r for r in rows if r["county"] == county]
        d["county_rates"].append({
            "name": COUNTY_NAME.get(county, county.title()), "n": len(c),
            "redeemed": sum(1 for r in c if r["status"].upper().startswith("REDEEM")) / len(c),
            "cert": sum(1 for r in c if r["_sold"] and not r["_3p"]) / len(c),
            "third": sum(1 for r in c if r["_sold"] and r["_3p"]) / len(c)})

    # your matches in the next 7 days
    up = []
    for k, v in load_seen().items():
        if k.startswith("_") or not v.get("ok"):
            continue
        dd = days_until(v.get("sale_date", ""), today)
        if dd is None or not 0 <= dd <= 7:
            continue
        county = k.split(":")[0]
        desc = (v.get("land_use") or {}).get("desc") or ""
        g = d["guide_by_type"].get(_group(desc))
        bid = v.get("bid")
        up.append({"days": dd, "date": v["sale_date"], "county": COUNTY_NAME.get(county, county),
                   "cat": v.get("cat"), "where": ", ".join(x for x in (v.get("address"), (v.get("city") or "").split(",")[0].title()) if x)
                   or v.get("parcel") or "", "type": desc.title(), "bid": bid,
                   "est": (bid * g["median"], bid * g["p75"]) if bid and g else None,
                   "links": ([("Listing", v["link"])] if v.get("link") else []) + property_links(county, v.get("parcel"))})
    d["upcoming"] = sorted(up, key=lambda u: u["days"])
    return d


def weekly_charts(d: dict) -> dict[str, bytes]:
    """PNG charts (matplotlib). Returns {} if matplotlib isn't installed or there's no data."""
    try:
        import io
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        from matplotlib.ticker import FuncFormatter
    except ImportError:
        print("[weekly] matplotlib not installed; sending the report without charts", file=sys.stderr)
        return {}

    def style(ax, title):
        ax.set_facecolor(C_SURFACE)
        for s in ("top", "right", "left"):
            ax.spines[s].set_visible(False)
        ax.spines["bottom"].set_color(C_GRID)
        ax.tick_params(colors=C_TEXT2, labelsize=9, length=0)
        ax.set_title(title, loc="left", fontsize=12, color=C_TEXT, fontweight="bold", pad=24)

    def png(fig):
        buf = io.BytesIO()
        fig.savefig(buf, format="png", dpi=160, facecolor=C_SURFACE, bbox_inches="tight")
        plt.close(fig)
        return buf.getvalue()

    money_fmt = FuncFormatter(lambda v, _: f"${v / 1000:,.0f}K" if v >= 1000 else f"${v:,.0f}")
    out = {}
    rows = d["rows"]

    # 1) outcome of every sale day (stacked bars)
    days = sorted({(r["_d"], r["county"]) for r in rows})[-12:]
    if days:
        cats = [("Sold to outside bidder", C_BLUE, lambda r: r["_sold"] and r["_3p"]),
                ("Sold to cert holder", C_ORANGE, lambda r: r["_sold"] and not r["_3p"]),
                ("Redeemed", C_GRAY, lambda r: r["status"].upper().startswith("REDEEM")),
                ("Canceled / other", C_GRAY_DARK, lambda r: not r["_sold"] and not r["status"].upper().startswith("REDEEM"))]
        fig, ax = plt.subplots(figsize=(7.2, 3.4))
        labels = [f"{dt:%m/%d}\n{'BRW' if c == 'broward' else 'MDC'}" for dt, c in days]
        bottom = [0] * len(days)
        for name, color, f in cats:
            vals = [sum(1 for r in rows if (r["_d"], r["county"]) == k and f(r)) for k in days]
            ax.bar(labels, vals, bottom=bottom, color=color, label=name, width=0.6,
                   edgecolor=C_SURFACE, linewidth=2)
            bottom = [b + v for b, v in zip(bottom, vals)]
        for x, t in enumerate(bottom):
            ax.text(x, t + max(bottom) * 0.02, str(t), ha="center", va="bottom", fontsize=8, color=C_TEXT2)
        ax.set_ylim(0, max(bottom) * 1.12)
        ax.yaxis.grid(True, color=C_GRID, linewidth=0.8)
        ax.set_axisbelow(True)
        ax.set_ylabel("Listings", color=C_TEXT2, fontsize=9)
        ax.legend(ncol=4, fontsize=8, frameon=False, loc="lower left", bbox_to_anchor=(0, 1.02),
                  labelcolor=C_TEXT2, handlelength=1, columnspacing=1.2, borderaxespad=0)
        style(ax, "What happened on each sale day")
        out["outcomes"] = png(fig)

    # 2) opening bid vs price paid (outside bidders), log-log
    pts = [r for r in d["third_all"] if r["_bid"] and r["_amt"]]
    if pts:
        groups = [("Vacant residential", C_BLUE), ("Single family", C_ORANGE), ("Other", C_AQUA)]
        gof = lambda r: r["_g"] if r["_g"] in ("Vacant residential", "Single family") else "Other"
        fig, ax = plt.subplots(figsize=(7.2, 4.0))
        xlo, xhi = min(r["_bid"] for r in pts) * 0.7, max(r["_bid"] for r in pts) * 1.4
        ylo = min(min(r["_amt"] for r in pts), min(r["_bid"] for r in pts)) * 0.7
        yhi = max(r["_amt"] for r in pts) * 1.4
        for m in (1, 2, 5, 10):
            x0, x1 = max(xlo, ylo / m), min(xhi, yhi / m)
            if x0 >= x1:
                continue
            ax.plot([x0, x1], [x0 * m, x1 * m], color="#cfcec8", linewidth=1, linestyle="--", zorder=1)
            ax.text(x1, x1 * m, f" {m}×", color=C_TEXT2, fontsize=8,
                    va="bottom" if x1 < xhi else "center", ha="right" if x1 < xhi else "left")
        for name, color in groups:
            g = [r for r in pts if gof(r) == name]
            if g:
                ax.scatter([r["_bid"] for r in g], [r["_amt"] for r in g], s=55, color=color,
                           edgecolors=C_SURFACE, linewidths=1.5, label=f"{name} ({len(g)})", zorder=3)
        ax.set_xscale("log"); ax.set_yscale("log")
        ax.set_xlim(xlo, xhi); ax.set_ylim(ylo, yhi)
        ax.tick_params(which="minor", length=0)
        ax.minorticks_off()
        ax.xaxis.set_major_formatter(money_fmt); ax.yaxis.set_major_formatter(money_fmt)
        ax.set_xlabel("Opening bid", color=C_TEXT2, fontsize=9)
        ax.set_ylabel("Price paid", color=C_TEXT2, fontsize=9)
        ax.grid(True, color=C_GRID, linewidth=0.6, which="major")
        ax.set_axisbelow(True)
        ax.legend(ncol=3, fontsize=8, frameon=False, loc="lower left", bbox_to_anchor=(0, 1.02),
                  labelcolor=C_TEXT2, handletextpad=0.3, borderaxespad=0)
        style(ax, "Outside-bidder sales: opening bid vs. price paid (all data)")
        out["scatter"] = png(fig)

    # 3) median multiple by property type
    guide = [g for g in d["guide"] if g["n"] >= 2]
    if guide:
        fig, ax = plt.subplots(figsize=(7.2, 0.55 * len(guide) + 1.1))
        names = [f"{g['type']}  (n={g['n']})" for g in guide][::-1]
        vals = [g["median"] for g in guide][::-1]
        ax.barh(names, vals, color=C_BLUE, height=0.55, edgecolor=C_SURFACE, linewidth=2)
        for y, v in enumerate(vals):
            ax.text(v + max(vals) * 0.015, y, f"{v:.1f}×", va="center", fontsize=9, color=C_TEXT)
        ax.axvline(1, color=C_TEXT2, linewidth=1, linestyle="--")
        ax.xaxis.grid(True, color=C_GRID, linewidth=0.8)
        ax.set_axisbelow(True)
        ax.set_xlim(0, max(vals) * 1.15)
        ax.xaxis.set_major_formatter(FuncFormatter(lambda v, _: f"{v:.0f}×"))
        style(ax, "Typical price paid, as a multiple of the opening bid")
        ax.text(0, 1.04, "Median of outside-bidder sales · dashed line = opening bid", transform=ax.transAxes,
                fontsize=8, color=C_TEXT2)
        out["multiples"] = png(fig)
    return out


def _m(v) -> str:
    return "—" if v is None else f"${v:,.0f}"


def weekly_html(d: dict, chart_src: dict[str, str]) -> str:
    """Email-safe HTML report. chart_src maps chart name -> img src (cid:... or data:...)."""
    e = lambda s: html.escape(str(s))
    td = 'style="padding:7px 8px;border-bottom:1px solid #ecebe6;font-size:13px;vertical-align:top"'
    tdr = 'style="padding:7px 8px;border-bottom:1px solid #ecebe6;font-size:13px;text-align:right;white-space:nowrap;vertical-align:top"'
    th = 'style="padding:7px 8px;border-bottom:2px solid #d6d5cf;font-size:11px;text-transform:uppercase;letter-spacing:.04em;color:#52514e;text-align:left"'
    thr = th.replace("text-align:left", "text-align:right")
    h2 = 'style="font-size:17px;margin:30px 0 4px;color:#0b0b0b"'
    sub = 'style="font-size:13px;color:#52514e;margin:0 0 12px"'
    links = lambda ls: " · ".join(f'<a href="{e(u)}" style="color:#2a78d6;text-decoration:none">{e(n)}</a>' for n, u in ls)
    img = lambda k: (f'<img src="{chart_src[k]}" width="680" style="width:100%;max-width:680px;height:auto;display:block;margin:8px 0 4px" alt="">'
                     if k in chart_src else "")
    k = d["kpi"]
    P = []
    P.append(f'''<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Auction report {d["today"]:%m/%d/%Y}</title><meta name="color-scheme" content="light"></head>
<body style="margin:0;background:#f1f0ec;font-family:-apple-system,Segoe UI,Roboto,Helvetica,Arial,sans-serif;color:#0b0b0b">
<div style="max-width:760px;margin:0 auto;padding:16px">
<div style="background:#fcfcfb;border-radius:12px;padding:24px 22px">
<div style="font-size:12px;color:#52514e;text-transform:uppercase;letter-spacing:.06em">Tax deed auctions · Miami-Dade &amp; Broward</div>
<h1 style="font-size:24px;margin:4px 0 2px">Weekly report</h1>
<div style="font-size:14px;color:#52514e">{d["start"]:%b %d} – {d["end"]:%b %d, %Y}</div>''')

    if not d["rows"]:
        P.append('<p style="margin-top:24px">No results saved yet. Check that the <b>auction-results</b> Action is '
                 'running and committing <code>results.csv</code>.</p></div></div></body></html>')
        return "".join(P)

    # KPI tiles
    tiles = [("Listings", f'{k["listings"]}'), ("Sold", f'{k["sold"]}'),
             ("To outside bidders", f'{k["third"]}'),
             ("Median × opening", f'{k["median_x"]:.1f}×' if k["median_x"] else "—"),
             ("Redeemed", f'{k["redeemed_pct"]:.0%}' if k["redeemed_pct"] is not None else "—")]
    P.append('<table role="presentation" width="100%" cellspacing="0" cellpadding="0" style="margin-top:18px;border-collapse:separate;border-spacing:6px 0"><tr>')
    for label, val in tiles:
        P.append(f'<td style="background:#f4f3ef;border-radius:8px;padding:10px 10px;width:20%;vertical-align:top">'
                 f'<div style="font-size:11px;color:#52514e">{e(label)}</div>'
                 f'<div style="font-size:18px;font-weight:700;margin-top:2px">{e(val)}</div></td>')
    P.append("</tr></table>")
    if not d["week"]:
        P.append('<p style="font-size:14px;color:#52514e;margin:14px 0 0">No tax deed sales this week. '
                 'The guide below uses all data saved so far.</p>')
    for c in d["counties"]:
        mx = f', outside bidders paid a median <b>{c["median_x"]:.1f}×</b> the opening bid' if c["median_x"] else ""
        P.append(f'<p style="font-size:14px;margin:12px 0 0"><b>{e(c["name"])}</b>: {c["n"]} listings on {c["days"]} sale day(s) · '
                 f'{c["sold"]} sold ({c["third"]} to outside bidders) · {c["redeemed"]} redeemed{mx}.</p>')

    # this week's sales
    if d["sold_week"]:
        P.append(f'<h2 {h2}>What sold this week</h2><p {sub}>Sorted by price. Open the Property link to see what was sold.</p>')
        P.append('<table width="100%" cellspacing="0" cellpadding="0" style="border-collapse:collapse">')
        P.append(f'<tr><th {th}>Date</th><th {th}>Property</th><th {thr}>Opening</th><th {thr}>Paid</th></tr>')
        for r in d["sold_week"]:
            lot = f" · {int(r['_sq']):,} sq ft" if r["_sq"] else ""
            pa = _f(r.get("pa_total_val"))
            pav = f" · PA value {_m(pa)}" if pa else ""
            ls = r["_links"] + ([("Listing", r["listing"])] if r.get("listing") else [])
            buyer = "outside bidder" if r["_3p"] else "cert holder"
            mult = f"{r['_x']:.1f}× · " if r["_x"] else ""
            P.append(f'<tr><td {td}>{r["_d"]:%m/%d}<br><span style="color:#52514e;font-size:11px">{e(COUNTY_NAME.get(r["county"], r["county"]))}</span></td>'
                     f'<td {td}><b>{e(r["address"] or "No address")}</b>, {e(_city(r))}<br>'
                     f'<span style="color:#52514e;font-size:12px">{e(r["_g"])}{lot}{pav}</span><br>'
                     f'<span style="font-size:12px">{links(ls)}</span></td>'
                     f'<td {tdr}>{_m(r["_bid"])}</td><td {td.replace("vertical-align:top", "vertical-align:top;text-align:right")}><b style="white-space:nowrap">{_m(r["_amt"])}</b><br>'
                     f'<span style="color:#52514e;font-size:11px">{mult}{buyer}</span></td></tr>')
        P.append("</table>")

    # charts
    if chart_src:
        P.append(f'<h2 {h2}>Charts</h2>')
        P.append(img("outcomes"))
        P.append(img("scatter"))
        P.append(img("multiples"))

    # bidding guide
    P.append(f'<h2 {h2}>Bidding guide</h2><p {sub}>All {len(d["rows"])} results saved since '
             f'{min(r["_d"] for r in d["rows"]):%b %d}. Based on sales to outside bidders, where there was real competition.</p>')
    if len(d["third_all"]) < 5:
        P.append(f'<p style="font-size:13px;color:#52514e">Only {len(d["third_all"])} outside-bidder sale(s) so far. '
                 'These numbers become reliable after about 20.</p>')
    if d["guide"]:
        P.append('<table width="100%" cellspacing="0" cellpadding="0" style="border-collapse:collapse">')
        P.append(f'<tr><th {th}>Property type</th><th {thr}>Sales</th><th {thr}>Median ×</th>'
                 f'<th {thr}>75% sold ≤</th><th {thr}>$/sq ft</th></tr>')
        for g in d["guide"]:
            ppsf = f"${g['ppsf']:,.2f}" if g["ppsf"] else "—"
            P.append(f'<tr><td {td}>{e(g["type"])}</td><td {tdr}>{g["n"]}</td><td {tdr}><b>{g["median"]:.1f}×</b></td>'
                     f'<td {tdr}>{g["p75"]:.1f}×</td><td {tdr}>{ppsf}</td></tr>')
        P.append("</table>")
    notes = []
    if d["lot_vs_comps"]:
        notes.append(f'Vacant lots sell for a median <b>{d["lot_vs_comps"][0]:.0%}</b> of their comps value (n={d["lot_vs_comps"][1]}).')
    if d["cities"]:
        notes.append("Most competitive cities: " + ", ".join(f'{e(c)} <b>{m:.1f}×</b> (n={n})' for c, m, n in d["cities"]) + ".")
    for c in d["county_rates"]:
        notes.append(f'{e(c["name"])}: {c["redeemed"]:.0%} redeemed before the sale, {c["cert"]:.0%} went to the cert holder '
                     f'with no bids, {c["third"]:.0%} sold to outside bidders (n={c["n"]}).')
    if notes:
        P.append('<ul style="font-size:13px;padding-left:18px;margin:12px 0 0">' + "".join(f"<li style='margin:4px 0'>{n}</li>" for n in notes) + "</ul>")

    # upcoming
    P.append(f'<h2 {h2}>Your matches in the next 7 days</h2>')
    if not d["upcoming"]:
        P.append(f'<p {sub}>None of your matches go to sale in the next 7 days.</p>')
    else:
        P.append(f'<p {sub}>Likely price = opening bid × what similar properties have gone for (median – 75th percentile).</p>')
        P.append('<table width="100%" cellspacing="0" cellpadding="0" style="border-collapse:collapse">')
        P.append(f'<tr><th {th}>Sale</th><th {th}>Property</th><th {thr}>Opening</th><th {thr}>Likely price</th></tr>')
        for u in d["upcoming"]:
            icon = "🌱" if u["cat"] == "lot" else "🏠"
            est = f'{_m(u["est"][0])} – {_m(u["est"][1])}' if u["est"] else '<span style="color:#52514e">not enough data</span>'
            P.append(f'<tr><td {td}>{e(u["date"][:5])}<br><span style="color:#52514e;font-size:11px">{e(u["county"])}</span></td>'
                     f'<td {td}>{icon} <b>{e(u["where"])}</b><br><span style="color:#52514e;font-size:12px">{e(u["type"])}</span><br>'
                     f'<span style="font-size:12px">{links(u["links"])}</span></td>'
                     f'<td {tdr}>{_m(u["bid"])}</td><td {tdr}>{est}</td></tr>')
        P.append("</table>")
    P.append('<p style="font-size:11px;color:#8a8983;margin-top:26px">Generated by auction-watcher from the public auction '
             'calendars. For your own bidding decisions only.</p></div></div></body></html>')
    return "".join(P)


def weekly_telegram(d: dict) -> str:
    """Short Telegram summary (HTML parse mode); the full report goes as an attached file."""
    e = html.escape
    k = d["kpi"]
    L = [f"<b>📈 Weekly auction report</b>", f"<i>{d['start']:%b %d} – {d['end']:%b %d}</i>", ""]
    if not d["rows"]:
        L.append("No results saved yet. Check that the auction-results Action is running.")
        return "\n".join(L)
    if d["week"]:
        mx = f" · median <b>{k['median_x']:.1f}×</b> opening" if k["median_x"] else ""
        L.append(f"<b>{k['listings']}</b> listings · <b>{k['sold']}</b> sold ({k['third']} to outside bidders) · "
                 f"{k['redeemed_pct']:.0%} redeemed{mx}")
    else:
        L.append("No tax deed sales this week.")
    if d["sold_week"]:
        L += ["", "<b>Top sales</b>"]
        short = {"Vacant residential": "Lot", "Single family": "House", "Multi-family": "Multi",
                 "Mobile home": "Mobile", "Other vacant": "Lot*", "Condo": "Condo"}
        rows = [(_city(r)[:12], short.get(r["_g"], "Other"), _m(r["_amt"]),
                 f"{r['_x']:.1f}x" if r["_x"] else "cert") for r in d["sold_week"][:6]]
        table = [("City", "Type", "Paid", "x open")] + rows
        w = [max(len(r[i]) for r in table) for i in range(4)]
        fmt = lambda r: f"{r[0]:<{w[0]}} {r[1]:<{w[1]}} {r[2]:>{w[2]}} {r[3]:>{w[3]}}"
        L.append("<pre>" + e("\n".join(fmt(r) for r in table)) + "</pre>")
    if d["upcoming"]:
        L += ["", f"<b>Next 7 days: {len(d['upcoming'])} of your matches</b>"]
        for u in d["upcoming"][:5]:
            icon = "🌱" if u["cat"] == "lot" else "🏠"
            est = f" → likely {_m(u['est'][0])}–{_m(u['est'][1])}" if u["est"] else ""
            L.append(f"{icon} {e(u['date'][:5])} {e(u['where'])} · opens {_m(u['bid'])}{est}")
    L += ["", "Full report with tables, charts and Property Appraiser links attached ⬇️"]
    return "\n".join(L)


def send_weekly(today: date, dry_run: bool) -> None:
    import base64
    d = weekly_data(today)
    charts = weekly_charts(d) if d["rows"] else {}
    file_html = weekly_html(d, {k: "data:image/png;base64," + base64.b64encode(v).decode() for k, v in charts.items()})
    name = f"auction-report-{today:%Y-%m-%d}.html"
    if dry_run or not (TELEGRAM_TOKEN or SMTP_USER):
        Path(name).write_text(file_html, encoding="utf-8")
        for k, v in charts.items():
            Path(f"chart-{k}.png").write_bytes(v)
        print(weekly_telegram(d))
        print(f"\n[weekly] wrote {name} and {len(charts)} chart(s)")
        return
    if TELEGRAM_TOKEN and TELEGRAM_CHAT_ID:
        tg("sendMessage", chat_id=TELEGRAM_CHAT_ID, text=weekly_telegram(d), parse_mode="HTML",
           disable_web_page_preview=True)
        if charts:
            media = [{"type": "photo", "media": f"attach://{k}"} for k in charts]
            r = requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMediaGroup",
                              data={"chat_id": TELEGRAM_CHAT_ID, "media": json.dumps(media)},
                              files={k: (f"{k}.png", v, "image/png") for k, v in charts.items()}, timeout=60)
            if not r.json().get("ok"):
                print(f"[warn] Telegram charts: {r.text[:200]}", file=sys.stderr)
        r = requests.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendDocument",
                          data={"chat_id": TELEGRAM_CHAT_ID, "caption": "Full weekly report (open in your browser)"},
                          files={"document": (name, file_html.encode("utf-8"), "text/html")}, timeout=60)
        if not r.json().get("ok"):
            print(f"[warn] Telegram report file: {r.text[:200]}", file=sys.stderr)
    if SMTP_USER and SMTP_PASS:
        msg = EmailMessage()
        msg["Subject"] = f"📈 Weekly auction report · {d['start']:%b %d} – {d['end']:%b %d}"
        msg["From"], msg["To"] = SMTP_USER, EMAIL_TO
        msg.set_content(re.sub(r"<[^>]+>", "", weekly_telegram(d)))
        msg.add_alternative(weekly_html(d, {k: f"cid:{k}" for k in charts}), subtype="html")
        body = msg.get_payload()[1]
        for k, v in charts.items():
            body.add_related(v, "image", "png", cid=f"<{k}>")
        with smtplib.SMTP_SSL("smtp.gmail.com", 465) as smtp:
            smtp.login(SMTP_USER, SMTP_PASS)
            smtp.send_message(msg)


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
    out.extend(property_links(item.get("county", "miamidade"), item.get("parcel")))
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
    ap.add_argument("--since", help="with --results: collect every sale day from MM/DD/YYYY to today "
                                    f"(default: the last {RESULTS_DAYS_BACK} days)")
    args = ap.parse_args()

    if args.weekly:
        send_weekly(date.today(), args.dry_run)
        return

    if args.results:
        end = date.today()
        start = (datetime.strptime(args.since, "%m/%d/%Y").date() if args.since
                 else end - timedelta(days=RESULTS_DAYS_BACK))
        collect_results(start, end, args.dry_run)
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
