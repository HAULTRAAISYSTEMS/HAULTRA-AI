from flask import (
    Flask, request, redirect, url_for, session, flash,
    render_template_string, send_file, abort, jsonify
)
import sqlite3
import os
import re
import io
import csv
import html
import math
import secrets
import warnings
import time
import json
import urllib.request
import urllib.parse
from datetime import datetime, date, timedelta
from functools import wraps
from werkzeug.security import generate_password_hash, check_password_hash
from werkzeug.utils import secure_filename

# Optional PDF export
PDF_ENABLED = True
try:
    from reportlab.lib.pagesizes import letter
    from reportlab.pdfgen import canvas
except Exception:
    PDF_ENABLED = False

app = Flask(__name__)
_secret_key = os.environ.get("SECRET_KEY", "")
if not _secret_key:
    warnings.warn(
        "SECRET_KEY env var not set — using an insecure default. Set SECRET_KEY before deploying.",
        stacklevel=2,
    )
    _secret_key = "haultra-super-secret-key-change-me"
app.secret_key = _secret_key

DATABASE     = os.environ.get("DATABASE_PATH", "haultra.db")
UPLOAD_FOLDER = os.environ.get("UPLOAD_FOLDER", os.path.join("static", "uploads"))
ALLOWED_EXTENSIONS = {"png", "jpg", "jpeg", "webp", "pdf"}
os.makedirs(UPLOAD_FOLDER, exist_ok=True)
app.config["UPLOAD_FOLDER"] = UPLOAD_FOLDER


# =========================================================
# HELPERS
# =========================================================
def e(value):
    return html.escape("" if value is None else str(value))


def now_ts():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def today_str():
    return date.today().strftime("%Y-%m-%d")


def allowed_file(filename):
    return "." in filename and filename.rsplit(".", 1)[1].lower() in ALLOWED_EXTENSIONS


def get_db():
    conn = sqlite3.connect(DATABASE)
    conn.row_factory = sqlite3.Row
    return conn


def get_csrf_token():
    if "_csrf_token" not in session:
        session["_csrf_token"] = secrets.token_hex(32)
    return session["_csrf_token"]


@app.before_request
def csrf_protect():
    if request.method == "POST":
        token = session.get("_csrf_token")
        # Support form data, JSON body, or explicit header
        if request.is_json:
            form_token = (request.get_json(silent=True) or {}).get("_csrf_token") \
                         or request.headers.get("X-CSRF-Token")
        else:
            form_token = request.form.get("_csrf_token")
        if not token or token != form_token:
            abort(403)


# Routes that are always accessible regardless of subscription status
_SUBSCRIPTION_EXEMPT = {
    "login", "logout", "company_register", "static",
    "subscription_blocked", "privacy_policy", "terms_of_service",
}

@app.before_request
def subscription_enforce():
    """
    Auto-suspend expired trials, then block suspended/cancelled accounts.
    Runs on every request after login.
    """
    if request.endpoint in _SUBSCRIPTION_EXEMPT or not session.get("company_id"):
        return

    company_id = session["company_id"]
    conn = get_db()
    co = conn.execute(
        "SELECT subscription_plan, subscription_status, trial_ends_at FROM companies WHERE id=?",
        (company_id,)
    ).fetchone()
    conn.close()

    if not co:
        return

    # Auto-expire trial if past end date
    if (co["subscription_plan"] == "trial"
            and co["subscription_status"] == "active"
            and co["trial_ends_at"]):
        try:
            ends = datetime.strptime(co["trial_ends_at"], "%Y-%m-%d %H:%M:%S")
        except ValueError:
            ends = None
        if ends and datetime.now() > ends:
            _conn = get_db()
            _conn.execute(
                "UPDATE companies SET subscription_status='suspended' WHERE id=?",
                (company_id,)
            )
            _conn.execute(
                """INSERT INTO subscriptions (company_id, plan, status, started_at, notes, created_at)
                   VALUES (?,?,?,?,?,?)""",
                (company_id, "trial", "suspended", now_ts(),
                 "Auto-suspended: trial period expired", now_ts())
            )
            _conn.commit()
            _conn.close()
            co = {"subscription_status": "suspended", "subscription_plan": "trial"}

    if co["subscription_status"] in ("suspended", "cancelled"):
        # Allow boss to view subscription page so they can act
        if request.endpoint in ("company_subscription", "company_settings"):
            return
        return redirect(url_for("subscription_blocked"))


def col_exists(conn, table_name, column_name):
    rows = conn.execute(f"PRAGMA table_info({table_name})").fetchall()
    return any(r[1] == column_name for r in rows)


def safe_add_column(conn, table_name, ddl):
    try:
        conn.execute(f"ALTER TABLE {table_name} ADD COLUMN {ddl}")
        conn.commit()
    except sqlite3.OperationalError:
        pass


def _haversine_mi(lat1, lon1, lat2, lon2):
    """Straight-line distance in miles between two lat/lng points."""
    R = 3958.8
    dlat = math.radians(lat2 - lat1)
    dlon = math.radians(lon2 - lon1)
    a = (math.sin(dlat / 2) ** 2
         + math.cos(math.radians(lat1)) * math.cos(math.radians(lat2))
         * math.sin(dlon / 2) ** 2)
    return R * 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))


def _geocode_server(address):
    """Geocode an address with Nominatim. Returns (lat, lng) or None."""
    url = ("https://nominatim.openstreetmap.org/search?format=json&limit=1&q="
           + urllib.parse.quote_plus(address))
    req = urllib.request.Request(url, headers={
        "User-Agent": "HaultraAISystems/1.0 route-optimizer",
        "Accept-Language": "en",
    })
    try:
        with urllib.request.urlopen(req, timeout=6) as resp:
            data = json.loads(resp.read().decode())
            if data:
                return float(data[0]["lat"]), float(data[0]["lon"])
    except Exception:
        pass
    return None


def _nearest_neighbor(stops_coords):
    """
    Greedy nearest-neighbor route ordering.
    stops_coords: list of (stop_id, lat, lng)
    Returns stop_ids in optimized order.
    """
    if not stops_coords:
        return []
    visited   = [stops_coords[0]]
    remaining = list(stops_coords[1:])
    while remaining:
        last = visited[-1]
        nearest = min(remaining,
                      key=lambda s: _haversine_mi(last[1], last[2], s[1], s[2]))
        visited.append(nearest)
        remaining.remove(nearest)
    return [s[0] for s in visited]


def load_stop_photos(conn, stop_ids):
    """Return dict {stop_id: [photo_row, ...]} for the given stop IDs."""
    if not stop_ids:
        return {}
    placeholders = ",".join("?" * len(stop_ids))
    rows = conn.execute(f"""
        SELECT rp.id, rp.stop_id, rp.file_path, rp.uploaded_at,
               COALESCE(u.username, 'Unknown') AS uploader
        FROM route_photos rp
        LEFT JOIN users u ON rp.uploaded_by = u.id
        WHERE rp.stop_id IN ({placeholders})
        ORDER BY rp.stop_id, rp.uploaded_at ASC
    """, stop_ids).fetchall()
    result = {}
    for r in rows:
        result.setdefault(r["stop_id"], []).append(r)
    return result


def build_photo_gallery_html(photos):
    """Render a gallery of uploaded photos with uploader name and timestamp."""
    if not photos:
        return ""
    items = []
    for p in photos:
        path = "/" + p["file_path"].replace("\\", "/")
        ext = p["file_path"].rsplit(".", 1)[-1].lower() if "." in p["file_path"] else ""
        if ext == "pdf":
            media = f'<a class="photo-pdf-link" href="{e(path)}" target="_blank">&#128196; PDF Document</a>'
        else:
            media = f'<a href="{e(path)}" target="_blank"><img class="photo-thumb" src="{e(path)}" alt="stop photo" loading="lazy"></a>'
        items.append(
            f'<div class="photo-item">'
            f'{media}'
            f'<div class="photo-meta">{e(p["uploader"])}<br>{e(p["uploaded_at"])}</div>'
            f'</div>'
        )
    return '<div class="photo-gallery">' + "".join(items) + "</div>"


def init_db():
    conn = get_db()
    cur = conn.cursor()

    cur.execute("""
    CREATE TABLE IF NOT EXISTS users (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        username TEXT UNIQUE NOT NULL,
        password_hash TEXT NOT NULL,
        role TEXT NOT NULL CHECK(role IN ('boss', 'driver')),
        full_name TEXT,
        phone TEXT,
        created_at TEXT NOT NULL
    )
    """)

    cur.execute("""
    CREATE TABLE IF NOT EXISTS routes (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        route_date TEXT NOT NULL,
        route_name TEXT NOT NULL,
        raw_text TEXT,
        assigned_to INTEGER,
        created_by INTEGER NOT NULL,
        status TEXT NOT NULL DEFAULT 'open' CHECK(status IN ('open','in_progress','completed')),
        notes TEXT,
        started_at TEXT,
        completed_at TEXT,
        created_at TEXT NOT NULL,
        FOREIGN KEY (assigned_to) REFERENCES users(id),
        FOREIGN KEY (created_by) REFERENCES users(id)
    )
    """)

    cur.execute("""
    CREATE TABLE IF NOT EXISTS stops (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        route_id INTEGER NOT NULL,
        stop_order INTEGER NOT NULL,
        customer_name TEXT,
        address TEXT,
        city TEXT,
        state TEXT,
        zip_code TEXT,
        action TEXT,
        container_size TEXT,
        ticket_number TEXT,
        reference_number TEXT,
        notes TEXT,
        status TEXT NOT NULL DEFAULT 'open' CHECK(status IN ('open','completed')),
        completed_at TEXT,
        driver_signature TEXT,
        photo_path TEXT,
        created_at TEXT NOT NULL,
        FOREIGN KEY (route_id) REFERENCES routes(id)
    )
    """)

    cur.execute("""
    CREATE TABLE IF NOT EXISTS route_photos (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        stop_id INTEGER NOT NULL,
        file_path TEXT NOT NULL,
        uploaded_at TEXT NOT NULL,
        FOREIGN KEY (stop_id) REFERENCES stops(id)
    )
    """)

    cur.execute("""
    CREATE TABLE IF NOT EXISTS load_scores (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        origin TEXT,
        destination TEXT,
        pickup_time TEXT,
        payout REAL DEFAULT 0,
        miles REAL DEFAULT 0,
        estimated_profit REAL DEFAULT 0,
        score REAL DEFAULT 0,
        notes TEXT,
        created_by INTEGER,
        created_at TEXT NOT NULL,
        FOREIGN KEY (created_by) REFERENCES users(id)
    )
    """)
    cur.execute("""
    CREATE TABLE IF NOT EXISTS orders (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        customer_name TEXT NOT NULL,
        phone TEXT,
        email TEXT,
        address TEXT NOT NULL,
        city TEXT,
        state TEXT,
        zip_code TEXT,
        service_type TEXT NOT NULL,
        container_size TEXT,
        notes TEXT,
        requested_date TEXT,
        status TEXT NOT NULL DEFAULT 'new' CHECK(status IN ('new','converted','closed')),
        company_id INTEGER,
        created_at TEXT NOT NULL
    )
    """)

    cur.execute("""
    CREATE TABLE IF NOT EXISTS companies (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        name TEXT NOT NULL,
        slug TEXT UNIQUE NOT NULL,
        owner_id INTEGER,
        subscription_plan TEXT NOT NULL DEFAULT 'trial'
            CHECK(subscription_plan IN ('trial','starter','pro','enterprise')),
        subscription_status TEXT NOT NULL DEFAULT 'active'
            CHECK(subscription_status IN ('active','suspended','cancelled')),
        max_drivers INTEGER NOT NULL DEFAULT 5,
        trial_ends_at TEXT,
        created_at TEXT NOT NULL,
        FOREIGN KEY (owner_id) REFERENCES users(id)
    )
    """)

    cur.execute("""
    CREATE TABLE IF NOT EXISTS subscriptions (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        company_id INTEGER NOT NULL,
        plan TEXT NOT NULL,
        status TEXT NOT NULL DEFAULT 'active',
        started_at TEXT NOT NULL,
        ends_at TEXT,
        notes TEXT,
        created_at TEXT NOT NULL,
        FOREIGN KEY (company_id) REFERENCES companies(id)
    )
    """)

    cur.execute("""
    CREATE TABLE IF NOT EXISTS dump_locations (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        name TEXT NOT NULL,
        address TEXT,
        city TEXT,
        state TEXT,
        zip_code TEXT,
        notes TEXT,
        active INTEGER NOT NULL DEFAULT 1,
        created_at TEXT NOT NULL
    )
    """)

    # Seed dump locations if table is empty
    if cur.execute("SELECT COUNT(*) FROM dump_locations").fetchone()[0] == 0:
        _seed_dumps = [
            ("Bay",         "83 Pagan Ave",          "Smithfield",    "VA", "23430", ""),
            ("SPSA Landfill","1 Bob Foeller Dr",      "Suffolk",       "VA", "",      ""),
            ("Holland",     "4801 Nansemond Pkwy",   "Suffolk",       "VA", "",      ""),
            ("Spivey",      "228 Salters Creek Rd",  "Hampton",       "VA", "",      ""),
            ("SB Cox",      "217 Cox Dr",            "Yorktown",      "VA", "",      ""),
            ("United",      "161 Wellman St",        "Norfolk",       "VA", "",      ""),
            ("Waterway",    "1431 Precon Dr",        "Chesapeake",    "VA", "",      ""),
            ("Dominion",    "5444 Bainbridge Blvd",  "Chesapeake",    "VA", "",      ""),
            ("Sykes",       "124 Sykes Ave",         "Virginia Beach","VA", "",      ""),
            ("MM GU2737",   "Seaboard Rd",           "",              "VA", "",      "Verify full city and ZIP before production"),
        ]
        _ts = now_ts()
        for _n, _a, _c, _s, _z, _notes in _seed_dumps:
            cur.execute(
                "INSERT INTO dump_locations (name, address, city, state, zip_code, notes, active, created_at) VALUES (?,?,?,?,?,?,1,?)",
                (_n, _a, _c, _s, _z, _notes, _ts)
            )

    # --- column migrations (safe, idempotent) ---
    safe_add_column(conn, "users", "full_name TEXT")
    safe_add_column(conn, "users", "phone TEXT")
    safe_add_column(conn, "users", "company_id INTEGER")
    safe_add_column(conn, "users", "is_superadmin INTEGER NOT NULL DEFAULT 0")
    safe_add_column(conn, "routes", "started_at TEXT")
    safe_add_column(conn, "routes", "company_id INTEGER")
    safe_add_column(conn, "orders", "email TEXT")
    safe_add_column(conn, "orders", "city TEXT")
    safe_add_column(conn, "orders", "state TEXT")
    safe_add_column(conn, "orders", "zip_code TEXT")
    safe_add_column(conn, "orders", "container_size TEXT")
    safe_add_column(conn, "orders", "requested_date TEXT")
    safe_add_column(conn, "orders", "company_id INTEGER")
    safe_add_column(conn, "load_scores", "company_id INTEGER")
    safe_add_column(conn, "route_photos", "uploaded_by INTEGER")
    safe_add_column(conn, "routes", "dump_location_id INTEGER")

    # --- default company bootstrap ---
    default_co = conn.execute("SELECT id FROM companies LIMIT 1").fetchone()
    if not default_co:
        conn.execute(
            """INSERT INTO companies (name, slug, subscription_plan, subscription_status,
               max_drivers, trial_ends_at, created_at)
               VALUES (?,?,?,?,?,?,?)""",
            ("Default Company", "default", "trial", "active", 10, None, now_ts())
        )
        conn.commit()
    default_co_id = conn.execute("SELECT id FROM companies LIMIT 1").fetchone()["id"]

    # migrate orphaned rows to the default company
    conn.execute("UPDATE users SET company_id=? WHERE company_id IS NULL", (default_co_id,))
    conn.execute("UPDATE routes SET company_id=? WHERE company_id IS NULL", (default_co_id,))
    conn.execute("UPDATE orders SET company_id=? WHERE company_id IS NULL", (default_co_id,))
    conn.execute("UPDATE load_scores SET company_id=? WHERE company_id IS NULL", (default_co_id,))
    conn.commit()

    existing_boss = cur.execute("SELECT id FROM users WHERE role='boss' LIMIT 1").fetchone()
    if not existing_boss:
        cur.execute(
            """INSERT INTO users (username, password_hash, role, full_name, phone,
               company_id, created_at) VALUES (?, ?, ?, ?, ?, ?, ?)""",
            ("boss", generate_password_hash("boss123"), "boss", "Boss", "", default_co_id, now_ts())
        )
        conn.commit()
        # make the default boss the company owner
        boss_id = cur.lastrowid
        conn.execute("UPDATE companies SET owner_id=? WHERE id=?", (boss_id, default_co_id))
        conn.commit()

    conn.close()


# =========================================================
# AUTH / SESSION
# =========================================================
def login_required(fn):
    @wraps(fn)
    def wrapper(*args, **kwargs):
        if "user_id" not in session:
            flash("Login required.", "error")
            return redirect(url_for("login"))
        return fn(*args, **kwargs)
    return wrapper


def boss_required(fn):
    @wraps(fn)
    def wrapper(*args, **kwargs):
        if "user_id" not in session:
            flash("Login required.", "error")
            return redirect(url_for("login"))
        if session.get("role") != "boss":
            flash("Boss access only.", "error")
            return redirect(url_for("dashboard"))
        return fn(*args, **kwargs)
    return wrapper

def driver_required(fn):
    @wraps(fn)
    def wrapper(*args, **kwargs):
        if "user_id" not in session:
            flash("Login required.", "error")
            return redirect(url_for("login"))
        if session.get("role") != "driver":
            flash("Driver access only.", "error")
            return redirect(url_for("dashboard"))
        return fn(*args, **kwargs)
    return wrapper

def superadmin_required(fn):
    @wraps(fn)
    def wrapper(*args, **kwargs):
        if "user_id" not in session:
            flash("Login required.", "error")
            return redirect(url_for("login"))
        if not session.get("is_superadmin"):
            flash("Superadmin access only.", "error")
            return redirect(url_for("dashboard"))
        return fn(*args, **kwargs)
    return wrapper


def get_current_user():
    if "user_id" not in session:
        return None
    conn = get_db()
    user = conn.execute("SELECT * FROM users WHERE id = ?", (session["user_id"],)).fetchone()
    conn.close()
    return user


def cid():
    """Return the current session's company_id (None if not logged in)."""
    return session.get("company_id")


def get_company_route(conn, route_id):
    """Fetch a route only if it belongs to the current company. Returns None otherwise."""
    return conn.execute(
        "SELECT * FROM routes WHERE id=? AND company_id=?",
        (route_id, cid())
    ).fetchone()


def get_company_stop(conn, stop_id):
    """Fetch a stop (with route fields) only if it belongs to the current company."""
    return conn.execute(
        """SELECT s.*, r.assigned_to, r.company_id, r.id AS route_id_int
           FROM stops s JOIN routes r ON s.route_id = r.id
           WHERE s.id=? AND r.company_id=?""",
        (stop_id, cid())
    ).fetchone()


# =========================================================
# ROUTE PARSER
# =========================================================
def clean_line(line):
    line = line.replace("\t", " ").replace("•", " ").replace("–", "-")
    line = re.sub(r"\s+", " ", line).strip()
    return line


def looks_like_address(line):
    line = line.strip()

    if not re.match(r"^\d{1,6}\s+", line):
        return False

    lower = line.lower()
    bad_starts = [
        "ticket", "tkt", "job", "ref", "load",
        "notes", "note",
        "pickup", "pick up",
        "drop", "swap", "dump",
        "service", "remove", "deliver", "delivery"
    ]

    if any(lower.startswith(x) for x in bad_starts):
        return False

    return True

def extract_city_state_zip(line):
    m = re.search(r"([A-Za-z .'-]+),\s*([A-Z]{2})\s*(\d{5})?", line)
    if m:
        return m.group(1).strip(), m.group(2).strip(), (m.group(3) or "").strip()
    return "", "", ""


def extract_ticket(line):
    patterns = [
        r"(?:ticket|tkt|job|ref|load)\s*#?:?\s*([A-Za-z0-9\-\/]+)",
        r"#\s*([A-Za-z0-9\-\/]+)"
    ]
    for p in patterns:
        m = re.search(p, line, re.IGNORECASE)
        if m:
            return m.group(1).strip()
    return ""


def extract_container_size(line):
    patterns = [
        r"\b(10|12|15|20|30|40)\s*(?:yd|yard|yards)\b",
        r"\b(10|12|15|20|30|40)\b"
    ]
    for p in patterns:
        m = re.search(p, line, re.IGNORECASE)
        if m:
            return m.group(1).strip()
    return ""


def extract_action(line):
    lower = line.lower()
    action_map = [
        ("swap", "Swap"),
        ("switch", "Swap"),
        ("remove", "Remove"),
        ("pickup", "Pickup"),
        ("pick up", "Pickup"),
        ("drop", "Drop"),
        ("delivery", "Drop"),
        ("deliver", "Drop"),
        ("dump", "Dump"),
        ("empty", "Dump"),
        ("final", "Final"),
        ("relocate", "Relocate"),
        ("service", "Service")
    ]
    for key, label in action_map:
        if key in lower:
            return label
    return ""


def split_into_stop_blocks(raw_text):
    lines = [clean_line(x) for x in raw_text.splitlines()]
    lines = [x for x in lines if x]
    if not lines:
        return []

    blocks = []
    current = []

    for line in lines:
        if re.match(r"^\d+[\).\-\s]+", line):
            if current:
                blocks.append(current)
                current = []
        current.append(line)

    if current:
        blocks.append(current)

    return blocks


def parse_stop_block(lines, order_num):
    customer_name = ""
    address = ""
    city = ""
    state = ""
    zip_code = ""
    action = ""
    container_size = ""
    ticket_number = ""
    reference_number = ""
    notes = []

    # Clean lines first
    cleaned_lines = [x.strip() for x in lines if x.strip()]

    if not cleaned_lines:
        return {
            "stop_order": order_num,
            "customer_name": "",
            "address": "",
            "city": "",
            "state": "",
            "zip_code": "",
            "action": "Service",
            "container_size": "",
            "ticket_number": "",
            "reference_number": "",
            "notes": ""
        }

    # 1) First line = customer, remove "1." / "2." / etc
    first_line = cleaned_lines[0]
    customer_name = re.sub(r"^\d+[\).\-\s]+", "", first_line).strip()

    # 2) Find first true address line AFTER customer
    address_index = None
    for i in range(1, len(cleaned_lines)):
        if looks_like_address(cleaned_lines[i]):
            address = cleaned_lines[i]
            address_index = i
            break

    # 3) If next line after address is city/state/zip, capture it
    if address_index is not None and address_index + 1 < len(cleaned_lines):
        csz = extract_city_state_zip(cleaned_lines[address_index + 1])
        if any(csz):
            city, state, zip_code = csz

    # 4) Parse action / size / ticket / reference from all lines
    for line in cleaned_lines:
        if not action:
            found_action = extract_action(line)
            if found_action:
                action = found_action

        if not container_size:
            found_size = extract_container_size(line)
            if found_size:
                container_size = found_size

        if not ticket_number:
            found_ticket = extract_ticket(line)
            if found_ticket:
                ticket_number = found_ticket

        if not reference_number:
            m = re.search(r"(?:po|ref)\s*#?:?\s*([A-Za-z0-9\-\/]+)", line, re.IGNORECASE)
            if m:
                reference_number = m.group(1).strip()

    # 5) Default action
    if not action:
        action = "Service"

    # 6) Notes = everything except the numbered customer line
    notes = "\n".join(cleaned_lines).strip()

    return {
        "stop_order": order_num,
        "customer_name": customer_name,
        "address": address,
        "city": city,
        "state": state,
        "zip_code": zip_code,
        "action": action,
        "container_size": container_size,
        "ticket_number": ticket_number,
        "reference_number": reference_number,
        "notes": notes
    }

def parse_boss_text(raw_text):
    blocks = split_into_stop_blocks(raw_text)
    parsed = []

    for idx, block in enumerate(blocks, start=1):
        stop = parse_stop_block(block, idx)
        if stop["customer_name"] or stop["address"]:
            parsed.append(stop)

    return parsed 

# =========================================================
# LOAD SCORING / AI SIDE
# =========================================================
def parse_money(value):
    value = (value or "").replace(",", "").replace("$", "").strip()
    if not value:
        return 0.0
    try:
        return float(value)
    except ValueError:
        return 0.0


def estimate_miles(origin, destination):
    # lightweight placeholder estimation when miles are not provided
    text = f"{origin} {destination}".lower()
    base = 120
    if "virginia beach" in text and "richmond" in text:
        return 110
    if "norfolk" in text and "atlanta" in text:
        return 560
    if "chesapeake" in text and "charlotte" in text:
        return 330
    if origin and destination:
        token_count = len((origin + " " + destination).split())
        return max(base, token_count * 35)
    return 0


def score_load_record(origin, destination, pickup_time, payout, miles):
    if not miles or miles <= 0:
        miles = estimate_miles(origin, destination)

    rpm = payout / miles if miles > 0 else 0
    estimated_cost = miles * 1.35
    estimated_profit = payout - estimated_cost

    score = 0
    score += min(rpm * 25, 50)
    score += 20 if estimated_profit > 500 else max(estimated_profit / 25, 0)

    pickup_bonus = 0
    pickup_lower = (pickup_time or "").lower()
    if "am" in pickup_lower:
        pickup_bonus += 8
    elif "pm" in pickup_lower:
        pickup_bonus += 4
    score += pickup_bonus

    if miles <= 200:
        score += 18
    elif miles <= 400:
        score += 12
    elif miles <= 650:
        score += 7
    else:
        score += 2

    score = round(min(score, 100), 1)
    return {
        "miles": round(miles, 1),
        "estimated_profit": round(estimated_profit, 2),
        "score": score,
        "rpm": round(rpm, 2)
    }


def parse_load_input_line(line):
    raw = line.strip()
    if not raw:
        return None

    parts = [x.strip() for x in raw.split("/")]
    route_part = parts[0] if parts else ""
    pickup_time = parts[1] if len(parts) > 1 else ""
    payout = parse_money(parts[2]) if len(parts) > 2 else 0.0
    miles = parse_money(parts[3]) if len(parts) > 3 else 0.0

    if ">" in route_part:
        origin, destination = [x.strip() for x in route_part.split(">", 1)]
    elif " to " in route_part.lower():
        split_match = re.split(r"\bto\b", route_part, maxsplit=1, flags=re.IGNORECASE)
        origin = split_match[0].strip()
        destination = split_match[1].strip() if len(split_match) > 1 else ""
    else:
        origin, destination = route_part.strip(), ""

    calc = score_load_record(origin, destination, pickup_time, payout, miles)

    return {
        "origin": origin,
        "destination": destination,
        "pickup_time": pickup_time,
        "payout": payout,
        "miles": calc["miles"],
        "estimated_profit": calc["estimated_profit"],
        "score": calc["score"],
        "notes": f"RPM: {calc['rpm']}"
    }


# =========================================================
# UI SHELL
# =========================================================
def nav_link(href, label, current_path):
    active = "active" if current_path == href else ""
    return f'<a class="nav-item {active}" href="{href}">{label}</a>'


def shell_page(title, body, extra_head=""):
    user = get_current_user()
    path = request.path

    sidebar = ""
    if user:
        # resolve company name for sidebar display
        _co_name = ""
        if user["company_id"]:
            _co_conn = get_db()
            _co_row = _co_conn.execute(
                "SELECT name, subscription_plan FROM companies WHERE id=?",
                (user["company_id"],)
            ).fetchone()
            _co_conn.close()
            if _co_row:
                _co_name = _co_row["name"]
                _co_plan = _co_row["subscription_plan"].title()

        boss_only = ""
        if user["role"] == "boss":
            boss_only = """
    {boss_panel}
    {orders}
    {users}
    {new_route}
    {text_route}
    {dump_locs}
    {co_settings}
    {subscription}
""".format(
    boss_panel=nav_link(url_for("boss_dashboard"), "📊 Boss Panel", path),
    orders=nav_link(url_for("orders_page"), "🧾 Orders", path),
    users=nav_link(url_for("manage_users"), "👥 Users", path),
    new_route=nav_link(url_for("new_route"), "➕ Create Route", path),
    text_route=nav_link(url_for("text_to_route"), "📝 Text to Route", path),
    dump_locs=nav_link(url_for("dump_locations_page"), "🗑 Dump Locations", path),
    co_settings=nav_link(url_for("company_settings"), "⚙ Company Settings", path),
    subscription=nav_link(url_for("company_subscription"), "💳 Subscription", path),
)

        superadmin_link = nav_link(url_for("superadmin_panel"), "🔧 Superadmin", path) \
            if session.get("is_superadmin") else ""

        co_badge = (f'<div class="muted small" style="margin-bottom:4px;">'
                    f'{e(_co_name)}</div>') if _co_name else ""

        sidebar = f"""
        <aside class="sidebar">
            <div class="logo-card">
                <div class="logo-text">HAULTRA</div>
                <div class="logo-sub">AI SYSTEMS</div>
            </div>
            {co_badge}
            <div class="muted small" style="margin-bottom:14px;">
                Logged in as {e(user['username'] if user else '')} ({e(user['role'] if user else '')})
            </div>
            <nav class="nav-stack">
                {nav_link(url_for('dashboard'), '🏠 Dashboard', path)}
                {nav_link(url_for('driver_dashboard'), '📍 My Routes', path) if user['role'] == 'driver' else ''}
                {nav_link(url_for('routes_page'), '🛻 Routes', path) if user['role'] == 'boss' else ''}
                {nav_link(url_for('drivers_page'), '🚚 Drivers', path) if user['role'] == 'boss' else ''}
                {boss_only}
                {superadmin_link}
                {nav_link(url_for('logout'), '🚪Logout', path)}
            </nav>
        </aside>
        """

    from flask import get_flashed_messages
    flashes = get_flashed_messages(with_categories=True)
    messages_html = "".join(
        f'<div class="flash {e(category)}">{e(msg)}</div>' for category, msg in flashes
    )

    csrf_token = get_csrf_token()

    return f"""
    <!doctype html>
    <html>
   <head>
    <title>{e(title)}</title>
    <meta name="viewport" content="width=device-width, initial-scale=1" />
    <meta name="csrf-token" content="{csrf_token}">

    <link rel="apple-touch-icon" href="/static/logo.png">

    {extra_head}
     <style>
* {{ box-sizing: border-box; }}

html, body {{
    margin: 0;
    padding: 0;
    width: 100%;
    min-height: 100%;
    background: radial-gradient(circle at top, #0f3f86 0%, #0b1733 45%, #08101f 100%);
    overflow-x: hidden;
}}

body {{
    font-family: Arial, Helvetica, sans-serif;
    color: #e5eefc;
}}

/* LINKS */
a {{
    color: #8fd3ff;
    text-decoration: none;
}}

a:hover {{
    text-decoration: underline;
}}

/* APP LAYOUT */
.app-shell {{
    display: flex;
    min-height: 100vh;
    width: 100%;
}}

/* SIDEBAR */
.sidebar {{
    width: 260px;
    padding: 20px 16px;
    background: rgba(7, 18, 40, 0.82);
    border-right: 1px solid rgba(100, 180, 255, 0.18);
    backdrop-filter: blur(10px);
}}
.nav-stack {{
    display: flex;
    flex-direction: column;
    gap: 10px;
}}

.nav-item {{
    display: block;
    width: 100%;
    padding: 14px 16px;
    border-radius: 14px;
    background: linear-gradient(180deg, rgba(12,42,89,0.95), rgba(8,25,55,0.95));
    border: 1px solid rgba(120, 200, 255, 0.25);
    color: #f2f7ff;
    font-weight: 800;
    text-decoration: none;
    transition: all 0.2s ease;
}}

.nav-item:hover {{
    background: linear-gradient(180deg, rgba(20,68,140,0.95), rgba(11,38,80,0.95));
    border-color: rgba(120, 220, 255, 0.45);
    text-decoration: none;
    transform: translateX(3px);
}}

.nav-item.active {{
    background: linear-gradient(90deg, #61f7df, #3fd2ff);
    color: #061223;
    border-color: transparent;
    box-shadow: 0 0 16px rgba(63, 210, 255, 0.22);
}}

/* MAIN CONTENT */
.content {{
    flex: 1;
    padding: 24px;
}}

/* HERO */
.hero {{
    border: 1px solid rgba(120, 200, 255, 0.35);
    border-radius: 18px;
    padding: 24px;
    margin-bottom: 18px;
    background: linear-gradient(180deg, rgba(14,67,142,0.45), rgba(7,18,40,0.75));
    box-shadow: 0 0 18px rgba(76, 209, 255, 0.1);
}}

.hero h1 {{
    margin: 0 0 8px 0;
    font-size: 24px;
    color: #6df7e8;
}}

.hero p {{
    margin: 0;
    color: #dcecff;
}}

/* CARDS */
.card {{
    background: linear-gradient(180deg, rgba(11,42,89,0.72), rgba(7,18,40,0.82));
    border: 1px solid rgba(120, 200, 255, 0.28);
    border-radius: 18px;
    padding: 18px;
    margin-bottom: 16px;
    box-shadow: 0 0 18px rgba(76, 209, 255, 0.08);
}}

.grid {{
    display: grid;
    grid-template-columns: repeat(auto-fit, minmax(210px, 1fr));
    gap: 14px;
}}

.stat {{
    background: rgba(16, 63, 128, 0.35);
    border: 1px solid rgba(124, 214, 255, 0.28);
    border-radius: 16px;
    padding: 16px;
}}

.stat .num {{
    font-size: 30px;
    font-weight: 800;
    margin-top: 6px;
}}

.row {{
    display: flex;
    gap: 12px;
    flex-wrap: wrap;
    align-items: center;
}}

.between {{
    justify-content: space-between;
}}

/* BUTTONS */
.btn, button {{
    display: inline-block;
    border: none;
    cursor: pointer;
    padding: 11px 15px;
    border-radius: 12px;
    font-weight: 800;
    color: #061223;
    background: linear-gradient(90deg, #61f7df, #3fd2ff);
    text-decoration: none;
}}

.btn.secondary {{
    background: linear-gradient(90deg, #6e8dcb, #4d6ab2);
    color: #fff;
}}

.btn.green {{
    background: linear-gradient(90deg, #56f0b7, #17c972);
    color: #062414;
}}

.btn.red {{
    background: linear-gradient(90deg, #ff8a8a, #f25151);
    color: #280808;
}}

.btn.orange {{
    background: linear-gradient(90deg, #ffd27c, #ffae38);
    color: #2b1a00;
}}

form.inline {{
    display: inline;
}}

label {{
    display: block;
    font-weight: 700;
    margin-top: 10px;
    margin-bottom: 5px;
}}

input, textarea, select {{
    width: 100%;
    padding: 12px;
    border-radius: 12px;
    border: 1px solid rgba(133, 211, 255, 0.35);
    background: rgba(5, 16, 33, 0.8);
    color: #f2f7ff;
}}

textarea {{
    min-height: 130px;
    resize: vertical;
}}

table {{
    width: 100%;
    border-collapse: collapse;
}}

th, td {{
    padding: 12px 8px;
    border-bottom: 1px solid rgba(135, 206, 255, 0.15);
    text-align: left;
    vertical-align: top;
}}

.table-wrap {{
    overflow-x: auto;
}}

.badge {{
    display: inline-block;
    padding: 6px 10px;
    border-radius: 999px;
    font-size: 12px;
    font-weight: 800;
}}

.badge.open {{
    background: rgba(56, 130, 246, 0.35);
}}

.badge.in_progress {{
    background: rgba(245, 158, 11, 0.30);
}}

.badge.completed {{
    background: rgba(34, 197, 94, 0.30);
}}

.flash {{
    padding: 12px 14px;
    border-radius: 12px;
    margin-bottom: 12px;
    font-weight: 700;
}}

.flash.success {{
    background: rgba(28, 126, 72, 0.55);
}}

.flash.error {{
    background: rgba(160, 35, 42, 0.65);
}}

.muted {{
    color: #c3d9ee;
}}

.small {{
    font-size: 13px;
}}

.stop-card {{
    background: rgba(6, 22, 46, 0.78);
    border: 1px solid rgba(122, 198, 255, 0.22);
    border-radius: 16px;
    padding: 16px;
    margin-bottom: 12px;
}}

.next-stop-glow {{
    border: 2px solid rgba(97, 247, 223, 0.65);
    box-shadow: 0 0 18px rgba(97, 247, 223, 0.18);
}}

.stop-handle {{
    cursor: grab;
    background: rgba(94, 129, 196, 0.35);
    border-radius: 10px;
    padding: 6px 10px;
    display: inline-block;
    margin-right: 8px;
    font-weight: 700;
}}

.photo-thumb {{
    max-width: 160px;
    max-height: 160px;
    width: 100%;
    object-fit: cover;
    border-radius: 10px;
    border: 1px solid rgba(150,215,255,0.30);
    display: block;
}}

.photo-gallery {{
    display: flex;
    flex-wrap: wrap;
    gap: 10px;
    margin-top: 10px;
}}

.photo-item {{
    display: flex;
    flex-direction: column;
    align-items: center;
    background: rgba(255,255,255,0.05);
    border: 1px solid rgba(150,215,255,0.15);
    border-radius: 10px;
    padding: 8px;
    width: 160px;
}}

.photo-meta {{
    font-size: 11px;
    color: #9dc8f0;
    text-align: center;
    margin-top: 5px;
    line-height: 1.4;
    word-break: break-all;
}}

.photo-pdf-link {{
    display: flex;
    align-items: center;
    justify-content: center;
    width: 140px;
    height: 80px;
    background: rgba(63,210,255,0.10);
    border: 1px solid rgba(63,210,255,0.30);
    border-radius: 8px;
    color: #3fd2ff;
    text-decoration: none;
    font-size: 13px;
    font-weight: 600;
    gap: 6px;
}}

.photo-pdf-link:hover {{
    background: rgba(63,210,255,0.20);
}}

.mini-prog-track {{
    width: 80px;
    height: 8px;
    background: rgba(255,255,255,0.10);
    border-radius: 4px;
    overflow: hidden;
    flex-shrink: 0;
}}

.mini-prog-fill {{
    height: 100%;
    background: linear-gradient(90deg, #3fd2ff, #56f0b7);
    border-radius: 4px;
    transition: width 0.4s;
}}

.inline-reassign {{
    display: flex;
    align-items: center;
    gap: 6px;
    flex-wrap: nowrap;
}}

.compact-select {{
    font-size: 12px;
    padding: 4px 6px;
    border-radius: 6px;
    background: rgba(16,63,128,0.55);
    border: 1px solid rgba(124,214,255,0.28);
    color: #e0f0ff;
    max-width: 130px;
}}

.btn-reassign {{
    font-size: 12px;
    padding: 4px 10px;
    border-radius: 6px;
    background: rgba(56,130,246,0.38);
    border: 1px solid rgba(124,214,255,0.28);
    color: #e0f0ff;
    cursor: pointer;
    white-space: nowrap;
}}

.btn-reassign:hover {{
    background: rgba(56,130,246,0.60);
}}

tr.status-in-progress td {{
    background: rgba(245,158,11,0.06);
}}

.footer-note {{
    text-align: center;
    color: #8aaecb;
    font-size: 12px;
    margin-top: 28px;
    padding: 18px 0 8px;
    border-top: 1px solid rgba(100,160,220,0.12);
    line-height: 1.8;
}}

.footer-note a {{
    color: #3fd2ff;
    text-decoration: none;
    margin: 0 6px;
}}

.footer-note a:hover {{
    text-decoration: underline;
}}

.footer-trust {{
    display: flex;
    justify-content: center;
    gap: 18px;
    flex-wrap: wrap;
    margin-bottom: 8px;
}}

.footer-badge {{
    display: inline-flex;
    align-items: center;
    gap: 5px;
    font-size: 11px;
    color: #6a9bc0;
    background: rgba(255,255,255,0.04);
    border: 1px solid rgba(100,160,220,0.15);
    border-radius: 20px;
    padding: 4px 10px;
}}

@media (max-width: 900px) {{
    .app-shell {{
        flex-direction: column;
    }}

    .sidebar {{
        width: 100%;
        border-right: none;
        border-bottom: 1px solid rgba(100,180,255,0.18);
    }}

    .content {{
        padding: 14px;
    }}
}}

html {{
    background-color: #08101f;
}}
</style>
    </head>
    <body>
        <div class="app-shell">
            {sidebar}
            <main class="content">
                {messages_html}
                {body}
                <div class="footer-note">
                    <div class="footer-trust">
                        <span class="footer-badge">&#128274; SSL Encrypted</span>
                        <span class="footer-badge">&#9989; SOC 2 Ready</span>
                        <span class="footer-badge">&#128100; Role-Based Access</span>
                        <span class="footer-badge">&#127968; US-Based Data</span>
                    </div>
                    <div>
                        <a href="/privacy">Privacy Policy</a>
                        &middot;
                        <a href="/terms">Terms of Service</a>
                        &middot;
                        <a href="mailto:info@haultraai.com">Support</a>
                    </div>
                    <div style="margin-top:4px;">&copy; {datetime.now().year} HAULTRA AI SYSTEMS &mdash; Built for the hauling industry.</div>
                </div>
            </main>
        </div>

                <script>
        // Auto-inject CSRF token into every POST form
        (function() {{
            var csrfToken = document.querySelector('meta[name="csrf-token"]').getAttribute('content');
            document.addEventListener("DOMContentLoaded", function() {{
                document.querySelectorAll("form").forEach(function(form) {{
                    if (form.method.toLowerCase() === "post") {{
                        var input = document.createElement("input");
                        input.type = "hidden";
                        input.name = "_csrf_token";
                        input.value = csrfToken;
                        form.appendChild(input);
                    }}
                }});
            }});
        }})();

        document.addEventListener("DOMContentLoaded", function () {{
            const isIOS =
                /iPad|iPhone|iPod/.test(navigator.userAgent) ||
                (navigator.platform === "MacIntel" && navigator.maxTouchPoints > 1);

            document.querySelectorAll(".map-btn").forEach(function (btn) {{
                const googleUrl = btn.dataset.google;
                const appleUrl = btn.dataset.apple;

                if (isIOS && appleUrl) {{
                    btn.href = appleUrl;
                }} else if (googleUrl) {{
                    btn.href = googleUrl;
                }}
            }});
        const nextStopBtn = document.getElementById("next-stop-btn");
    const nextStopCard = document.getElementById("next-stop-card");

    if (nextStopBtn && nextStopCard) {{
        nextStopBtn.addEventListener("click", function (e) {{
            e.preventDefault();
            nextStopCard.scrollIntoView({{
                behavior: "smooth",
                block: "center"
            }});
        }});
    }}

}});
</script>
        
    </body>
    </html>
    """


# =========================================================
# AUTH PAGES
# =========================================================
@app.route("/init")
@boss_required
def init_route():
    init_db()
    flash("Database re-initialized.", "success")
    return redirect(url_for("dashboard"))


@app.route("/login", methods=["GET", "POST"])
def login():
    init_db()
    if request.method == "POST":
        username = request.form.get("username", "").strip()
        password = request.form.get("password", "").strip()
        conn = get_db()
        user = conn.execute("SELECT * FROM users WHERE username = ?", (username,)).fetchone()
        conn.close()

        if user and check_password_hash(user["password_hash"], password):
            session["user_id"]       = user["id"]
            session["username"]      = user["username"]
            session["role"]          = user["role"]
            session["company_id"]    = user["company_id"]
            session["is_superadmin"] = bool(user["is_superadmin"])
            flash("Logged in.", "success")

            if user["role"] == "driver":
                return redirect(url_for("driver_dashboard"))

            return redirect(url_for("dashboard"))

        flash("Invalid login.", "error")
        return redirect(url_for("login"))

    body = f"""
    <div style="max-width:520px;margin:70px auto;">
        <div class="hero">
            <h1>HAULTRA Login</h1>
            <p>Operations + AI dispatch in one system.</p>
        </div>
        <div class="card">
           
                <form method="POST">
                <label>Username</label>
                <input name="username" required>
                <label>Password</label>
                <input type="password" name="password" required>
                <div style="margin-top:10px;">
                    <button type="submit">Login</button>
                </div>

                <div style="margin-top:14px;" class="small muted">
                Need an account?
                <a href="/signup">Create one here</a>
                </div>

               </form>
        </div>
    </div>
    """
    return render_template_string(shell_page("Login", body))
@app.route("/logout")
def logout():
    session.clear()
    flash("Logged out.", "success")
    return redirect(url_for("login"))

@app.route("/driver")
@driver_required
def driver_dashboard():
    conn = get_db()
    routes = conn.execute("""
        SELECT
            r.*,
            (
                SELECT COUNT(*)
                FROM stops s
                WHERE s.route_id = r.id
            ) AS total_stops,
            (
                SELECT COUNT(*)
                FROM stops s
                WHERE s.route_id = r.id
                  AND s.status = 'completed'
            ) AS completed_stops
        FROM routes r
        WHERE r.assigned_to = ?
        ORDER BY r.route_date DESC, r.id DESC
    """, (session["user_id"],)).fetchall()
    conn.close()

    rows = ""
    for r in routes:
        rows += f"""
        <tr>
            <td>{e(r['route_date'])}</td>
            <td>{e(r['route_name'])}</td>
            <td><span class="badge {e(r['status'])}">{e(r['status'])}</span></td>
            <td>{r['completed_stops']} / {r['total_stops']}</td>
            <td><a class="btn secondary" href="{url_for('driver_route_detail', route_id=r['id'])}">Open</a></td>
        </tr>
        """

    body = f"""
    <div class="hero">
        <h1>Driver Dashboard</h1>
        <p>See your assigned routes, open them fast, and complete stops in the field.</p>
    </div>

    <div class="card">
        <h2>My Assigned Routes</h2>
        <div class="table-wrap">
            <table>
                <thead>
                    <tr>
                        <th>Date</th>
                        <th>Route</th>
                        <th>Status</th>
                        <th>Progress</th>
                        <th></th>
                    </tr>
                </thead>
                <tbody>
                    {rows if rows else '<tr><td colspan="5">No assigned routes.</td></tr>'}
                </tbody>
            </table>
        </div>
    </div>
    """
    return render_template_string(shell_page("Driver Dashboard", body))

# =========================================================
# DASHBOARD / ANALYTICS
# =========================================================
@app.route("/")
def dashboard():
    if "user_id" not in session:
        return redirect(url_for("login"))

    conn = get_db()
    user = get_current_user()

    company_id = cid()
    if user["role"] == "boss":
        routes = conn.execute("""
            SELECT r.*, u.username AS assigned_username
            FROM routes r
            LEFT JOIN users u ON r.assigned_to = u.id
            WHERE r.company_id = ?
            ORDER BY r.route_date DESC, r.id DESC LIMIT 8
        """, (company_id,)).fetchall()
    else:
        routes = conn.execute("""
            SELECT r.*, u.username AS assigned_username
            FROM routes r
            LEFT JOIN users u ON r.assigned_to = u.id
            WHERE r.assigned_to = ? AND r.company_id = ?
            ORDER BY r.route_date DESC, r.id DESC LIMIT 8
        """, (user["id"], company_id)).fetchall()

    if user["role"] == "boss":
        route_total      = conn.execute("SELECT COUNT(*) n FROM routes WHERE company_id=?", (company_id,)).fetchone()["n"]
        open_routes      = conn.execute("SELECT COUNT(*) n FROM routes WHERE company_id=? AND status='open'", (company_id,)).fetchone()["n"]
        progress_routes  = conn.execute("SELECT COUNT(*) n FROM routes WHERE company_id=? AND status='in_progress'", (company_id,)).fetchone()["n"]
        completed_routes = conn.execute("SELECT COUNT(*) n FROM routes WHERE company_id=? AND status='completed'", (company_id,)).fetchone()["n"]
        stop_total       = conn.execute("SELECT COUNT(*) n FROM stops s JOIN routes r ON s.route_id=r.id WHERE r.company_id=?", (company_id,)).fetchone()["n"]
        total_loads      = conn.execute("SELECT COUNT(*) n FROM load_scores WHERE company_id=?", (company_id,)).fetchone()["n"]
    else:
        route_total      = conn.execute("SELECT COUNT(*) n FROM routes WHERE assigned_to=? AND company_id=?", (user["id"], company_id)).fetchone()["n"]
        open_routes      = conn.execute("SELECT COUNT(*) n FROM routes WHERE assigned_to=? AND company_id=? AND status='open'", (user["id"], company_id)).fetchone()["n"]
        progress_routes  = conn.execute("SELECT COUNT(*) n FROM routes WHERE assigned_to=? AND company_id=? AND status='in_progress'", (user["id"], company_id)).fetchone()["n"]
        completed_routes = conn.execute("SELECT COUNT(*) n FROM routes WHERE assigned_to=? AND company_id=? AND status='completed'", (user["id"], company_id)).fetchone()["n"]
        stop_total       = conn.execute("SELECT COUNT(*) n FROM stops s JOIN routes r ON s.route_id=r.id WHERE r.assigned_to=? AND r.company_id=?", (user["id"], company_id)).fetchone()["n"]
        total_loads      = conn.execute("SELECT COUNT(*) n FROM load_scores WHERE created_by=? AND company_id=?", (user["id"], company_id)).fetchone()["n"]

    top_load = conn.execute("SELECT * FROM load_scores WHERE company_id=? ORDER BY score DESC, estimated_profit DESC LIMIT 1", (company_id,)).fetchone()
    conn.close()

    route_rows = ""
    for r in routes:
       route_rows += f"""
<tr>
    <td>{e(r['route_date'])}</td>
    <td><a href="{url_for('view_route', route_id=r['id'])}">{e(r['route_name'])}</a></td>
    <td>{e(r['assigned_username'] or 'Unassigned')}</td>
    <td><span class="badge {e(r['status'])}">{e(r['status'])}</span></td>
    <td>
        <div class="row">
            <a class="btn secondary" href="{url_for('view_route', route_id=r['id'])}">Open</a>
            {f'''
            <form class="inline" method="POST"
                  action="{url_for('delete_route', route_id=r['id'])}"
                  onsubmit="return confirm('Delete this route?')">
                <button class="btn red" type="submit">Delete</button>
            </form>
            ''' if user['role'] == 'boss' else ''}
        </div>
    </td>
</tr>
"""

    top_load_html = "No loads scored yet"
    if top_load:
        top_load_html = f"{e(top_load['origin'])} → {e(top_load['destination'])} | Score {top_load['score']}"

    body = f"""
    <div class="hero">
        <h1>Dispatch Intelligence Dashboard</h1>
        <p>Run operations, track routes, manage drivers, complete stops, and score freight inside one HAULTRA system.</p>
    </div>

    <div class="grid">
        <div class="stat"><div>Total Routes</div><div class="num">{route_total}</div></div>
        <div class="stat"><div>Open Routes</div><div class="num">{open_routes}</div></div>
        <div class="stat"><div>In Progress</div><div class="num">{progress_routes}</div></div>
        <div class="stat"><div>Completed Routes</div><div class="num">{completed_routes}</div></div>
        <div class="stat"><div>Total Stops</div><div class="num">{stop_total}</div></div>
    </div>

    <div class="card">
        <div class="row between">
            <h2 style="margin:0;">Recent Routes</h2>
            <div class="row">
                {f'<a class="btn" href="{url_for("new_route")}">Create Route</a>' if user['role'] == 'boss' else ''}
                </div>
        </div>
        <div class="table-wrap">
            <table>
                <thead>
                    <tr>
                        <th>Date</th>
                        <th>Route</th>
                        <th>Assigned</th>
                        <th>Status</th>
                        <th></th>
                    </tr>
                </thead>
                <tbody>
                    {route_rows if route_rows else '<tr><td colspan="5">No routes yet.</td></tr>'}
                </tbody>
            </table>
        </div>
    </div>
    """
    return render_template_string(shell_page("Dashboard", body))
    

@app.route("/analytics")
@login_required
def analytics_page():
    conn = get_db()
    company_id = cid()
    route_by_status = conn.execute(
        "SELECT status, COUNT(*) AS n FROM routes WHERE company_id=? GROUP BY status",
        (company_id,)
    ).fetchall()
    top_loads = conn.execute(
        "SELECT * FROM load_scores WHERE company_id=? ORDER BY score DESC, estimated_profit DESC LIMIT 10",
        (company_id,)
    ).fetchall()
    top_drivers = conn.execute("""
        SELECT u.username,
               COUNT(DISTINCT r.id) AS routes_handled,
               SUM(CASE WHEN s.status='completed' THEN 1 ELSE 0 END) AS completed_stops
        FROM users u
        LEFT JOIN routes r ON r.assigned_to = u.id AND r.company_id = ?
        LEFT JOIN stops s ON s.route_id = r.id
        WHERE u.role='driver' AND u.company_id = ?
        GROUP BY u.id
        ORDER BY completed_stops DESC, routes_handled DESC, u.username ASC
    """, (company_id, company_id)).fetchall()
    conn.close()

    route_status_html = "".join(
        f'<div class="stat"><div>{e(r["status"]).replace("_", " ").title()}</div><div class="num">{r["n"]}</div></div>'
        for r in route_by_status
    ) or '<div class="stat"><div>No route data yet</div></div>'

    top_load_rows = ""
    for l in top_loads:
        top_load_rows += f"""
        <tr>
            <td>{e(l['origin'])}</td>
            <td>{e(l['destination'])}</td>
            <td>${l['payout']:.2f}</td>
            <td>{l['miles']}</td>
            <td>${l['estimated_profit']:.2f}</td>
            <td>{l['score']}</td>
        </tr>
        """

    driver_rows = ""
    for d in top_drivers:
        driver_rows += f"""
        <tr>
            <td>{e(d['username'])}</td>
            <td>{d['routes_handled'] or 0}</td>
            <td>{d['completed_stops'] or 0}</td>
        </tr>
        """

    body = f"""
    <div class="hero">
        <h1>Analytics</h1>
        <p>Quick view of route flow, driver output, and strongest loads scored inside HAULTRA.</p>
    </div>

    <div class="grid">{route_status_html}</div>

    <div class="card">
        <h2>Top AI-Scored Loads</h2>
        <div class="table-wrap">
            <table>
                <thead><tr><th>Origin</th><th>Destination</th><th>Payout</th><th>Miles</th><th>Profit</th><th>Score</th></tr></thead>
                <tbody>{top_load_rows if top_load_rows else '<tr><td colspan="6">No loads scored yet.</td></tr>'}</tbody>
            </table>
        </div>
    </div>

    <div class="card">
        <h2>Driver Output</h2>
        <div class="table-wrap">
            <table>
                <thead><tr><th>Driver</th><th>Routes Handled</th><th>Completed Stops</th></tr></thead>
                <tbody>{driver_rows if driver_rows else '<tr><td colspan="3">No driver data yet.</td></tr>'}</tbody>
            </table>
        </div>
    </div>
    """
    return render_template_string(shell_page("Analytics", body))


# =========================================================
# USERS / DRIVERS
# =========================================================
@app.route("/users")
@boss_required
def manage_users():
    conn = get_db()
    users = conn.execute(
        "SELECT * FROM users WHERE company_id=? ORDER BY role, username",
        (cid(),)
    ).fetchall()
    conn.close()

    current_uid = session["user_id"]
    boss_count  = sum(1 for u in users if u["role"] == "boss")

    rows = ""
    for u in users:
        is_self      = u["id"] == current_uid
        is_last_boss = u["role"] == "boss" and boss_count <= 1

        _del_td_style = 'style="text-align:right;white-space:nowrap;width:80px;"'
        if is_self:
            delete_cell = f'<td {_del_td_style}><span class="muted small">You</span></td>'
        elif is_last_boss:
            delete_cell = f'<td {_del_td_style}><span class="muted small" title="Cannot delete the last boss">—</span></td>'
        else:
            _del_uname  = e(u["username"])
            _del_action = url_for("delete_user", user_id=u["id"])
            delete_cell = (
                f'<td {_del_td_style}>'
                f'<form method="POST" action="{_del_action}" style="margin:0;" '
                f'onsubmit="return confirm(\'Delete {_del_uname}? This cannot be undone.\');">'
                f'<button type="submit" '
                f'style="background:transparent;color:#f87171;border:1px solid rgba(248,113,113,0.4);'
                f'border-radius:6px;padding:3px 10px;font-size:11px;cursor:pointer;line-height:1.4;">'
                f'Delete</button>'
                f'</form>'
                f'</td>'
            )

        role_badge = (
            '<span class="badge completed">Boss</span>'
            if u["role"] == "boss"
            else '<span class="badge">Driver</span>'
        )

        rows += f"""
        <tr>
            <td>{e(u['username'])}</td>
            <td>{e(u['full_name'] or '')}</td>
            <td>{e(u['phone'] or '')}</td>
            <td>{role_badge}</td>
            <td>{e(u['created_at'])}</td>
            {delete_cell}
        </tr>
        """

    body = f"""
    <div class="hero">
        <h1>Users</h1>
        <p>Create drivers and bosses that can work inside the same HAULTRA system.</p>
    </div>

    <div class="card">
        <div class="row between">
            <h2 style="margin:0;">All Users</h2>
            <a class="btn" href="{url_for('register')}">Create User</a>
        </div>
        <div class="table-wrap">
            <table>
                <thead><tr><th>Username</th><th>Full Name</th><th>Phone</th><th>Role</th><th>Created</th><th style="width:80px;"></th></tr></thead>
                <tbody>{rows}</tbody>
            </table>
        </div>
    </div>
    """
    return render_template_string(shell_page("Users", body))


@app.route("/users/<int:user_id>/delete", methods=["POST"])
@boss_required
def delete_user(user_id):
    conn = get_db()

    # Verify the target user belongs to this company
    target = conn.execute(
        "SELECT * FROM users WHERE id=? AND company_id=?", (user_id, cid())
    ).fetchone()
    if not target:
        conn.close()
        flash("User not found.", "error")
        return redirect(url_for("manage_users"))

    # Cannot delete yourself
    if user_id == session["user_id"]:
        conn.close()
        flash("You cannot delete your own account.", "error")
        return redirect(url_for("manage_users"))

    # Cannot delete the last boss
    if target["role"] == "boss":
        boss_count = conn.execute(
            "SELECT COUNT(*) n FROM users WHERE role='boss' AND company_id=?", (cid(),)
        ).fetchone()["n"]
        if boss_count <= 1:
            conn.close()
            flash("Cannot delete the last boss account.", "error")
            return redirect(url_for("manage_users"))

    # If deleting a driver: unassign their active routes (set assigned_to = NULL)
    if target["role"] == "driver":
        conn.execute(
            "UPDATE routes SET assigned_to=NULL WHERE assigned_to=? AND company_id=?",
            (user_id, cid())
        )

    conn.execute("DELETE FROM users WHERE id=? AND company_id=?", (user_id, cid()))
    conn.commit()
    conn.close()

    flash(f"User '{target['username']}' has been deleted.", "success")
    return redirect(url_for("manage_users"))


@app.route("/drivers")
@boss_required
def drivers_page():
    conn = get_db()
    drivers = conn.execute("""
        SELECT u.*, COUNT(DISTINCT r.id) AS routes_assigned,
               SUM(CASE WHEN s.status='completed' THEN 1 ELSE 0 END) AS completed_stops
        FROM users u
        LEFT JOIN routes r ON r.assigned_to = u.id AND r.company_id = ?
        LEFT JOIN stops s ON s.route_id = r.id
        WHERE u.role='driver' AND u.company_id = ?
        GROUP BY u.id
        ORDER BY u.username
    """, (cid(), cid())).fetchall()
    conn.close()

    cards = ""
    for d in drivers:
        cards += f"""
        <div class="stat">
            <div style="font-size:18px;font-weight:800;">{e(d['username'])}</div>
            <div class="small muted">{e(d['full_name'] or '')}</div>
            <div class="small muted">{e(d['phone'] or '')}</div>
            <div style="margin-top:10px;">Routes Assigned: <b>{d['routes_assigned'] or 0}</b></div>
            <div>Completed Stops: <b>{d['completed_stops'] or 0}</b></div>
        </div>
        """

    body = f"""
    <div class="hero">
        <h1>Drivers</h1>
        <p>See active drivers, route assignments, and stop completion totals.</p>
    </div>
    <div class="grid">{cards if cards else '<div class="stat">No drivers found.</div>'}</div>
    """
    return render_template_string(shell_page("Drivers", body))

@app.route("/signup")
def signup():
    """Legacy signup URL — redirect to company registration."""
    return redirect(url_for("company_register"))

@app.route("/order", methods=["GET", "POST"])
def public_order_form():
    init_db()

    if request.method == "POST":
        customer_name = request.form.get("customer_name", "").strip()
        phone = request.form.get("phone", "").strip()
        email = request.form.get("email", "").strip()
        address = request.form.get("address", "").strip()
        city = request.form.get("city", "").strip()
        state = request.form.get("state", "").strip()
        zip_code = request.form.get("zip_code", "").strip()
        service_type = request.form.get("service_type", "").strip()
        container_size = request.form.get("container_size", "").strip()
        requested_date = request.form.get("requested_date", "").strip()
        notes = request.form.get("notes", "").strip()

        if not customer_name or not address or not service_type:
            flash("Customer name, address, and service type are required.", "error")
            return redirect(url_for("public_order_form"))

        conn = get_db()
        # resolve company from ?company=slug or fall back to first company
        slug = request.args.get("company", "").strip()
        if slug:
            co_row = conn.execute("SELECT id FROM companies WHERE slug=?", (slug,)).fetchone()
        else:
            co_row = conn.execute("SELECT id FROM companies LIMIT 1").fetchone()
        form_company_id = co_row["id"] if co_row else None

        conn.execute("""
            INSERT INTO orders (
                customer_name, phone, email, address, city, state, zip_code,
                service_type, container_size, notes, requested_date, status, company_id, created_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'new', ?, ?)
        """, (
            customer_name, phone, email, address, city, state, zip_code,
            service_type, container_size, notes, requested_date, form_company_id, now_ts()
        ))
        conn.commit()
        conn.close()

        flash("Your dumpster request has been submitted.", "success")
        return redirect(url_for("public_order_form"))

    body = f"""
    <div style="max-width:760px;margin:0 auto;">
        <div class="hero">
            <h1>Request Dumpster Service</h1>
            <p>Book a drop-off, pickup, or swap from your phone in minutes.</p>
        </div>

        <div class="card">
            <form method="POST">
                <div class="grid">
                    <div>
                        <label>Customer Name</label>
                        <input name="customer_name" required>
                    </div>
                    <div>
                        <label>Phone</label>
                        <input name="phone">
                    </div>
                    <div>
                        <label>Email</label>
                        <input name="email" type="email">
                    </div>
                    <div>
                        <label>Requested Date</label>
                        <input name="requested_date" type="date" value="{today_str()}">
                    </div>
                </div>

                <label>Address</label>
                <input name="address" required>

                <div class="grid">
                    <div>
                        <label>City</label>
                        <input name="city">
                    </div>
                    <div>
                        <label>State</label>
                        <input name="state" maxlength="2">
                    </div>
                    <div>
                        <label>ZIP Code</label>
                        <input name="zip_code">
                    </div>
                </div>

                <div class="grid">
                    <div>
                        <label>Service Type</label>
                        <select name="service_type" required>
                            <option value="Drop">Drop</option>
                            <option value="Pickup">Pickup</option>
                            <option value="Swap">Swap</option>
                            <option value="Dump">Dump</option>
                            <option value="Service">Service</option>
                        </select>
                    </div>
                    <div>
                        <label>Container Size</label>
                        <select name="container_size">
                            <option value="">Select</option>
                            <option value="10">10 yd</option>
                            <option value="12">12 yd</option>
                            <option value="15">15 yd</option>
                            <option value="20">20 yd</option>
                            <option value="30">30 yd</option>
                            <option value="40">40 yd</option>
                        </select>
                    </div>
                </div>

                <label>Notes</label>
                <textarea name="notes" placeholder="Gate code, placement instructions, material type, callback notes, etc."></textarea>

                <div style="margin-top:14px;">
                    <button type="submit">Submit Order</button>
                </div>
            </form>
        </div>
    </div>
    """
    return render_template_string(shell_page("Request Dumpster Service", body))

@app.route("/register", methods=["GET", "POST"])
@boss_required
def register():
    if request.method == "POST":
        username  = request.form.get("username", "").strip()
        password  = request.form.get("password", "").strip()
        role      = request.form.get("role", "").strip()
        full_name = request.form.get("full_name", "").strip()
        phone     = request.form.get("phone", "").strip()

        if not username or not password or role not in ("boss", "driver"):
            flash("Fill everything correctly.", "error")
            return redirect(url_for("register"))

        company_id = cid()
        conn = get_db()

        # enforce driver seat limit from subscription plan
        if role == "driver":
            co = conn.execute("SELECT max_drivers FROM companies WHERE id=?", (company_id,)).fetchone()
            if co:
                current_drivers = conn.execute(
                    "SELECT COUNT(*) n FROM users WHERE role='driver' AND company_id=?",
                    (company_id,)
                ).fetchone()["n"]
                if current_drivers >= co["max_drivers"]:
                    conn.close()
                    flash(f"Driver limit reached ({co['max_drivers']}). Upgrade your plan to add more.", "error")
                    return redirect(url_for("register"))

        try:
            conn.execute(
                """INSERT INTO users (username, password_hash, role, full_name, phone,
                   company_id, created_at) VALUES (?, ?, ?, ?, ?, ?, ?)""",
                (username, generate_password_hash(password), role,
                 full_name, phone, company_id, now_ts())
            )
            conn.commit()
            flash("User created.", "success")
        except sqlite3.IntegrityError:
            flash("Username already exists.", "error")
        finally:
            conn.close()
        return redirect(url_for("manage_users"))

    body = """
    <div class="hero">
        <h1>Create User</h1>
        <p>Add drivers and boss accounts to HAULTRA.</p>
    </div>
    <div class="card">
        <form method="POST">
            <label>Username</label>
            <input name="username" required>
            <label>Password</label>
            <input type="password" name="password" required>
            <label>Full Name</label>
            <input name="full_name">
            <label>Phone</label>
            <input name="phone">
            <label>Role</label>
            <select name="role" required>
                <option value="driver">Driver</option>
                <option value="boss">Boss</option>
            </select>
            <div style="margin-top:10px;"><button type="submit">Create User</button></div>
        </form>
    </div>
    """
    return render_template_string(shell_page("Create User", body))


# =========================================================
# BOSS DASHBOARD
# =========================================================

@app.route("/orders")
@boss_required
def orders_page():
    conn = get_db()
    company_id = cid()
    drivers = conn.execute(
        "SELECT id, username FROM users WHERE role='driver' AND company_id=? ORDER BY username",
        (company_id,)
    ).fetchall()

    orders = conn.execute("""
        SELECT *
        FROM orders
        WHERE company_id = ?
        ORDER BY
            CASE status
                WHEN 'new' THEN 0
                WHEN 'converted' THEN 1
                WHEN 'closed' THEN 2
                ELSE 3
            END,
            id DESC
    """, (company_id,)).fetchall()
    conn.close()

    driver_options = '<option value="">Unassigned</option>'
    for d in drivers:
        driver_options += f'<option value="{d["id"]}">{e(d["username"])}</option>'

    rows = ""
    for o in orders:
        create_route_btn = ""
        close_btn = ""

        if o["status"] == "new":
            create_route_btn = f"""
            <form method="GET" action="{url_for('convert_order_to_route', order_id=o['id'])}">
                <select name="assigned_to" style="min-width:140px;">
                    {driver_options}
                </select>
                <button type="submit" class="btn green">Create Route</button>
            </form>
            """

        if o["status"] != "closed":
            close_btn = f"""
            <form method="POST"
                  action="{url_for('close_order', order_id=o['id'])}"
                  class="inline">
                <button class="btn orange" type="submit">Close</button>
            </form>
            """

        delete_btn = f"""
        <form method="POST"
              action="{url_for('delete_order', order_id=o['id'])}"
              class="inline"
              onsubmit="return confirm('Delete this order?')">
            <button class="btn red" type="submit">Delete</button>
        </form>
        """

        rows += f"""
        <tr>
            <td>{e(o['customer_name'])}</td>
            <td>{e(o['service_type'])}</td>
            <td>{e(o['container_size'] or '')}</td>
            <td>{e(o['address'])}</td>
            <td>{e(o['requested_date'] or '')}</td>
            <td><span class="badge {e(o['status'])}">{e(o['status'])}</span></td>
            <td>
                <div class="row">
                    {create_route_btn}
                    {close_btn}
                    {delete_btn}
                </div>
            </td>
        </tr>
        """

    body = f"""
    <div class="hero">
        <h1>Customer Orders</h1>
        <p>Review customer dumpster requests and convert them into live routes.</p>
    </div>

    <div class="card">
        <div class="row between">
            <h2 style="margin:0;">Incoming Orders</h2>
            <a class="btn secondary" href="{url_for('public_order_form')}">Open Public Form</a>
        </div>

        <div class="table-wrap">
            <table>
                <thead>
                    <tr>
                        <th>Customer</th>
                        <th>Service</th>
                        <th>Size</th>
                        <th>Address</th>
                        <th>Requested</th>
                        <th>Status</th>
                        <th></th>
                    </tr>
                </thead>
                <tbody>
                    {rows if rows else '<tr><td colspan="7">No orders yet.</td></tr>'}
                </tbody>
            </table>
        </div>
    </div>
    """
    return render_template_string(shell_page("Orders", body))

def build_order_raw_text(order_row):
    parts = []
    if order_row["customer_name"]:
        parts.append(f"1. {order_row['customer_name']}")
    if order_row["address"]:
        parts.append(order_row["address"])
    csz = " ".join(filter(None, [
        order_row["city"] if order_row["city"] else "",
        order_row["state"] if order_row["state"] else "",
        order_row["zip_code"] if order_row["zip_code"] else "",
    ])).strip()
    if csz:
        parts.append(csz)
    if order_row["service_type"]:
        parts.append(order_row["service_type"])
    if order_row["container_size"]:
        parts.append(f"{order_row['container_size']} yd")
    if order_row["notes"]:
        parts.append(order_row["notes"])
    return "\n".join(parts)


@app.route("/order/<int:order_id>/convert")
@boss_required
def convert_order_to_route(order_id):
    conn = get_db()
    assigned_to_raw = request.args.get("assigned_to", "").strip()
    assigned_to = int(assigned_to_raw) if assigned_to_raw.isdigit() else None
    order_row = conn.execute(
        "SELECT * FROM orders WHERE id = ? AND company_id = ?",
        (order_id, cid())
    ).fetchone()

    if not order_row:
        conn.close()
        flash("Order not found.", "error")
        return redirect(url_for("orders_page"))

    if order_row["status"] != "new":
        conn.close()
        flash("Order already converted or closed.", "error")
        return redirect(url_for("orders_page"))

    route_date = order_row["requested_date"] or today_str()
    route_name = f"{order_row['service_type']} - {order_row['customer_name']}"
    raw_text = build_order_raw_text(order_row)

    cur = conn.cursor()
    cur.execute("""
        INSERT INTO routes (
            route_date, route_name, raw_text, assigned_to, created_by,
            status, notes, company_id, created_at
        ) VALUES (?, ?, ?, ?, ?, 'open', ?, ?, ?)
    """, (
        route_date,
        route_name,
        raw_text,
        assigned_to,
        session["user_id"],
        f"Created from customer order #{order_row['id']}",
        cid(),
        now_ts()
    ))
    route_id = cur.lastrowid

    parsed_stops = parse_boss_text(raw_text)
    for stop in parsed_stops:
        cur.execute("""
            INSERT INTO stops (
                route_id, stop_order, customer_name, address, city, state, zip_code,
                action, container_size, ticket_number, reference_number, notes,
                status, created_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'open', ?)
        """, (
            route_id,
            stop["stop_order"],
            stop["customer_name"],
            stop["address"],
            stop["city"],
            stop["state"],
            stop["zip_code"],
            stop["action"],
            stop["container_size"],
            stop["ticket_number"],
            stop["reference_number"],
            stop["notes"],
            now_ts()
        ))

    cur.execute("UPDATE orders SET status = 'converted' WHERE id = ?", (order_id,))
    conn.commit()
    conn.close()

    flash("Order converted into a route.", "success")
    return redirect(url_for("view_route", route_id=route_id))

@app.route("/boss")
@boss_required
def boss_dashboard():
    conn = get_db()

    company_id = cid()

    # --- summary counts ---
    total_routes    = conn.execute("SELECT COUNT(*) AS n FROM routes WHERE company_id=?", (company_id,)).fetchone()["n"]
    open_routes     = conn.execute("SELECT COUNT(*) AS n FROM routes WHERE company_id=? AND status='open'", (company_id,)).fetchone()["n"]
    progress_routes = conn.execute("SELECT COUNT(*) AS n FROM routes WHERE company_id=? AND status='in_progress'", (company_id,)).fetchone()["n"]
    completed_routes= conn.execute("SELECT COUNT(*) AS n FROM routes WHERE company_id=? AND status='completed'", (company_id,)).fetchone()["n"]
    total_stops     = conn.execute("SELECT COUNT(*) AS n FROM stops s JOIN routes r ON s.route_id=r.id WHERE r.company_id=?", (company_id,)).fetchone()["n"]
    completed_stops = conn.execute("SELECT COUNT(*) AS n FROM stops s JOIN routes r ON s.route_id=r.id WHERE r.company_id=? AND s.status='completed'", (company_id,)).fetchone()["n"]
    drivers_count   = conn.execute("SELECT COUNT(*) AS n FROM users WHERE role='driver' AND company_id=?", (company_id,)).fetchone()["n"]
    new_orders      = conn.execute("SELECT COUNT(*) AS n FROM orders WHERE status='new' AND company_id=?", (company_id,)).fetchone()["n"]

    # --- active routes (open + in_progress) with per-route stop progress ---
    active_routes = conn.execute("""
        SELECT r.id, r.route_name, r.route_date, r.status, r.assigned_to,
               COALESCE(u.username, 'Unassigned') AS assigned_username,
               COUNT(s.id) AS total_stops,
               SUM(CASE WHEN s.status='completed' THEN 1 ELSE 0 END) AS done_stops
        FROM routes r
        LEFT JOIN users u ON r.assigned_to = u.id
        LEFT JOIN stops s ON s.route_id = r.id
        WHERE r.status IN ('open', 'in_progress') AND r.company_id = ?
        GROUP BY r.id
        ORDER BY CASE r.status WHEN 'in_progress' THEN 0 ELSE 1 END,
                 r.route_date DESC, r.id DESC
    """, (company_id,)).fetchall()

    # --- recently completed routes (capped at 25) ---
    recent_completed = conn.execute("""
        SELECT r.id, r.route_name, r.route_date, r.status, r.assigned_to,
               COALESCE(u.username, 'Unassigned') AS assigned_username,
               COUNT(s.id) AS total_stops,
               SUM(CASE WHEN s.status='completed' THEN 1 ELSE 0 END) AS done_stops
        FROM routes r
        LEFT JOIN users u ON r.assigned_to = u.id
        LEFT JOIN stops s ON s.route_id = r.id
        WHERE r.status = 'completed' AND r.company_id = ?
        GROUP BY r.id
        ORDER BY r.route_date DESC, r.id DESC
        LIMIT 25
    """, (company_id,)).fetchall()

    # --- driver performance ---
    driver_stats = conn.execute("""
        SELECT u.id, u.username,
               COUNT(DISTINCT r.id) AS route_count,
               COUNT(s.id) AS stop_count,
               SUM(CASE WHEN s.status='completed' THEN 1 ELSE 0 END) AS completed_stop_count,
               SUM(CASE WHEN r.status='in_progress' THEN 1 ELSE 0 END) AS active_routes
        FROM users u
        LEFT JOIN routes r ON r.assigned_to = u.id AND r.company_id = ?
        LEFT JOIN stops s ON s.route_id = r.id
        WHERE u.role = 'driver' AND u.company_id = ?
        GROUP BY u.id
        ORDER BY u.username
    """, (company_id, company_id)).fetchall()

    # --- all drivers for reassign dropdowns ---
    all_drivers = conn.execute(
        "SELECT id, username FROM users WHERE role='driver' AND company_id=? ORDER BY username",
        (company_id,)
    ).fetchall()

    conn.close()

    # --- build driver options string (reused per route row) ---
    def driver_opts(current_id):
        opts = '<option value="">Unassigned</option>'
        for d in all_drivers:
            sel = " selected" if d["id"] == current_id else ""
            opts += f'<option value="{d["id"]}"{sel}>{e(d["username"])}</option>'
        return opts

    # --- route row builder ---
    def route_row(r, show_reassign=True):
        total = r["total_stops"] or 0
        done  = r["done_stops"] or 0
        pct   = int(done / total * 100) if total else 0
        status_label = e(r["status"].replace("_", " ").title())
        row_class = "status-in-progress" if r["status"] == "in_progress" else ""
        progress_cell = f"""
            <div style="display:flex;align-items:center;gap:8px;">
                <div class="mini-prog-track"><div class="mini-prog-fill" style="width:{pct}%"></div></div>
                <span style="font-size:12px;color:#9dc8f0;">{done}/{total}</span>
            </div>"""
        reassign_cell = ""
        if show_reassign:
            reassign_cell = f"""
            <form class="inline-reassign" method="POST"
                  action="{url_for('reassign_route', route_id=r['id'])}">
                <select name="driver_id" class="compact-select">
                    {driver_opts(r['assigned_to'])}
                </select>
                <button class="btn-reassign" type="submit">Save</button>
            </form>"""
        return f"""
        <tr class="{row_class}">
            <td><a href="{url_for('view_route', route_id=r['id'])}">{e(r['route_name'])}</a></td>
            <td style="white-space:nowrap;">{e(r['route_date'] or '')}</td>
            <td><span class="badge {e(r['status'])}">{status_label}</span></td>
            <td>{e(r['assigned_username'])}</td>
            <td>{progress_cell}</td>
            <td>{reassign_cell}</td>
        </tr>"""

    active_rows   = "".join(route_row(r) for r in active_routes) or \
        '<tr><td colspan="6" style="text-align:center;color:#9dc8f0;">No active routes.</td></tr>'
    completed_rows= "".join(route_row(r, show_reassign=False) for r in recent_completed) or \
        '<tr><td colspan="6" style="text-align:center;color:#9dc8f0;">None yet.</td></tr>'

    route_thead = """<thead><tr>
        <th>Route</th><th>Date</th><th>Status</th>
        <th>Driver</th><th>Progress</th><th>Reassign</th>
    </tr></thead>"""
    completed_thead = """<thead><tr>
        <th>Route</th><th>Date</th><th>Status</th>
        <th>Driver</th><th>Progress</th><th></th>
    </tr></thead>"""

    driver_rows = ""
    for d in driver_stats:
        s_total = d["stop_count"] or 0
        s_done  = d["completed_stop_count"] or 0
        pct     = int(s_done / s_total * 100) if s_total else 0
        active_badge = (f'<span class="badge in_progress" style="font-size:11px;">'
                        f'{d["active_routes"] or 0} active</span>') if (d["active_routes"] or 0) > 0 else ""
        driver_rows += f"""
        <tr>
            <td>{e(d['username'])} {active_badge}</td>
            <td>{d['route_count'] or 0}</td>
            <td>
                <div style="display:flex;align-items:center;gap:8px;">
                    <div class="mini-prog-track"><div class="mini-prog-fill" style="width:{pct}%"></div></div>
                    <span style="font-size:12px;color:#9dc8f0;">{s_done}/{s_total}</span>
                </div>
            </td>
        </tr>"""

    body = f"""
    <div class="hero">
        <h1>Boss Panel</h1>
        <p>Live overview of all routes, driver progress, and assignments.</p>
    </div>

    <div class="grid">
        <div class="stat"><div>Total Routes</div><div class="num">{total_routes}</div></div>
        <div class="stat"><div>Open</div><div class="num">{open_routes}</div></div>
        <div class="stat" style="border-color:rgba(245,158,11,0.45);">
            <div>In Progress</div><div class="num" style="color:#fbbf24;">{progress_routes}</div>
        </div>
        <div class="stat" style="border-color:rgba(34,197,94,0.35);">
            <div>Completed</div><div class="num" style="color:#4ade80;">{completed_routes}</div>
        </div>
        <div class="stat"><div>Total Stops</div><div class="num">{total_stops}</div></div>
        <div class="stat" style="border-color:rgba(34,197,94,0.35);">
            <div>Stops Done</div><div class="num" style="color:#4ade80;">{completed_stops}</div>
        </div>
        <div class="stat"><div>Drivers</div><div class="num">{drivers_count}</div></div>
        <div class="stat"><div>New Orders</div><div class="num">{new_orders}</div></div>
    </div>

    <div class="card">
        <h2>&#128338; Active Routes</h2>
        <div class="table-wrap">
            <table>
                {route_thead}
                <tbody>{active_rows}</tbody>
            </table>
        </div>
    </div>

    <div class="card">
        <h2>&#10003; Recently Completed</h2>
        <div class="table-wrap">
            <table>
                {completed_thead}
                <tbody>{completed_rows}</tbody>
            </table>
        </div>
    </div>

    <div class="card">
        <h2>&#128100; Driver Performance</h2>
        <div class="table-wrap">
            <table>
                <thead><tr><th>Driver</th><th>Routes</th><th>Stops Progress</th></tr></thead>
                <tbody>{driver_rows if driver_rows else '<tr><td colspan="3">No drivers.</td></tr>'}</tbody>
            </table>
        </div>
    </div>
    """
    return render_template_string(shell_page("Boss Panel", body))

# =========================================================
# REASSIGN ROUTE
# =========================================================
@app.route("/route/<int:route_id>/reassign", methods=["POST"])
@boss_required
def reassign_route(route_id):
    driver_id_raw = request.form.get("driver_id", "").strip()
    driver_id = int(driver_id_raw) if driver_id_raw.isdigit() else None

    conn = get_db()
    route = conn.execute(
        "SELECT id FROM routes WHERE id=? AND company_id=?", (route_id, cid())
    ).fetchone()
    if not route:
        conn.close()
        abort(404)

    if driver_id is not None:
        driver = conn.execute(
            "SELECT id FROM users WHERE id=? AND role='driver' AND company_id=?",
            (driver_id, cid())
        ).fetchone()
        if not driver:
            conn.close()
            flash("Driver not found.", "error")
            return redirect(url_for("boss_dashboard"))

    conn.execute("UPDATE routes SET assigned_to=? WHERE id=? AND company_id=?",
                 (driver_id, route_id, cid()))
    conn.commit()
    conn.close()
    flash("Route reassigned.", "success")
    return redirect(url_for("boss_dashboard"))


# =========================================
# TEXT TO ROUTE
# =========================================

@app.route("/text-to-route", methods=["GET", "POST"])
@boss_required
def text_to_route():
    conn = get_db()
    company_id = cid()
    drivers = conn.execute(
        "SELECT id, username FROM users WHERE role='driver' AND company_id=? ORDER BY username",
        (company_id,)
    ).fetchall()

    if request.method == "POST":
        route_date = request.form.get("route_date", "").strip() or today_str()
        route_name = request.form.get("route_name", "").strip()
        raw_text = request.form.get("raw_text", "").strip()
        assigned_to_raw = request.form.get("assigned_to", "").strip()
        notes = request.form.get("notes", "").strip()

        assigned_to = int(assigned_to_raw) if assigned_to_raw.isdigit() else None

        if not route_name or not raw_text:
            conn.close()
            flash("Route name and pasted text are required.", "error")
            return redirect(url_for("text_to_route"))

        parsed_stops = parse_boss_text(raw_text)

        if not parsed_stops:
            conn.close()
            flash("No stops could be parsed.", "error")
            return redirect(url_for("text_to_route"))

        cur = conn.cursor()
        cur.execute("""
            INSERT INTO routes (
                route_date, route_name, raw_text, assigned_to, created_by,
                status, notes, company_id, created_at
            ) VALUES (?, ?, ?, ?, ?, 'open', ?, ?, ?)
        """, (
            route_date,
            route_name,
            raw_text,
            assigned_to,
            session["user_id"],
            notes,
            company_id,
            now_ts()
        ))

        route_id = cur.lastrowid

        for stop in parsed_stops:
            cur.execute("""
                INSERT INTO stops (
                    route_id, stop_order, customer_name, address, city, state, zip_code,
                    action, container_size, ticket_number, reference_number, notes,
                    status, created_at
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'open', ?)
            """, (
                route_id,
                stop["stop_order"],
                stop["customer_name"],
                stop["address"],
                stop["city"],
                stop["state"],
                stop["zip_code"],
                stop["action"],
                stop["container_size"],
                stop["ticket_number"],
                stop["reference_number"],
                stop["notes"],
                now_ts()
            ))

        conn.commit()
        conn.close()

        flash(f"Route created with {len(parsed_stops)} stops.", "success")
        return redirect(url_for("view_route", route_id=route_id))

    driver_options = '<option value="">Unassigned</option>'
    for d in drivers:
        driver_options += f'<option value="{d["id"]}">{e(d["username"])}</option>'

    conn.close()

    body = f"""
    <div class="hero">
        <h1>Text to Route</h1>
        <p>Paste dispatch text and convert it instantly.</p>
    </div>

    <div class="card">
        <form method="POST">
            <input name="route_name" placeholder="Route Name" required>
            <select name="assigned_to">
                {driver_options}
            </select>
            <textarea name="raw_text" placeholder="Paste boss text here..." required></textarea>
            <button type="submit" class="btn green">Create Route</button>
        </form>
    </div>
    """
    return render_template_string(shell_page("Text to Route", body))

# =========================================================
# ROUTES / STOPS
# =========================================================
@app.route("/routes")
@login_required
def routes_page():
    user = get_current_user()
    conn = get_db()
    q = request.args.get("q", "").strip()
    status = request.args.get("status", "").strip()

    params = [cid()]
    sql = """
        SELECT r.*, u.username AS assigned_username, c.username AS created_username
        FROM routes r
        LEFT JOIN users u ON r.assigned_to = u.id
        LEFT JOIN users c ON r.created_by = c.id
        WHERE r.company_id = ?
    """

    if user["role"] != "boss":
        sql += " AND r.assigned_to = ?"
        params.append(user["id"])

    if q:
        sql += " AND (r.route_name LIKE ? OR r.notes LIKE ? OR r.raw_text LIKE ?)"
        like_q = f"%{q}%"
        params.extend([like_q, like_q, like_q])

    if status in ("open", "in_progress", "completed"):
        sql += " AND r.status = ?"
        params.append(status)

    sql += " ORDER BY r.route_date DESC, r.id DESC"

    routes = conn.execute(sql, tuple(params)).fetchall()
    conn.close()

    rows = ""
    for r in routes:
        rows += f"""
        <tr>
            <td>{e(r['route_date'])}</td>
            <td><a href="{url_for('view_route', route_id=r['id'])}">{e(r['route_name'])}</a></td>
            <td>{e(r['assigned_username'] or 'Unassigned')}</td>
            <td>{e(r['created_username'] or '')}</td>
            <td><span class="badge {e(r['status'])}">{e(r['status'])}</span></td>
            <td>
                <div class="row">
                  <td>
    <div class="row">
        <a class="btn secondary" href="{url_for('view_route', route_id=r['id'])}">Open</a>
        <a class="btn green" href="{url_for('export_route_csv', route_id=r['id'])}">CSV</a>

        {f'''
        <form class="inline" method="POST"
              action="{url_for('delete_route', route_id=r['id'])}"
              onsubmit="return confirm('Delete this entire route?')">
            <button class="btn red" type="submit">Delete</button>
        </form>
        ''' if user['role'] == 'boss' else ''}

    </div>
</td>
                </div>
            </td>
        </tr>
        """

    body = f"""
    <div class="hero">
        <h1>Routes</h1>
        <p>Search, filter, open, export, and manage route flow.</p>
    </div>
    <div class="card">
        <form method="GET" class="row">
            <div style="flex:1;min-width:220px;">
                <label>Search</label>
                <input name="q" value="{e(q)}" placeholder="Route name, notes, or pasted route text">
            </div>
            <div style="min-width:180px;">
                <label>Status</label>
                <select name="status">
                    <option value="">All</option>
                    <option value="open" {'selected' if status=='open' else ''}>Open</option>
                    <option value="in_progress" {'selected' if status=='in_progress' else ''}>In Progress</option>
                    <option value="completed" {'selected' if status=='completed' else ''}>Completed</option>
                </select>
            </div>
            <div style="align-self:flex-end;">
                <button type="submit">Filter</button>
            </div>
        </form>
    </div>
    <div class="card">
        <div class="row between">
            <h2 style="margin:0;">All Routes</h2>
            {f'<a class="btn" href="{url_for("new_route")}">Create Route</a>' if user['role']=='boss' else ''}
        </div>
        <div class="table-wrap">
            <table>
                <thead><tr><th>Date</th><th>Route</th><th>Assigned</th><th>Created By</th><th>Status</th><th>Actions</th></tr></thead>
                <tbody>{rows if rows else '<tr><td colspan="6">No routes found.</td></tr>'}</tbody>
            </table>
        </div>
    </div>
    """
    return render_template_string(shell_page("Routes", body))


@app.route("/route/new", methods=["GET", "POST"])
@boss_required
def new_route():
    conn = get_db()
    drivers = conn.execute(
        "SELECT id, username FROM users WHERE role='driver' AND company_id=? ORDER BY username",
        (cid(),)
    ).fetchall()
    dump_locs = conn.execute(
        "SELECT id, name, city FROM dump_locations WHERE active=1 ORDER BY name"
    ).fetchall()

    if request.method == "POST":
        route_name       = request.form.get("route_name", "").strip()
        route_date       = request.form.get("route_date", today_str()).strip()
        assigned_to      = request.form.get("assigned_to", "").strip()
        raw_text         = request.form.get("raw_text", "").strip()
        notes            = request.form.get("notes", "").strip()
        dump_location_id = request.form.get("dump_location_id", "").strip()

        if not route_name:
            flash("Route name required.", "error")
            conn.close()
            return redirect(url_for("new_route"))

        assigned_to_val    = int(assigned_to) if assigned_to.isdigit() else None
        dump_location_val  = int(dump_location_id) if dump_location_id.isdigit() else None
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO routes (route_date, route_name, raw_text, assigned_to, created_by,
                                status, notes, dump_location_id, company_id, created_at)
            VALUES (?, ?, ?, ?, ?, 'open', ?, ?, ?, ?)
        """, (route_date, route_name, raw_text, assigned_to_val, session["user_id"],
              notes, dump_location_val, cid(), now_ts()))
        route_id = cur.lastrowid

        parsed_stops = parse_boss_text(raw_text)
        for stop in parsed_stops:
            cur.execute("""
                INSERT INTO stops (
                    route_id, stop_order, customer_name, address, city, state, zip_code,
                    action, container_size, ticket_number, reference_number, notes,
                    status, created_at
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'open', ?)
            """, (
                route_id,
                stop["stop_order"],
                stop["customer_name"],
                stop["address"],
                stop["city"],
                stop["state"],
                stop["zip_code"],
                stop["action"],
                stop["container_size"],
                stop["ticket_number"],
                stop["reference_number"],
                stop["notes"],
                now_ts()
            ))

        conn.commit()
        conn.close()
        flash(f"Route created with {len(parsed_stops)} parsed stops.", "success")
        return redirect(url_for("view_route", route_id=route_id))

    conn.close()
    driver_options = '<option value="">Unassigned</option>'
    for d in drivers:
        driver_options += f'<option value="{d["id"]}">{e(d["username"])}</option>'

    dump_options = '<option value="">— No dump location —</option>'
    for dl in dump_locs:
        city_label = f" ({e(dl['city'])})" if dl['city'] else ""
        dump_options += f'<option value="{dl["id"]}">{e(dl["name"])}{city_label}</option>'

    body = f"""
    <div class="hero">
        <h1>Create Route</h1>
        <p>Paste your boss route text, auto-parse stops, assign a driver, and send it live.</p>
    </div>
    <div class="card">
        <form method="POST">
            <label>Route Name</label>
            <input name="route_name" placeholder="Friday Roll Off Route" required>
            <label>Route Date</label>
            <input type="date" name="route_date" value="{today_str()}" required>
            <label>Assign Driver</label>
            <select name="assigned_to">{driver_options}</select>
            <label>Dump Location</label>
            <select name="dump_location_id">{dump_options}</select>
            <label>Boss Route Text</label>
            <textarea name="raw_text" placeholder="Paste the exact route text your boss sends..."></textarea>
            <label>Notes</label>
            <textarea name="notes" placeholder="Extra route instructions..."></textarea>
            <div style="margin-top:10px;"><button type="submit">Create Route + Parse Stops</button></div>
        </form>
    </div>
    """
    return render_template_string(shell_page("Create Route", body))

@app.route("/driver/route/<int:route_id>")
@driver_required
def driver_route_detail(route_id):
    conn = get_db()
    route = conn.execute("""
        SELECT r.*, u.username AS assigned_username
        FROM routes r
        LEFT JOIN users u ON r.assigned_to = u.id
        WHERE r.id = ? AND r.assigned_to = ?
    """, (route_id, session["user_id"])).fetchone()

    if not route:
        conn.close()
        flash("Route not found.", "error")
        return redirect(url_for("driver_dashboard"))

    stops = conn.execute("""
        SELECT *
        FROM stops
        WHERE route_id = ?
        ORDER BY stop_order ASC, id ASC
    """, (route_id,)).fetchall()

    stop_ids = [s["id"] for s in stops]
    photos_by_stop = load_stop_photos(conn, stop_ids)

    dump_loc = None
    if route["dump_location_id"]:
        dump_loc = conn.execute(
            "SELECT * FROM dump_locations WHERE id=?", (route["dump_location_id"],)
        ).fetchone()

    conn.close()

    completed_count = sum(1 for s in stops if s["status"] == "completed")
    total_count = len(stops)

    from urllib.parse import quote_plus

    addresses = []
    for s in stops:
        full_address = " ".join(filter(None, [
            s["address"] or "",
            s["city"] or "",
            s["state"] or "",
            s["zip_code"] or "",
        ])).strip()
        if full_address:
            addresses.append(full_address)

    route_map_url = ""
    if len(addresses) == 1:
        route_map_url = "https://www.google.com/maps/search/?api=1&query=" + quote_plus(addresses[0])
    elif len(addresses) >= 2:
        origin = quote_plus(addresses[0])
        destination = quote_plus(addresses[-1])
        route_map_url = (
            "https://www.google.com/maps/dir/?api=1"
            f"&origin={origin}"
            f"&destination={destination}"
            "&travelmode=driving"
        )
        if len(addresses) > 2:
            waypoints = "|".join(quote_plus(a) for a in addresses[1:-1])
            route_map_url += f"&waypoints={waypoints}"

    # Apple Maps full route: supports origin→destination with optional +to: waypoints
    route_map_url_apple = ""
    if len(addresses) == 1:
        route_map_url_apple = "https://maps.apple.com/?q=" + quote_plus(addresses[0]) + "&dirflg=d"
    elif len(addresses) >= 2:
        # Apple Maps supports multi-stop via "daddr=A+to:B+to:C" (up to ~10 stops reliable)
        daddr = "+to:".join(quote_plus(a) for a in addresses[1:])
        route_map_url_apple = (
            "https://maps.apple.com/?saddr=" + quote_plus(addresses[0]) +
            "&daddr=" + daddr +
            "&dirflg=d"
        )

    # Google Maps waypoints cap at 8 intermediate stops (10 total incl. origin+dest)
    route_map_url_google = route_map_url
    if len(addresses) > 10:
        origin_g = quote_plus(addresses[0])
        dest_g   = quote_plus(addresses[-1])
        wpts     = "|".join(quote_plus(a) for a in addresses[1:9])
        route_map_url_google = (
            "https://www.google.com/maps/dir/?api=1"
            f"&origin={origin_g}&destination={dest_g}"
            f"&waypoints={wpts}&travelmode=driving"
        )

    nav_card_btns = ""
    if route_map_url_google:
        nav_card_btns += (
            f'<a class="btn-driver btn-driver-nav" target="_blank" href="{route_map_url_google}">'
            '&#128205; Google Maps</a>'
        )
    if route_map_url_apple:
        nav_card_btns += (
            f'<a class="btn-driver btn-driver-apple" target="_blank" href="{route_map_url_apple}">'
            '&#63743; Apple Maps</a>'
        )

    nav_card_html = ""
    if nav_card_btns:
        stop_word = "stop" if len(addresses) == 1 else "stops"
        nav_card_html = f"""
<div class="card" style="margin-bottom:14px;">
    <div style="font-weight:900;font-size:16px;margin-bottom:4px;">Start Full Route Navigation</div>
    <div class="small muted" style="margin-bottom:14px;">Opens all {len(addresses)} {stop_word} in order &bull; driving mode</div>
    <div class="dsc-action-row">{nav_card_btns}</div>
</div>"""

    # Dump location card
    dump_card_html = ""
    if dump_loc:
        from urllib.parse import quote_plus as _qp
        _dump_addr_parts = [
            dump_loc["address"] or "",
            dump_loc["city"] or "",
            dump_loc["state"] or "",
            dump_loc["zip_code"] or "",
        ]
        _dump_addr = " ".join(p for p in _dump_addr_parts if p).strip()
        _dump_google = "https://www.google.com/maps/dir/?api=1&destination=" + _qp(_dump_addr) if _dump_addr else ""
        _dump_apple  = "http://maps.apple.com/?daddr=" + _qp(_dump_addr) if _dump_addr else ""
        _dump_notes  = f'<div class="small muted" style="margin-top:4px;">{e(dump_loc["notes"])}</div>' if dump_loc["notes"] else ""
        _dump_nav = ""
        if _dump_google:
            _dump_nav += f'<a class="btn-driver btn-driver-nav" target="_blank" href="{_dump_google}">&#128205; Google Maps</a>'
        if _dump_apple:
            _dump_nav += f'<a class="btn-driver btn-driver-apple" target="_blank" href="{_dump_apple}">&#63743; Apple Maps</a>'
        dump_card_html = f"""
<div class="card" style="margin-bottom:14px;border-color:rgba(255,138,138,0.35);">
    <div style="font-weight:900;font-size:16px;margin-bottom:2px;">&#128465; Dump Location</div>
    <div style="font-size:18px;font-weight:800;color:#ff8a8a;margin-bottom:2px;">{e(dump_loc["name"])}</div>
    <div class="small muted">{e(_dump_addr)}</div>
    {_dump_notes}
    {f'<div class="dsc-action-row" style="margin-top:12px;">{_dump_nav}</div>' if _dump_nav else ""}
</div>"""

    # Build stop data list for JS distance calculation
    stop_address_data = []
    next_open_stop_id = None
    stop_cards = ""

    for s in stops:
        stop_key = s["id"]

        if next_open_stop_id is None and s["status"] != "completed":
            next_open_stop_id = stop_key

        is_next = (stop_key == next_open_stop_id)
        is_done = s["status"] == "completed"

        full_address = " ".join(filter(None, [
            s["address"] or "",
            s["city"] or "",
            s["state"] or "",
            s["zip_code"] or "",
        ])).strip()

        nav_google = "https://www.google.com/maps/dir/?api=1&destination=" + quote_plus(full_address)
        nav_apple  = "http://maps.apple.com/?daddr=" + quote_plus(full_address)

        photo_html = build_photo_gallery_html(photos_by_stop.get(s["id"], []))

        action_color = {
            "Drop": "#3fd2ff", "Pickup": "#56f0b7", "Swap": "#ffd27c",
            "Dump": "#ff8a8a", "Remove": "#ff8a8a", "Service": "#b0c4ff",
            "Final": "#c084fc", "Relocate": "#f9a8d4",
        }.get(s["action"] or "", "#b0c4ff")

        toggle_label = "Reopen Stop" if is_done else "Complete Stop"
        toggle_class = "btn-driver btn-driver-reopen" if is_done else "btn-driver btn-driver-complete"

        card_class = "driver-stop-card"
        if is_next:
            card_class += " dsc-active"
        elif is_done:
            card_class += " dsc-done"

        card_id = "next-stop-card" if is_next else f"stop-{stop_key}"

        # detail block hidden for completed stops, visible for open
        detail_style = "display:none;" if is_done else ""

        if full_address:
            stop_address_data.append({"id": stop_key, "address": full_address})

        stop_cards += f"""
<div class="{card_class}" id="{card_id}" data-stop-id="{stop_key}">

  <div class="dsc-header" onclick="toggleStopDetail({stop_key})">
    <div class="dsc-num">#{s['stop_order']}</div>
    <div class="dsc-summary">
      <div class="dsc-customer">{e(s['customer_name'] or 'Stop ' + str(s['stop_order']))}</div>
      <div class="dsc-addr">{e(full_address or 'No address')}</div>
      <div class="dsc-meta-row">
        <span class="action-pill" style="background:{action_color};color:#06101f;">{e(s['action'] or 'Service')}</span>
        {f'<span class="action-pill" style="background:rgba(150,200,255,0.18);color:#cde;">{e(s["container_size"])} yd</span>' if s['container_size'] else ''}
        <span class="badge" id="badge-{stop_key}" style="font-size:11px;">{e(s['status'])}</span>
        <span class="dist-badge" id="dist-{stop_key}"></span>
      </div>
    </div>
    <div class="dsc-chevron" id="chev-{stop_key}">{'▲' if not is_done else '▼'}</div>
  </div>

  <div class="dsc-body" id="body-{stop_key}" style="{detail_style}">
    {"" if not s['ticket_number'] else f'<div class="dsc-field"><span class="dsc-label">Ticket</span>{e(s["ticket_number"])}</div>'}
    {"" if not s['reference_number'] else f'<div class="dsc-field"><span class="dsc-label">Ref</span>{e(s["reference_number"])}</div>'}
    {"" if not s['notes'] else f'<div class="dsc-field"><span class="dsc-label">Notes</span><span style="white-space:pre-wrap;">{e(s["notes"] or "")}</span></div>'}
    <div class="dsc-field" id="done-at-row-{stop_key}" style="{'display:none;' if not s['completed_at'] else ''}">
      <span class="dsc-label">Done</span><span id="done-at-{stop_key}">{e(s['completed_at'] or '')}</span>
    </div>
    {photo_html}

    <div class="dsc-action-row" style="margin-bottom:10px;">
      <a class="btn-driver btn-driver-nav" href="{nav_google}" target="_blank">
        &#128205; Google Maps
      </a>
      <a class="btn-driver btn-driver-apple" href="{nav_apple}" target="_blank">
        &#63743; Apple Maps
      </a>
    </div>
    <form class="dsc-toggle-form" method="POST"
          action="{url_for('toggle_stop_complete', stop_id=s['id'])}"
          data-stop-id="{stop_key}">
      <button id="toggle-btn-{stop_key}" class="{toggle_class}" type="submit" style="width:100%;">{toggle_label}</button>
    </form>

    <details class="upload-details">
      <summary>&#128247; Upload Photo / Proof</summary>
      <form method="POST" action="{url_for('upload_stop_photo', stop_id=s['id'])}" enctype="multipart/form-data" style="margin-top:10px;">
        <input type="file" name="photos" accept=".png,.jpg,.jpeg,.webp,.pdf" multiple required style="margin-bottom:8px;width:100%;">
        <button class="btn secondary" type="submit" style="width:100%;">Upload</button>
      </form>
    </details>
  </div>

</div>
"""

    route_action_buttons = ""
    if route["status"] == "open":
        route_action_buttons = f"""
        <form class="inline" method="POST" action="{url_for('mark_route_in_progress', route_id=route_id)}">
            <button class="btn orange" style="font-size:16px;padding:14px 22px;">Start Route</button>
        </form>"""
    elif route["status"] == "in_progress":
        route_action_buttons = f"""
        <form class="inline" method="POST" action="{url_for('mark_route_completed', route_id=route_id)}">
            <button class="btn green" style="font-size:16px;padding:14px 22px;">Finish Route</button>
        </form>"""

    pct = int(completed_count / total_count * 100) if total_count else 0
    next_stop_num = ""
    for s in stops:
        if s["status"] != "completed":
            next_stop_num = str(s["stop_order"])
            break

    sticky_label = f"Next Stop #{next_stop_num}" if next_stop_num else "All Stops Done!"
    sticky_disabled = "disabled" if not next_stop_num else ""

    # Serialize stop addresses for JS distance engine
    import json as _json
    stop_addr_json = _json.dumps(stop_address_data)

    extra_head = """
<style>
/* ---- Driver Route Page ---- */
.driver-stop-card {
    background: linear-gradient(180deg,rgba(10,36,74,0.82),rgba(6,18,42,0.92));
    border: 1px solid rgba(120,200,255,0.22);
    border-radius: 18px;
    margin-bottom: 14px;
    overflow: hidden;
    transition: box-shadow 0.2s;
}
.dsc-active {
    border: 2px solid rgba(97,247,223,0.75) !important;
    box-shadow: 0 0 28px rgba(97,247,223,0.22);
}
.dsc-done {
    opacity: 0.55;
    border-color: rgba(80,80,100,0.3) !important;
}
.dsc-header {
    display: flex;
    align-items: flex-start;
    gap: 12px;
    padding: 16px;
    cursor: pointer;
    user-select: none;
    -webkit-tap-highlight-color: transparent;
}
.dsc-num {
    font-size: 22px;
    font-weight: 900;
    color: #61f7df;
    min-width: 36px;
    padding-top: 2px;
}
.dsc-done .dsc-num { color: #6a7a8a; }
.dsc-summary { flex: 1; }
.dsc-customer {
    font-size: 17px;
    font-weight: 800;
    color: #f0f8ff;
    line-height: 1.2;
}
.dsc-addr {
    font-size: 13px;
    color: #a0bcd8;
    margin-top: 3px;
}
.dsc-meta-row {
    display: flex;
    flex-wrap: wrap;
    gap: 6px;
    margin-top: 7px;
    align-items: center;
}
.action-pill {
    display: inline-block;
    padding: 3px 10px;
    border-radius: 999px;
    font-size: 12px;
    font-weight: 800;
}
.dist-badge {
    font-size: 12px;
    color: #8fd3ff;
    font-weight: 700;
}
.dsc-chevron {
    color: #6a8aa8;
    font-size: 14px;
    padding-top: 4px;
    min-width: 18px;
    text-align: right;
}
.dsc-body {
    padding: 0 16px 16px 16px;
    border-top: 1px solid rgba(120,200,255,0.12);
}
.dsc-field {
    display: flex;
    gap: 8px;
    font-size: 14px;
    padding: 5px 0;
    border-bottom: 1px solid rgba(120,200,255,0.07);
    color: #daeeff;
}
.dsc-field:last-of-type { border-bottom: none; }
.dsc-label {
    color: #7aa8c8;
    font-weight: 700;
    min-width: 52px;
    flex-shrink: 0;
}
.dsc-action-row {
    display: flex;
    gap: 10px;
    margin-top: 14px;
}
.btn-driver {
    flex: 1;
    display: block;
    padding: 16px 10px;
    border-radius: 14px;
    font-size: 16px;
    font-weight: 900;
    text-align: center;
    border: none;
    cursor: pointer;
    text-decoration: none;
    line-height: 1;
    -webkit-tap-highlight-color: transparent;
    touch-action: manipulation;
}
.btn-driver-nav {
    background: linear-gradient(90deg,#3fd2ff,#1aa8e0);
    color: #041220;
}
.btn-driver-complete {
    background: linear-gradient(90deg,#56f0b7,#17c972);
    color: #021a0e;
}
.btn-driver-reopen {
    background: linear-gradient(90deg,#6e8dcb,#4d6ab2);
    color: #fff;
}
.btn-driver-apple {
    background: linear-gradient(90deg,#c8cdd8,#9aa0b0);
    color: #0a1020;
}
.upload-details {
    margin-top: 12px;
}
.upload-details summary {
    color: #7ab8d8;
    font-size: 13px;
    cursor: pointer;
    padding: 6px 0;
}
.progress-bar-wrap {
    background: rgba(255,255,255,0.08);
    border-radius: 999px;
    height: 10px;
    margin: 10px 0 4px;
    overflow: hidden;
}
.progress-bar-fill {
    height: 100%;
    border-radius: 999px;
    background: linear-gradient(90deg,#61f7df,#3fd2ff);
    transition: width 0.4s ease;
}
#sticky-next-bar {
    position: fixed;
    bottom: 0;
    left: 0;
    right: 0;
    z-index: 999;
    padding: 12px 16px;
    background: rgba(6,14,30,0.96);
    border-top: 1px solid rgba(97,247,223,0.3);
    backdrop-filter: blur(12px);
}
#sticky-next-bar button {
    width: 100%;
    padding: 16px;
    font-size: 17px;
    font-weight: 900;
    border-radius: 14px;
    background: linear-gradient(90deg,#61f7df,#3fd2ff);
    color: #041220;
    border: none;
    cursor: pointer;
    touch-action: manipulation;
}
#sticky-next-bar button:disabled {
    background: rgba(80,100,130,0.5);
    color: #8899aa;
    cursor: default;
}
.stop-list-wrap { padding-bottom: 90px; }
@media (min-width: 900px) {
    #sticky-next-bar { left: 260px; }
}
</style>
"""

    body = f"""
<div class="hero" style="padding-bottom:14px;">
    <div class="row between" style="align-items:flex-start;flex-wrap:wrap;gap:10px;">
        <div>
            <h1 style="margin:0 0 4px;">{e(route['route_name'])}</h1>
            <div class="small muted">{e(route['route_date'])} &bull; {e(route['assigned_username'] or 'Unassigned')}</div>
        </div>
        <span class="badge {e(route['status'])}" style="font-size:14px;padding:8px 14px;">{e(route['status'].replace('_',' ').title())}</span>
    </div>
    <div class="progress-bar-wrap"><div id="progress-fill" class="progress-bar-fill" style="width:{pct}%;"></div></div>
    <div id="progress-text" class="small muted">{completed_count} of {total_count} stops complete</div>
    <div class="row" style="margin-top:14px;gap:10px;flex-wrap:wrap;">
        {route_action_buttons}
        <a class="btn secondary" href="{url_for('driver_dashboard')}">&#8592; Back</a>
    </div>
</div>

{nav_card_html}

{dump_card_html}

<div class="stop-list-wrap" id="stop-list">
    {stop_cards if stop_cards else '<div class="card">No stops on this route.</div>'}
</div>

<div id="sticky-next-bar">
    <button id="sticky-next-btn" onclick="scrollToNext()" {sticky_disabled}>{e(sticky_label)}</button>
</div>

<script>
(function() {{
    var csrfToken = (document.querySelector('meta[name="csrf-token"]') || {{}}).getAttribute
        ? document.querySelector('meta[name="csrf-token"]').getAttribute('content')
        : '';

    // ================================================================
    // DOM helpers
    // ================================================================
    function $id(id) {{ return document.getElementById(id); }}

    function openBody(stopId) {{
        var b = $id('body-' + stopId), c = $id('chev-' + stopId);
        if (b) b.style.display = 'block';
        if (c) c.textContent = '\u25b2';
    }}
    function closeBody(stopId) {{
        var b = $id('body-' + stopId), c = $id('chev-' + stopId);
        if (b) b.style.display = 'none';
        if (c) c.textContent = '\u25bc';
    }}

    // ================================================================
    // Toggle stop detail (tap header)
    // ================================================================
    window.toggleStopDetail = function(stopId) {{
        var b = $id('body-' + stopId);
        if (!b) return;
        if (b.style.display === 'none') openBody(stopId); else closeBody(stopId);
    }};

    // ================================================================
    // Sticky "Next Stop" scroll
    // ================================================================
    window.scrollToNext = function() {{
        var next = $id('next-stop-card');
        if (next) next.scrollIntoView({{ behavior: 'smooth', block: 'center' }});
    }};

    // Auto-scroll to next open stop on page load
    window.addEventListener('load', function() {{
        var next = $id('next-stop-card');
        if (next) setTimeout(function() {{
            next.scrollIntoView({{ behavior: 'smooth', block: 'center' }});
        }}, 350);
    }});

    // ================================================================
    // Progress bar + text update
    // ================================================================
    function updateProgress(completed, total) {{
        var pct   = total > 0 ? Math.round(completed / total * 100) : 0;
        var fill  = $id('progress-fill');
        var text  = $id('progress-text');
        if (fill) fill.style.width = pct + '%';
        if (text) text.textContent = completed + ' of ' + total + ' stops complete';
    }}

    // ================================================================
    // Sticky button text update
    // ================================================================
    function updateStickyBtn() {{
        var btn = $id('sticky-next-btn');
        if (!btn) return;
        var nextCard = document.querySelector('.driver-stop-card:not(.dsc-done)');
        if (!nextCard) {{
            btn.disabled = true;
            btn.textContent = 'All Stops Done! \u2713';
        }} else {{
            var numEl = nextCard.querySelector('.dsc-num');
            var num   = numEl ? numEl.textContent.replace('#','') : '';
            btn.disabled = false;
            btn.textContent = 'Next Stop #' + num;
        }}
    }}

    // ================================================================
    // Mark one card as completed in the DOM
    // ================================================================
    function markDone(stopId, completedAt) {{
        var card = document.querySelector('[data-stop-id="' + stopId + '"]');
        if (!card) return;
        card.classList.remove('dsc-active');
        card.classList.add('dsc-done');
        if (card.id === 'next-stop-card') card.id = 'stop-' + stopId;

        var badge = $id('badge-' + stopId);
        if (badge) {{ badge.className = 'badge completed'; badge.textContent = 'completed'; }}

        var btn = $id('toggle-btn-' + stopId);
        if (btn) {{
            btn.textContent = 'Reopen Stop';
            btn.className   = 'btn-driver btn-driver-reopen';
            btn.style.width = '100%';
        }}

        var row = $id('done-at-row-' + stopId);
        var ts  = $id('done-at-' + stopId);
        if (ts)  ts.textContent  = completedAt;
        if (row) row.style.display = '';

        closeBody(stopId);
    }}

    // ================================================================
    // Mark one card as reopened in the DOM
    // ================================================================
    function markOpen(stopId) {{
        var card = document.querySelector('[data-stop-id="' + stopId + '"]');
        if (!card) return;
        card.classList.remove('dsc-done');

        var badge = $id('badge-' + stopId);
        if (badge) {{ badge.className = 'badge open'; badge.textContent = 'open'; }}

        var btn = $id('toggle-btn-' + stopId);
        if (btn) {{
            btn.textContent = 'Complete Stop';
            btn.className   = 'btn-driver btn-driver-complete';
            btn.style.width = '100%';
        }}

        var row = $id('done-at-row-' + stopId);
        if (row) row.style.display = 'none';

        openBody(stopId);
    }}

    // ================================================================
    // Highlight the next open stop as active
    // ================================================================
    function highlightNext() {{
        document.querySelectorAll('.driver-stop-card').forEach(function(c) {{
            c.classList.remove('dsc-active');
            if (c.id === 'next-stop-card') c.id = 'stop-' + c.dataset.stopId;
        }});
        var nextCard = document.querySelector('.driver-stop-card:not(.dsc-done)');
        if (!nextCard) return null;
        nextCard.classList.add('dsc-active');
        nextCard.id = 'next-stop-card';
        openBody(nextCard.dataset.stopId);
        return nextCard;
    }}

    // ================================================================
    // AJAX stop completion — intercept all .dsc-toggle-form submits
    // ================================================================
    document.getElementById('stop-list').addEventListener('submit', function(e) {{
        var form = e.target;
        if (!form.classList.contains('dsc-toggle-form')) return;
        e.preventDefault();

        var stopId = form.dataset.stopId;
        var btn    = $id('toggle-btn-' + stopId);

        // Optimistic disable to prevent double-tap
        if (btn) {{ btn.disabled = true; btn.textContent = 'Saving\u2026'; }}

        var fd = new FormData();
        fd.append('_csrf_token', csrfToken);

        fetch(form.action, {{
            method:  'POST',
            headers: {{ 'X-Requested-With': 'XMLHttpRequest' }},
            body:    fd,
        }})
        .then(function(r) {{ return r.json(); }})
        .then(function(data) {{
            if (!data.success) throw new Error('not ok');

            if (data.new_status === 'completed') {{
                markDone(stopId, data.completed_at);
            }} else {{
                markOpen(stopId);
            }}

            updateProgress(data.progress.completed, data.progress.total);

            var nextCard = highlightNext();
            updateStickyBtn();

            if (data.new_status === 'completed' && nextCard) {{
                setTimeout(function() {{
                    nextCard.scrollIntoView({{ behavior: 'smooth', block: 'center' }});
                }}, 280);
            }}
        }})
        .catch(function() {{
            // Network/server error — fall back to a normal page reload submit
            if (btn) {{ btn.disabled = false; btn.textContent = btn.dataset.label || 'Complete Stop'; }}
            form.submit();
        }});
    }});

    // ================================================================
    // Distance: Geolocation + Nominatim geocoding
    // ================================================================
    var stopAddresses = {stop_addr_json};

    function haversine(lat1, lon1, lat2, lon2) {{
        var R = 3958.8, dLat = (lat2-lat1)*Math.PI/180, dLon = (lon2-lon1)*Math.PI/180;
        var a = Math.sin(dLat/2)*Math.sin(dLat/2) +
                Math.cos(lat1*Math.PI/180)*Math.cos(lat2*Math.PI/180)*
                Math.sin(dLon/2)*Math.sin(dLon/2);
        return R * 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1-a));
    }}

    function geocode(address, cb) {{
        fetch('https://nominatim.openstreetmap.org/search?format=json&limit=1&q=' +
              encodeURIComponent(address), {{ headers: {{ 'Accept-Language': 'en' }} }})
            .then(function(r) {{ return r.json(); }})
            .then(function(d) {{ if (d && d.length) cb(parseFloat(d[0].lat), parseFloat(d[0].lon)); }})
            .catch(function() {{}});
    }}

    if (stopAddresses.length && navigator.geolocation) {{
        navigator.geolocation.getCurrentPosition(function(pos) {{
            var uLat = pos.coords.latitude, uLon = pos.coords.longitude;
            var idx  = 0;
            (function tick() {{
                if (idx >= stopAddresses.length) return;
                var item = stopAddresses[idx++];
                geocode(item.address, function(lat, lon) {{
                    var el = $id('dist-' + item.id);
                    if (el) el.textContent = haversine(uLat, uLon, lat, lon).toFixed(1) + ' mi';
                }});
                setTimeout(tick, 1300);
            }})();
        }}, function() {{}}, {{ timeout: 8000 }});
    }}
}})();
</script>
"""
    return render_template_string(shell_page("Driver Route", body, extra_head))


@app.route("/route/<int:route_id>")
@login_required
def view_route(route_id):
    conn = get_db()
    route = conn.execute("""
        SELECT r.*, u.username AS assigned_username, c.username AS created_username
        FROM routes r
        LEFT JOIN users u ON r.assigned_to = u.id
        LEFT JOIN users c ON r.created_by = c.id
        WHERE r.id = ? AND r.company_id = ?
    """, (route_id, cid())).fetchone()
    if not route:
        conn.close()
        abort(404)

    if session.get("role") != "boss" and route["assigned_to"] != session["user_id"]:
        conn.close()
        flash("Access denied.", "error")
        return redirect(url_for("dashboard"))

    stops = conn.execute("SELECT * FROM stops WHERE route_id = ? ORDER BY stop_order ASC, id ASC", (route_id,)).fetchall()
    stop_ids = [s["id"] for s in stops]
    photos_by_stop = load_stop_photos(conn, stop_ids)
    conn.close()

    completed_count = sum(1 for s in stops if s["status"] == "completed")
    total_count = len(stops)
    
    route_action_buttons = ""

    if route["status"] == "open":
        route_action_buttons += f"""
        <form class="inline" method="POST" action="{url_for('mark_route_in_progress', route_id=route_id)}">
            <button class="btn orange" type="submit">Start Route</button>
        </form>
        """

    if route["status"] == "in_progress":
        route_action_buttons += f"""
        <form class="inline" method="POST" action="{url_for('mark_route_completed', route_id=route_id)}">
            <button class="btn green" type="submit">Complete Route</button>
        </form>
        """

    if route["status"] == "completed":
        route_action_buttons += f"""
    <form class="inline" method="POST" action="{url_for('reopen_route', route_id=route_id)}">
        <button class="btn secondary" type="submit">Reopen Route</button>
    </form>
    """

    if session.get("role") == "boss":
        route_action_buttons += f"""
    <form class="inline" method="POST" action="{url_for('optimize_route', route_id=route_id)}"
          id="optimize-form"
          onsubmit="showOptimizeOverlay(event, {len(stops)})">
        <button class="btn orange" type="submit" id="optimize-btn">&#9883; Optimize Route</button>
    </form>
    <form class="inline" method="POST"
      action="{url_for('delete_route', route_id=route_id)}"
      onsubmit="return confirm('Delete this entire route?')">
        <button class="btn red" type="submit">Delete Route</button>
    </form>
    """

    extra_head = '<script src="https://cdn.jsdelivr.net/npm/sortablejs@1.15.2/Sortable.min.js"></script>'
    reorder_script = ""
    if session.get("role") == "boss":
        reorder_script = f"""
        <script>
            document.addEventListener("DOMContentLoaded", function() {{
                const el = document.getElementById("stop-list");
                if (!el || typeof Sortable === "undefined") return;
                new Sortable(el, {{
                    animation: 150,
                    handle: ".stop-handle",
                    onEnd: function() {{
                        const ids = Array.from(el.querySelectorAll("[data-stop-id]")).map(x => x.dataset.stopId);
                        const csrfMeta = document.querySelector('meta[name="csrf-token"]');
                        fetch("{url_for('reorder_stops', route_id=route_id)}", {{
                            method: "POST",
                            headers: {{
                                "Content-Type": "application/json",
                                "X-CSRF-Token": csrfMeta ? csrfMeta.getAttribute('content') : ''
                            }},
                            body: JSON.stringify({{ stop_ids: ids }})
                        }}).then(r => r.json()).then(data => {{
                            if (data.success) window.location.reload();
                            else alert("Reorder failed");
                        }});
                    }}
                }});
            }});
        </script>
        """
    next_open_stop_id = None
    stop_cards = ""
    for s in stops:
        if next_open_stop_id is None and s["status"] != "completed":
         next_open_stop_id = s["stop_order"]
        photo_html = build_photo_gallery_html(photos_by_stop.get(s["id"], []))

        edit_button = f'<a class="btn secondary" href="{url_for("edit_stop", stop_id=s["id"])}">Edit</a>' if session.get("role") == "boss" else ''
        delete_button = f'<form class="inline" method="POST" action="{url_for("delete_stop", stop_id=s["id"])}" onsubmit="return confirm(\'Delete this stop?\')"><button class="btn red" type="submit">Delete</button></form>' if session.get("role") == "boss" else ''

        stop_cards += f"""
        <div class="stop-card" data-stop-id="{s['id']}">
            <div class="row between">
                <div>
                    {'<span class="stop-handle">☰</span>' if session.get('role') == 'boss' else ''}
                    <strong>Stop #{s['stop_order']}</strong>
                    <span class="badge {e(s['status'])}">{e(s['status'])}</span>
                </div>
                <div class="row">
                    {edit_button}
                    {delete_button}
                    <form class="inline" method="POST" action="{url_for('toggle_stop_complete', stop_id=s['id'])}">
                        <button class="btn green" type="submit">{'Reopen Stop' if s['status']=='completed' else 'Complete Stop'}</button>
                    </form>
                </div>
            </div>
            <p><strong>Customer:</strong> {e(s['customer_name'] or '')}</p>
            <p><strong>Address:</strong> {e(s['address'] or '')} {e(s['city'] or '')} {e(s['state'] or '')} {e(s['zip_code'] or '')}</p>
            <p><strong>Action:</strong> {e(s['action'] or '')}</p>
            <p><strong>Container:</strong> {e(s['container_size'] or '')}</p>
            <p><strong>Ticket:</strong> {e(s['ticket_number'] or '')}</p>
            <p><strong>Reference:</strong> {e(s['reference_number'] or '')}</p>
            <p><strong>Notes:</strong><br>{e(s['notes'] or '').replace(chr(10), '<br>')}</p>
            <p><strong>Signature:</strong> {e(s['driver_signature'] or '')}</p>
            <p><strong>Completed At:</strong> {e(s['completed_at'] or '')}</p>
            {photo_html}
            <form method="POST" action="{url_for('upload_stop_photo', stop_id=s['id'])}" enctype="multipart/form-data">
                <label>Upload Photo / Ticket / Proof</label>
                <input type="file" name="photos" accept=".png,.jpg,.jpeg,.webp,.pdf" multiple required>
                <button class="btn secondary" type="submit">Upload</button>
            </form>
        </div>
        """

    add_stop_block = ""
    if session.get("role") == "boss":
        add_stop_block = f"""
        <div class="card">
            <h2>Add Manual Stop</h2>
            <form method="POST" action="{url_for('add_stop', route_id=route_id)}">
                <div class="grid">
                    <div><label>Customer</label><input name="customer_name"></div>
                    <div><label>Address</label><input name="address"></div>
                    <div><label>City</label><input name="city"></div>
                    <div><label>State</label><input name="state"></div>
                    <div><label>ZIP</label><input name="zip_code"></div>
                    <div><label>Action</label><input name="action"></div>
                    <div><label>Container Size</label><input name="container_size"></div>
                    <div><label>Ticket Number</label><input name="ticket_number"></div>
                    <div><label>Reference Number</label><input name="reference_number"></div>
                </div>
                <label>Notes</label>
                <textarea name="notes"></textarea>
                <div style="margin-top:10px;"><button type="submit">Add Stop</button></div>
            </form>
        </div>
        """

    body = f"""
    <div class="hero">
        <h1>{e(route['route_name'])}</h1>
        <p>{e(route['route_date'])} | Assigned to: {e(route['assigned_username'] or 'Unassigned')}</p>
        <p>Status: <span class="badge {e(route['status'])}">{e(route['status'])}</span></p>
        <p>Progress: {completed_count}/{total_count} stops completed</p>
        <div class="row" style="margin-top:12px;">
            {route_action_buttons}
        </div>
    </div>

    <div id="stop-list">
        {stop_cards}
    </div>

    {add_stop_block}
    {reorder_script}

    <!-- Optimize loading overlay -->
    <div id="optimize-overlay" style="
            display:none; position:fixed; inset:0; z-index:2000;
            background:rgba(4,10,22,0.88); backdrop-filter:blur(6px);
            flex-direction:column; align-items:center; justify-content:center;
            color:#e5eefc; font-family:inherit;">
        <div style="font-size:42px; margin-bottom:16px;">&#9883;</div>
        <div style="font-size:20px; font-weight:900; margin-bottom:8px;">Optimizing Route&hellip;</div>
        <div id="optimize-msg" style="font-size:14px; color:#8fd3ff; margin-bottom:24px;">
            Geocoding stops &mdash; this takes about 1 second per stop
        </div>
        <div style="width:240px; background:rgba(255,255,255,0.1); border-radius:999px; height:8px; overflow:hidden;">
            <div id="optimize-progress-bar"
                 style="height:100%; width:0%; border-radius:999px;
                        background:linear-gradient(90deg,#61f7df,#3fd2ff);
                        transition:width 1.1s linear;"></div>
        </div>
        <div id="optimize-step" style="font-size:12px; color:#6a8aa8; margin-top:10px;"></div>
    </div>

    <script>
    function showOptimizeOverlay(e, stopCount) {{
        var overlay = document.getElementById('optimize-overlay');
        if (overlay) {{
            overlay.style.display = 'flex';
            // Animate the fake progress bar in sync with geocoding (1.1s/stop)
            var bar  = document.getElementById('optimize-progress-bar');
            var step = document.getElementById('optimize-step');
            var done = 0;
            var interval = setInterval(function() {{
                done++;
                if (done <= stopCount) {{
                    var pct = Math.round(done / stopCount * 85); // cap at 85% until redirect
                    if (bar)  bar.style.width  = pct + '%';
                    if (step) step.textContent = 'Geocoding stop ' + done + ' of ' + stopCount + '\u2026';
                }} else {{
                    clearInterval(interval);
                    if (bar)  bar.style.width = '100%';
                    if (step) step.textContent = 'Saving optimized order\u2026';
                }}
            }}, 1100);
        }}
        // Let the form submit normally
    }}
    </script>
    """

    return render_template_string(shell_page("Route", body, extra_head))

@app.route("/route/<int:route_id>/start", methods=["POST"])
@login_required
def mark_route_in_progress(route_id):
    conn = get_db()
    route = conn.execute(
        "SELECT * FROM routes WHERE id=? AND company_id=?", (route_id, cid())
    ).fetchone()

    if not route:
        conn.close()
        abort(404)

    if session.get("role") != "boss" and route["assigned_to"] != session["user_id"]:
        conn.close()
        flash("Access denied.", "error")
        return redirect(url_for("dashboard"))

    conn.execute("""
        UPDATE routes SET status='in_progress', started_at=?
        WHERE id=? AND company_id=?
    """, (now_ts(), route_id, cid()))

    conn.commit()
    conn.close()

    flash("Route marked in progress.", "success")
    return redirect(url_for("view_route", route_id=route_id))


@app.route("/route/<int:route_id>/complete", methods=["POST"])
@login_required
def mark_route_completed(route_id):
    conn = get_db()
    route = conn.execute(
        "SELECT * FROM routes WHERE id=? AND company_id=?", (route_id, cid())
    ).fetchone()

    if not route:
        conn.close()
        abort(404)

    if session.get("role") != "boss" and route["assigned_to"] != session["user_id"]:
        conn.close()
        flash("Access denied.", "error")
        return redirect(url_for("dashboard"))

    conn.execute("""
        UPDATE routes SET status='completed', completed_at=?
        WHERE id=? AND company_id=?
    """, (now_ts(), route_id, cid()))

    conn.commit()
    conn.close()

    flash("Route marked completed.", "success")
    return redirect(url_for("view_route", route_id=route_id))


@app.route("/route/<int:route_id>/reopen", methods=["POST"])
@login_required
def reopen_route(route_id):
    conn = get_db()
    route = conn.execute(
        "SELECT * FROM routes WHERE id=? AND company_id=?", (route_id, cid())
    ).fetchone()

    if not route:
        conn.close()
        abort(404)

    if session.get("role") != "boss" and route["assigned_to"] != session["user_id"]:
        conn.close()
        flash("Access denied.", "error")
        return redirect(url_for("dashboard"))

    conn.execute("""
        UPDATE routes SET status='open', completed_at=NULL
        WHERE id=? AND company_id=?
    """, (route_id, cid()))

    conn.commit()
    conn.close()

    flash("Route reopened.", "success")
    return redirect(url_for("view_route", route_id=route_id))


# =========================================================
# ADD STOP
# =========================================================
@app.route("/route/<int:route_id>/add_stop", methods=["POST"])
@boss_required
def add_stop(route_id):
    conn = get_db()
    if not conn.execute(
        "SELECT id FROM routes WHERE id=? AND company_id=?", (route_id, cid())
    ).fetchone():
        conn.close()
        abort(404)

    last = conn.execute(
        "SELECT MAX(stop_order) as m FROM stops WHERE route_id=?",
        (route_id,)
    ).fetchone()["m"] or 0

    conn.execute("""
        INSERT INTO stops (
            route_id, stop_order, customer_name, address, city, state, zip_code,
            action, container_size, ticket_number, reference_number, notes,
            status, created_at
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'open', ?)
    """, (
        route_id,
        last + 1,
        request.form.get("customer_name"),
        request.form.get("address"),
        request.form.get("city"),
        request.form.get("state"),
        request.form.get("zip_code"),
        request.form.get("action"),
        request.form.get("container_size"),
        request.form.get("ticket_number"),
        request.form.get("reference_number"),
        request.form.get("notes"),
        now_ts()
    ))

    conn.commit()
    conn.close()
    flash("Stop added.", "success")
    return redirect(url_for("view_route", route_id=route_id))


# =========================================================
# EDIT STOP
# =========================================================
@app.route("/stop/<int:stop_id>/edit", methods=["GET", "POST"])
@boss_required
def edit_stop(stop_id):
    conn = get_db()
    # verify stop belongs to this company
    ownership = conn.execute(
        """SELECT s.*, r.id AS route_id_chk FROM stops s
           JOIN routes r ON s.route_id = r.id
           WHERE s.id=? AND r.company_id=?""",
        (stop_id, cid())
    ).fetchone()
    if not ownership:
        conn.close()
        abort(404)

    if request.method == "POST":
        conn.execute("""
            UPDATE stops SET
                customer_name=?, address=?, city=?, state=?, zip_code=?,
                action=?, container_size=?, ticket_number=?, reference_number=?, notes=?
            WHERE id=?
        """, (
            request.form.get("customer_name"),
            request.form.get("address"),
            request.form.get("city"),
            request.form.get("state"),
            request.form.get("zip_code"),
            request.form.get("action"),
            request.form.get("container_size"),
            request.form.get("ticket_number"),
            request.form.get("reference_number"),
            request.form.get("notes"),
            stop_id
        ))
        conn.commit()
        route_id = ownership["route_id"]
        conn.close()
        flash("Stop updated.", "success")
        return redirect(url_for("view_route", route_id=route_id))

    stop = ownership
    conn.close()

    body = f"""
    <div class="card">
        <h2>Edit Stop</h2>
        <form method="POST">
            <input name="customer_name" value="{e(stop['customer_name'])}">
            <input name="address" value="{e(stop['address'])}">
            <input name="city" value="{e(stop['city'])}">
            <input name="state" value="{e(stop['state'])}">
            <input name="zip_code" value="{e(stop['zip_code'])}">
            <input name="action" value="{e(stop['action'])}">
            <input name="container_size" value="{e(stop['container_size'])}">
            <input name="ticket_number" value="{e(stop['ticket_number'])}">
            <input name="reference_number" value="{e(stop['reference_number'])}">
            <textarea name="notes">{e(stop['notes'])}</textarea>
            <button type="submit">Save</button>
        </form>
    </div>
    """
    return render_template_string(shell_page("Edit Stop", body))

# =========================================================
# DELETE ROUTE
# =========================================================
@app.route("/route/<int:route_id>/delete", methods=["POST"])
@boss_required
def delete_route(route_id):
    conn = get_db()
    if not conn.execute(
        "SELECT id FROM routes WHERE id=? AND company_id=?", (route_id, cid())
    ).fetchone():
        conn.close()
        abort(404)

    # delete child records first
    conn.execute("DELETE FROM route_photos WHERE stop_id IN (SELECT id FROM stops WHERE route_id=?)", (route_id,))
    conn.execute("DELETE FROM stops WHERE route_id=?", (route_id,))
    conn.execute("DELETE FROM routes WHERE id=? AND company_id=?", (route_id, cid()))

    conn.commit()
    conn.close()

    flash("Route deleted.", "success")
    return redirect(url_for("routes_page"))

# =========================================
# ORDER ACTIONS
# =========================================

@app.route("/order/<int:order_id>/close", methods=["POST"])
@boss_required
def close_order(order_id):
    conn = get_db()
    conn.execute(
        "UPDATE orders SET status='closed' WHERE id = ? AND company_id = ?",
        (order_id, cid())
    )
    conn.commit()
    conn.close()
    flash("Order closed.", "success")
    return redirect(url_for("orders_page"))


@app.route("/order/<int:order_id>/delete", methods=["POST"])
@boss_required
def delete_order(order_id):
    conn = get_db()

    order = conn.execute(
        "SELECT status FROM orders WHERE id = ? AND company_id = ?",
        (order_id, cid())
    ).fetchone()

    if not order:
        conn.close()
        abort(404)

    if order["status"] == "converted":
        conn.close()
        flash("Cannot delete a converted order.", "error")
        return redirect(url_for("orders_page"))

    conn.execute("DELETE FROM orders WHERE id = ? AND company_id = ?", (order_id, cid()))
    conn.commit()
    conn.close()

    flash("Order deleted.", "success")
    return redirect(url_for("orders_page"))


# =========================================================
# DELETE STOP
# =========================================================
@app.route("/stop/<int:stop_id>/delete", methods=["POST"])
@boss_required
def delete_stop(stop_id):
    conn = get_db()
    row = conn.execute(
        """SELECT s.route_id FROM stops s
           JOIN routes r ON s.route_id = r.id
           WHERE s.id=? AND r.company_id=?""",
        (stop_id, cid())
    ).fetchone()
    if not row:
        conn.close()
        abort(404)
    route_id = row["route_id"]

    conn.execute("DELETE FROM route_photos WHERE stop_id=?", (stop_id,))
    conn.execute("DELETE FROM stops WHERE id=?", (stop_id,))
    conn.commit()
    conn.close()

    flash("Stop deleted.", "success")
    return redirect(url_for("view_route", route_id=route_id))


# =========================================================
# COMPLETE / REOPEN STOP
# =========================================================
@app.route("/stop/<int:stop_id>/toggle", methods=["POST"])
@login_required
def toggle_stop_complete(stop_id):
    conn = get_db()
    stop = conn.execute(
        """SELECT s.*, r.assigned_to, r.company_id FROM stops s
           JOIN routes r ON s.route_id = r.id
           WHERE s.id=? AND r.company_id=?""",
        (stop_id, cid())
    ).fetchone()

    if not stop:
        conn.close()
        abort(404)

    if session.get("role") != "boss" and stop["assigned_to"] != session["user_id"]:
        conn.close()
        flash("Access denied.", "error")
        return redirect(url_for("dashboard"))

    new_status = "completed" if stop["status"] == "open" else "open"
    completed_at = now_ts() if new_status == "completed" else None

    conn.execute("""
        UPDATE stops SET status=?, completed_at=? WHERE id=?
    """, (new_status, completed_at, stop_id))
    conn.commit()

    if request.headers.get("X-Requested-With") == "XMLHttpRequest":
        total     = conn.execute("SELECT COUNT(*) n FROM stops WHERE route_id=?", (stop["route_id"],)).fetchone()["n"]
        completed = conn.execute("SELECT COUNT(*) n FROM stops WHERE route_id=? AND status='completed'", (stop["route_id"],)).fetchone()["n"]
        conn.close()
        return jsonify({
            "success": True,
            "stop_id": stop_id,
            "new_status": new_status,
            "completed_at": completed_at or "",
            "progress": {"completed": completed, "total": total},
        })

    conn.close()
    return redirect(url_for("view_route", route_id=stop["route_id"]))


# =========================================================
# REORDER STOPS
# =========================================================
@app.route("/route/<int:route_id>/reorder", methods=["POST"])
@boss_required
def reorder_stops(route_id):
    conn = get_db()
    if not conn.execute(
        "SELECT id FROM routes WHERE id=? AND company_id=?", (route_id, cid())
    ).fetchone():
        conn.close()
        return jsonify({"success": False, "error": "not found"}), 404

    data = request.get_json()
    ids = data.get("stop_ids", [])

    for i, sid in enumerate(ids, start=1):
        # scope update to stops that actually belong to this route
        conn.execute(
            "UPDATE stops SET stop_order=? WHERE id=? AND route_id=?",
            (i, sid, route_id)
        )
    conn.commit()
    conn.close()

    return jsonify({"success": True})


# =========================================================
# ROUTE OPTIMIZATION
# =========================================================
@app.route("/route/<int:route_id>/optimize", methods=["POST"])
@boss_required
def optimize_route(route_id):
    conn = get_db()
    stops = conn.execute(
        "SELECT * FROM stops WHERE route_id=? ORDER BY stop_order ASC, id ASC",
        (route_id,)
    ).fetchall()

    if len(stops) < 2:
        conn.close()
        flash("Need at least 2 stops to optimize.", "error")
        return redirect(url_for("view_route", route_id=route_id))

    # Geocode every stop that has an address
    geocoded   = []   # (stop_id, lat, lng)
    no_address = []   # stop_ids with no geocodable address

    for idx, s in enumerate(stops):
        addr = " ".join(filter(None, [
            s["address"] or "", s["city"] or "",
            s["state"] or "", s["zip_code"] or "",
        ])).strip()

        if addr:
            coords = _geocode_server(addr)
            if coords:
                geocoded.append((s["id"], coords[0], coords[1]))
            else:
                no_address.append(s["id"])
            # Nominatim rate-limit: 1 request/second
            if idx < len(stops) - 1:
                time.sleep(1.1)
        else:
            no_address.append(s["id"])

    if len(geocoded) < 2:
        conn.close()
        flash("Not enough addresses could be geocoded to optimize the route.", "error")
        return redirect(url_for("view_route", route_id=route_id))

    # Nearest-neighbor reorder; append ungeocoded stops at the end
    optimized_ids = _nearest_neighbor(geocoded) + no_address

    for new_order, stop_id in enumerate(optimized_ids, start=1):
        conn.execute("UPDATE stops SET stop_order=? WHERE id=?", (new_order, stop_id))
    conn.commit()
    conn.close()

    skipped = len(no_address)
    skip_note = f" ({skipped} stop{'s' if skipped != 1 else ''} without address appended at end)" if skipped else ""
    flash(f"Route optimized: {len(geocoded)} stops reordered by shortest driving distance.{skip_note}", "success")
    return redirect(url_for("view_route", route_id=route_id))


# =========================================================
# PHOTO UPLOAD
# =========================================================
@app.route("/stop/<int:stop_id>/upload", methods=["POST"])
@login_required
def upload_stop_photo(stop_id):
    conn = get_db()
    stop_row = conn.execute(
        """SELECT r.id AS route_id, r.assigned_to FROM stops s
           JOIN routes r ON s.route_id = r.id
           WHERE s.id=? AND r.company_id=?""",
        (stop_id, cid())
    ).fetchone()
    if not stop_row:
        conn.close()
        abort(404)
    route_id = stop_row["route_id"]

    # Drivers may only upload to their own routes
    if session.get("role") != "boss" and stop_row["assigned_to"] != session["user_id"]:
        conn.close()
        flash("Access denied.", "error")
        return redirect(url_for("dashboard"))

    files = request.files.getlist("photos")
    if not files or all(f.filename == "" for f in files):
        conn.close()
        flash("No file selected.", "error")
        return redirect(url_for("view_route", route_id=route_id))

    saved = 0
    for file in files:
        if file.filename == "" or not allowed_file(file.filename):
            continue
        uid = secrets.token_hex(8)
        filename = f"{stop_id}_{uid}_{secure_filename(file.filename)}"
        path = os.path.join(app.config["UPLOAD_FOLDER"], filename)
        file.save(path)
        conn.execute(
            "INSERT INTO route_photos (stop_id, file_path, uploaded_at, uploaded_by) VALUES (?,?,?,?)",
            (stop_id, path, now_ts(), session.get("user_id")),
        )
        saved += 1

    if saved:
        conn.commit()
        flash(f"{saved} photo(s) uploaded.", "success")
    else:
        flash("No valid files uploaded.", "error")
    conn.close()
    return redirect(url_for("view_route", route_id=route_id))


# =========================================================
# CSV EXPORT
# =========================================================
@app.route("/route/<int:route_id>/csv")
@login_required
def export_route_csv(route_id):
    conn = get_db()
    stops = conn.execute("SELECT * FROM stops WHERE route_id=?", (route_id,)).fetchall()
    conn.close()

    output = io.StringIO()
    writer = csv.writer(output)

    writer.writerow(["Stop", "Customer", "Address", "Action", "Status"])

    for s in stops:
        writer.writerow([
            s["stop_order"],
            s["customer_name"],
            s["address"],
            s["action"],
            s["status"]
        ])

    output.seek(0)

    return send_file(
        io.BytesIO(output.read().encode()),
        mimetype="text/csv",
        as_attachment=True,
        download_name="route.csv"
    )


# =========================================================
# AI DISPATCH SYSTEM
# =========================================================
@app.route("/ai", methods=["GET", "POST"])
@login_required
def ai_dispatch():
    results = []

    if request.method == "POST":
        lines = request.form.get("loads", "").splitlines()
        conn = get_db()

        for line in lines:
            parsed = parse_load_input_line(line)
            if parsed:
                conn.execute("""
                    INSERT INTO load_scores (
                        origin, destination, pickup_time, payout, miles,
                        estimated_profit, score, notes, created_by, company_id, created_at
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, (
                    parsed["origin"],
                    parsed["destination"],
                    parsed["pickup_time"],
                    parsed["payout"],
                    parsed["miles"],
                    parsed["estimated_profit"],
                    parsed["score"],
                    parsed["notes"],
                    session["user_id"],
                    cid(),
                    now_ts()
                ))
                results.append(parsed)

        conn.commit()
        conn.close()

    rows = ""
    for r in results:
        rows += f"<tr><td>{e(r['origin'])}</td><td>{e(r['destination'])}</td><td>{e(str(r['score']))}</td></tr>"

    body = f"""
    <div class="card">
        <h2>AI Load Scoring</h2>
        <form method="POST">
            <textarea name="loads" placeholder="VA > NC / 8am / 1200 / 300"></textarea>
            <button type="submit">Score Loads</button>
        </form>

        <table>
            <tr><th>Origin</th><th>Destination</th><th>Score</th></tr>
            {rows}
        </table>
    </div>
    """

    return render_template_string(shell_page("AI Dispatch", body))


# =========================================================
# COMPANY REGISTRATION (public — creates a new tenant)
# =========================================================
@app.route("/register-company", methods=["GET", "POST"])
def company_register():
    init_db()

    if request.method == "POST":
        company_name = request.form.get("company_name", "").strip()
        username     = request.form.get("username", "").strip()
        password     = request.form.get("password", "").strip()
        full_name    = request.form.get("full_name", "").strip()
        phone        = request.form.get("phone", "").strip()

        if not company_name or not username or not password:
            flash("Company name, username, and password are required.", "error")
            return redirect(url_for("company_register"))

        # make a URL-safe slug from company name
        slug_base = re.sub(r"[^a-z0-9]+", "-", company_name.lower()).strip("-")
        slug = slug_base
        conn = get_db()
        # ensure unique slug
        n = 1
        while conn.execute("SELECT id FROM companies WHERE slug=?", (slug,)).fetchone():
            slug = f"{slug_base}-{n}"
            n += 1

        try:
            trial_ends = (datetime.now() + timedelta(days=14)).strftime("%Y-%m-%d %H:%M:%S")
            conn.execute(
                """INSERT INTO companies (name, slug, subscription_plan, subscription_status,
                   max_drivers, trial_ends_at, created_at) VALUES (?,?,?,?,?,?,?)""",
                (company_name, slug, "trial", "active", 5, trial_ends, now_ts())
            )
            conn.commit()
            company_id = conn.execute("SELECT id FROM companies WHERE slug=?", (slug,)).fetchone()["id"]

            conn.execute(
                """INSERT INTO users (username, password_hash, role, full_name, phone,
                   company_id, created_at) VALUES (?,?,?,?,?,?,?)""",
                (username, generate_password_hash(password), "boss",
                 full_name, phone, company_id, now_ts())
            )
            conn.commit()
            owner_id = conn.execute("SELECT id FROM users WHERE username=? AND company_id=?",
                                    (username, company_id)).fetchone()["id"]
            conn.execute("UPDATE companies SET owner_id=? WHERE id=?", (owner_id, company_id))

            # record initial trial subscription
            conn.execute(
                """INSERT INTO subscriptions (company_id, plan, status, started_at, created_at)
                   VALUES (?,?,?,?,?)""",
                (company_id, "trial", "active", now_ts(), now_ts())
            )
            conn.commit()
            conn.close()
            flash("Account created! Please log in.", "success")
            return redirect(url_for("login"))

        except sqlite3.IntegrityError:
            conn.close()
            flash("That username is already taken.", "error")
            return redirect(url_for("company_register"))

    body = """
    <div style="max-width:560px;margin:60px auto;">
        <div class="hero">
            <h1>Start Free Trial</h1>
            <p>Create your HAULTRA company account — free for 14 days, no credit card required.</p>
        </div>
        <div class="card">
            <form method="POST">
                <label>Company Name</label>
                <input name="company_name" placeholder="ABC Hauling LLC" required>
                <label>Your Username (boss login)</label>
                <input name="username" required>
                <label>Password</label>
                <input type="password" name="password" required>
                <label>Full Name</label>
                <input name="full_name">
                <label>Phone</label>
                <input name="phone">
                <div style="margin-top:14px;">
                    <button type="submit" class="btn green" style="width:100%;font-size:16px;padding:14px;">
                        Create Company Account
                    </button>
                </div>
                <p class="muted small" style="margin-top:12px;text-align:center;">
                    Already have an account? <a href="/login">Log in</a>
                </p>
            </form>
        </div>
    </div>
    """
    return render_template_string(shell_page("Register", body))


# =========================================================
# COMPANY SETTINGS
# =========================================================
@app.route("/company/settings", methods=["GET", "POST"])
@boss_required
def company_settings():
    conn = get_db()
    company = conn.execute("SELECT * FROM companies WHERE id=?", (cid(),)).fetchone()

    if request.method == "POST":
        new_name = request.form.get("company_name", "").strip()
        if new_name:
            conn.execute("UPDATE companies SET name=? WHERE id=?", (new_name, cid()))
            conn.commit()
            flash("Company name updated.", "success")
        conn.close()
        return redirect(url_for("company_settings"))

    conn.close()

    plan_labels = {
        "trial": ("Trial", "#fbbf24"),
        "starter": ("Starter", "#3fd2ff"),
        "pro": ("Pro", "#56f0b7"),
        "enterprise": ("Enterprise", "#c084fc"),
    }
    plan      = company["subscription_plan"] if company else "trial"
    plan_name, plan_color = plan_labels.get(plan, ("Unknown", "#9dc8f0"))
    max_d     = company["max_drivers"] if company else 0
    co_name   = company["name"] if company else ""
    co_slug   = company["slug"] if company else ""
    trial_end = company["trial_ends_at"] if company else ""

    body = f"""
    <div class="hero">
        <h1>Company Settings</h1>
        <p>Manage your company profile and account details.</p>
    </div>

    <div class="card">
        <h2>Profile</h2>
        <form method="POST">
            <label>Company Name</label>
            <input name="company_name" value="{e(co_name)}" required>
            <div style="margin-top:10px;">
                <button type="submit" class="btn">Save</button>
            </div>
        </form>
        <p class="muted small" style="margin-top:10px;">Slug: <code>{e(co_slug)}</code></p>
    </div>

    <div class="card">
        <h2>Subscription</h2>
        <div class="grid">
            <div class="stat" style="border-color:{plan_color}40;">
                <div>Current Plan</div>
                <div class="num" style="color:{plan_color};font-size:22px;">{plan_name}</div>
            </div>
            <div class="stat">
                <div>Max Drivers</div>
                <div class="num">{max_d}</div>
            </div>
            {"" if not trial_end else f'<div class="stat"><div>Trial Ends</div><div class="num" style="font-size:16px;">{e(trial_end)}</div></div>'}
        </div>
        <a class="btn orange" href="{url_for('company_subscription')}" style="margin-top:12px;display:inline-block;">
            Manage Subscription
        </a>
    </div>
    """
    return render_template_string(shell_page("Company Settings", body))


# =========================================================
# SUBSCRIPTION MANAGEMENT (placeholder)
# =========================================================
@app.route("/company/subscription")
@boss_required
def company_subscription():
    conn = get_db()
    company = conn.execute("SELECT * FROM companies WHERE id=?", (cid(),)).fetchone()
    history = conn.execute(
        "SELECT * FROM subscriptions WHERE company_id=? ORDER BY started_at DESC",
        (cid(),)
    ).fetchall()
    conn.close()

    plan   = company["subscription_plan"]   if company else "trial"
    status = company["subscription_status"] if company else "active"
    max_d  = company["max_drivers"]         if company else 5
    trial_ends_at = company["trial_ends_at"] if company else None

    # compute trial countdown
    trial_banner = ""
    if plan == "trial" and trial_ends_at:
        try:
            ends_dt   = datetime.strptime(trial_ends_at, "%Y-%m-%d %H:%M:%S")
            days_left = (ends_dt - datetime.now()).days
            if days_left > 0:
                trial_banner = (
                    f'<div style="background:rgba(251,191,36,0.15);border:1px solid rgba(251,191,36,0.4);'
                    f'border-radius:10px;padding:14px 18px;margin-bottom:18px;">'
                    f'&#9888; Your free trial ends in <strong>{days_left} day{"s" if days_left != 1 else ""}</strong>. '
                    f'Contact <a href="mailto:info@haultraai.com">info@haultraai.com</a> to upgrade.</div>'
                )
            elif status == "active":
                trial_banner = (
                    '<div style="background:rgba(248,113,113,0.15);border:1px solid rgba(248,113,113,0.4);'
                    'border-radius:10px;padding:14px 18px;margin-bottom:18px;">'
                    '&#128274; Your trial has expired. Upgrade to restore full access.</div>'
                )
        except ValueError:
            pass

    plans = [
        ("trial",      "Free",       "$0",    "14 days • up to 5 drivers",                  "#fbbf24"),
        ("starter",    "Starter",    "$49/mo","Up to 10 drivers",                            "#3fd2ff"),
        ("pro",        "Pro",        "$99/mo","Up to 30 drivers • priority support",         "#56f0b7"),
        ("enterprise", "Enterprise", "Custom","Unlimited drivers • dedicated support",       "#c084fc"),
    ]

    # plan display label map
    plan_labels = {
        "trial":      "Free Trial",
        "starter":    "Starter",
        "pro":        "Pro",
        "enterprise": "Enterprise",
    }
    plan_label = plan_labels.get(plan, plan.title())

    # expiration date display
    if plan == "trial" and trial_ends_at:
        exp_display = trial_ends_at[:10]   # YYYY-MM-DD
        try:
            ends_dt2 = datetime.strptime(trial_ends_at, "%Y-%m-%d %H:%M:%S")
            days_left2 = (ends_dt2 - datetime.now()).days
            if days_left2 > 0:
                exp_display = f"{trial_ends_at[:10]} ({days_left2}d left)"
            else:
                exp_display = f"{trial_ends_at[:10]} (expired)"
        except ValueError:
            pass
    else:
        exp_display = "—" if status == "active" else "Subscription ended"

    # upgrade CTA visibility: only show when not already on enterprise
    show_upgrade = plan in ("trial", "starter", "pro")
    upgrade_btn = (
        '<a href="mailto:info@haultraai.com?subject=Upgrade%20Request" '
        'class="btn" style="background:linear-gradient(135deg,#3fd2ff,#56f0b7);'
        'color:#0a1628;font-weight:700;border:none;padding:10px 22px;'
        'text-decoration:none;border-radius:8px;display:inline-block;">'
        '&#11014;&#65039; Upgrade Plan</a>'
    ) if show_upgrade else ""

    plan_cards = ""
    for key, label, price, desc, color in plans:
        active = key == plan
        border = f"border:2px solid {color};" if active else "border:1px solid rgba(255,255,255,0.08);"
        badge  = (f'<span class="badge" style="background:{color}30;color:{color};'
                  f'font-size:11px;margin-left:8px;">&#10003; Current</span>') if active else ""
        upgrade_card_btn = ""
        if not active and key != "trial":
            upgrade_card_btn = (
                f'<div style="margin-top:12px;">'
                f'<a href="mailto:info@haultraai.com?subject=Upgrade%20to%20{label}" '
                f'class="btn" style="background:{color}22;color:{color};border:1px solid {color}55;'
                f'font-size:13px;padding:7px 16px;text-decoration:none;border-radius:7px;display:inline-block;">'
                f'Upgrade to {label}</a></div>'
            )
        plan_cards += f"""
        <div class="stat" style="padding:18px;{border}border-radius:12px;">
            <div style="font-size:16px;font-weight:800;">{label}{badge}</div>
            <div class="num" style="color:{color};font-size:24px;margin:6px 0;">{price}</div>
            <div class="muted small">{desc}</div>
            {upgrade_card_btn}
        </div>"""

    # current usage
    conn2 = get_db()
    driver_count = conn2.execute(
        "SELECT COUNT(*) n FROM users WHERE role='driver' AND company_id=?", (cid(),)
    ).fetchone()["n"]
    conn2.close()

    pct = int(driver_count / max_d * 100) if max_d else 0
    bar_color = "#f87171" if pct >= 90 else "#3fd2ff"
    seat_bar = f"""
    <div style="margin-top:6px;">
        <div style="font-size:13px;color:#9dc8f0;margin-bottom:4px;">{driver_count} / {max_d} driver seats used</div>
        <div class="mini-prog-track" style="width:100%;height:10px;">
            <div class="mini-prog-fill" style="width:{pct}%;background:{bar_color};"></div>
        </div>
    </div>"""

    hist_rows = ""
    for h in history:
        plan_hl = plan_labels.get(h["plan"], h["plan"].title())
        hist_rows += f"""
        <tr>
            <td>{e(plan_hl)}</td>
            <td><span class="badge">{e(h['status'].title())}</span></td>
            <td>{e(h['started_at'])}</td>
            <td>{e(h['ends_at'] or '—')}</td>
            <td>{e(h['notes'] or '')}</td>
        </tr>"""

    status_color = "#4ade80" if status == "active" else "#f87171"
    plan_color_map = {
        "trial": "#fbbf24", "starter": "#3fd2ff",
        "pro": "#56f0b7", "enterprise": "#c084fc",
    }
    pc = plan_color_map.get(plan, "#9dc8f0")

    body = f"""
    <div class="hero">
        <h1>Billing &amp; Subscription</h1>
        <p>Your plan details, usage, and upgrade options.</p>
    </div>

    {trial_banner}

    <div class="card">
        <div style="display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:12px;margin-bottom:18px;">
            <h2 style="margin:0;">Plan Overview</h2>
            {upgrade_btn}
        </div>
        <div class="grid">
            <div class="stat">
                <div class="muted small">Current Plan</div>
                <div class="num" style="color:{pc};font-size:22px;">{plan_label}</div>
            </div>
            <div class="stat">
                <div class="muted small">Status</div>
                <div class="num" style="color:{status_color};font-size:22px;">{status.title()}</div>
            </div>
            <div class="stat">
                <div class="muted small">{"Trial Expiration" if plan == "trial" else "Renewal / Expiration"}</div>
                <div class="num" style="font-size:16px;font-weight:600;">{exp_display}</div>
            </div>
            <div class="stat">
                <div class="muted small">Driver Seats</div>
                {seat_bar}
            </div>
        </div>
    </div>

    <div class="card">
        <h2>Available Plans</h2>
        <div class="grid">{plan_cards}</div>
        <p class="muted small" style="margin-top:14px;">
            &#9993; To upgrade, email <strong>info@haultraai.com</strong> with your company name and desired plan.
            Self-serve billing coming soon.
        </p>
    </div>

    <div class="card">
        <h2>Subscription History</h2>
        <div class="table-wrap">
            <table>
                <thead><tr><th>Plan</th><th>Status</th><th>Started</th><th>Ends</th><th>Notes</th></tr></thead>
                <tbody>{hist_rows or '<tr><td colspan="5" class="muted">No history yet.</td></tr>'}</tbody>
            </table>
        </div>
    </div>
    """
    return render_template_string(shell_page("Subscription", body))


# =========================================================
# SUPERADMIN PANEL
# =========================================================
@app.route("/superadmin")
@superadmin_required
def superadmin_panel():
    conn = get_db()
    companies = conn.execute("""
        SELECT c.*,
               COALESCE(u.username, '—') AS owner_username,
               (SELECT COUNT(*) FROM users uu WHERE uu.company_id = c.id) AS user_count,
               (SELECT COUNT(*) FROM routes r WHERE r.company_id = c.id) AS route_count
        FROM companies c
        LEFT JOIN users u ON c.owner_id = u.id
        ORDER BY c.created_at DESC
    """).fetchall()
    conn.close()

    now_dt = datetime.now()

    rows = ""
    for c in companies:
        # compute trial days remaining
        trial_cell = "—"
        if c["subscription_plan"] == "trial" and c["trial_ends_at"]:
            try:
                ends = datetime.strptime(c["trial_ends_at"], "%Y-%m-%d %H:%M:%S")
                days_left = (ends - now_dt).days
                if days_left > 0:
                    trial_cell = f'<span style="color:#fbbf24;">{days_left}d left</span>'
                else:
                    trial_cell = '<span style="color:#f87171;">Expired</span>'
            except ValueError:
                trial_cell = e(c["trial_ends_at"])

        status_color = {"active": "completed", "suspended": "in_progress", "cancelled": "open"}
        status_cls   = status_color.get(c["subscription_status"], "")

        rows += f"""
        <tr>
            <td><strong>{e(c['name'])}</strong></td>
            <td><code style="font-size:11px;">{e(c['slug'])}</code></td>
            <td>{e(c['owner_username'])}</td>
            <td><span class="badge">{e(c['subscription_plan'].title())}</span></td>
            <td><span class="badge {status_cls}">{e(c['subscription_status'].title())}</span></td>
            <td>{trial_cell}</td>
            <td>{c['max_drivers']}</td>
            <td>{c['user_count']}</td>
            <td>{c['route_count']}</td>
            <td style="white-space:nowrap;">
                <a class="btn secondary" href="{url_for('superadmin_edit_company', company_id=c['id'])}"
                   style="font-size:12px;padding:4px 10px;">Edit</a>
            </td>
        </tr>"""

    body = f"""
    <div class="hero">
        <h1>&#128295; Superadmin</h1>
        <p>Full visibility across all companies on this HAULTRA instance.</p>
    </div>
    <div class="card">
        <h2>All Companies ({len(companies)})</h2>
        <div class="table-wrap">
            <table>
                <thead><tr>
                    <th>Company</th><th>Slug</th><th>Owner</th><th>Plan</th>
                    <th>Status</th><th>Trial</th><th>Max Drivers</th>
                    <th>Users</th><th>Routes</th><th></th>
                </tr></thead>
                <tbody>{rows or '<tr><td colspan="10" class="muted">No companies.</td></tr>'}</tbody>
            </table>
        </div>
    </div>
    """
    return render_template_string(shell_page("Superadmin", body))


# =========================================================
# SUBSCRIPTION BLOCKED PAGE
# =========================================================
@app.route("/subscription/blocked")
def subscription_blocked():
    conn = get_db()
    company_id = session.get("company_id")
    co = None
    if company_id:
        co = conn.execute(
            "SELECT name, subscription_plan, subscription_status, trial_ends_at FROM companies WHERE id=?",
            (company_id,)
        ).fetchone()
    conn.close()

    plan   = co["subscription_plan"] if co else "trial"
    status = co["subscription_status"] if co else "suspended"
    name   = co["name"] if co else ""

    if status == "suspended" and plan == "trial":
        reason = "Your 14-day free trial has ended."
        action = "Upgrade to a paid plan to restore access."
    elif status == "suspended":
        reason = "Your account has been suspended."
        action  = "Please contact support or upgrade your plan."
    else:
        reason = "Your account has been cancelled."
        action  = "Contact support to reactivate."

    sub_link = ""
    if session.get("role") == "boss":
        sub_link = f'<a class="btn green" href="{url_for("company_subscription")}" style="margin-top:16px;display:inline-block;font-size:16px;padding:14px 28px;">View Plans &amp; Upgrade</a>'

    body = f"""
    <div style="max-width:560px;margin:80px auto;text-align:center;">
        <div class="hero">
            <div style="font-size:52px;margin-bottom:12px;">&#128274;</div>
            <h1>Account Access Restricted</h1>
            <p style="font-size:16px;">{e(reason)}</p>
            <p class="muted">{e(action)}</p>
            {sub_link}
            <p style="margin-top:20px;">
                <a href="{url_for('logout')}" class="muted small">Log out</a>
                &nbsp;·&nbsp;
                <a href="mailto:info@haultraai.com" class="muted small">Contact Support</a>
            </p>
        </div>
    </div>
    """
    return render_template_string(shell_page("Access Restricted", body))


# =========================================================
# SUPERADMIN — EDIT COMPANY PLAN
# =========================================================
@app.route("/superadmin/company/<int:company_id>/edit", methods=["GET", "POST"])
@superadmin_required
def superadmin_edit_company(company_id):
    conn = get_db()
    co = conn.execute("SELECT * FROM companies WHERE id=?", (company_id,)).fetchone()
    if not co:
        conn.close()
        abort(404)

    PLAN_LIMITS = {
        "trial":      5,
        "starter":    10,
        "pro":        30,
        "enterprise": 9999,
    }

    if request.method == "POST":
        new_plan    = request.form.get("plan", "").strip()
        new_status  = request.form.get("status", "").strip()
        max_drivers = request.form.get("max_drivers", "").strip()
        notes       = request.form.get("notes", "").strip()
        trial_ends  = request.form.get("trial_ends_at", "").strip()

        if new_plan not in PLAN_LIMITS:
            flash("Invalid plan.", "error")
            conn.close()
            return redirect(url_for("superadmin_edit_company", company_id=company_id))
        if new_status not in ("active", "suspended", "cancelled"):
            flash("Invalid status.", "error")
            conn.close()
            return redirect(url_for("superadmin_edit_company", company_id=company_id))

        # default max_drivers from plan if not overridden
        try:
            max_d = int(max_drivers) if max_drivers else PLAN_LIMITS[new_plan]
        except ValueError:
            max_d = PLAN_LIMITS[new_plan]

        # set trial_ends_at only for trial plan
        t_ends = trial_ends if (new_plan == "trial" and trial_ends) else None

        conn.execute(
            """UPDATE companies SET subscription_plan=?, subscription_status=?,
               max_drivers=?, trial_ends_at=? WHERE id=?""",
            (new_plan, new_status, max_d, t_ends, company_id)
        )
        # record in subscription history
        conn.execute(
            """INSERT INTO subscriptions (company_id, plan, status, started_at, notes, created_at)
               VALUES (?,?,?,?,?,?)""",
            (company_id, new_plan, new_status, now_ts(),
             notes or f"Updated by superadmin", now_ts())
        )
        conn.commit()
        conn.close()
        flash(f"Company updated to {new_plan} / {new_status}.", "success")
        return redirect(url_for("superadmin_panel"))

    conn.close()

    plan_options = ""
    for p in ("trial", "starter", "pro", "enterprise"):
        sel = " selected" if p == co["subscription_plan"] else ""
        plan_options += f'<option value="{p}"{sel}>{p.title()}</option>'

    status_options = ""
    for s in ("active", "suspended", "cancelled"):
        sel = " selected" if s == co["subscription_status"] else ""
        status_options += f'<option value="{s}"{sel}>{s.title()}</option>'

    body = f"""
    <div class="hero">
        <h1>Edit Company: {e(co['name'])}</h1>
        <p>Change subscription plan, status, and seat limits.</p>
    </div>
    <div class="card" style="max-width:560px;">
        <form method="POST">
            <label>Plan</label>
            <select name="plan">{plan_options}</select>

            <label>Status</label>
            <select name="status">{status_options}</select>

            <label>Max Drivers <span class="muted small">(leave blank to use plan default)</span></label>
            <input name="max_drivers" type="number" min="1" value="{e(str(co['max_drivers']))}">

            <label>Trial Ends At <span class="muted small">(only applies to trial plan — YYYY-MM-DD HH:MM:SS)</span></label>
            <input name="trial_ends_at" value="{e(co['trial_ends_at'] or '')}">

            <label>Notes <span class="muted small">(recorded in subscription history)</span></label>
            <input name="notes" placeholder="e.g. Upgraded via Stripe payment">

            <div style="margin-top:14px;" class="row">
                <button type="submit" class="btn green">Save Changes</button>
                <a class="btn secondary" href="{url_for('superadmin_panel')}">Cancel</a>
            </div>
        </form>
    </div>
    """
    return render_template_string(shell_page("Edit Company", body))


# =========================================================
# PRIVACY POLICY
# =========================================================
@app.route("/privacy")
def privacy_policy():
    today = datetime.now().strftime("%B %d, %Y")
    body = f"""
    <div class="hero">
        <h1>Privacy Policy</h1>
        <p class="muted small">Effective date: <strong style="color:#e0f0ff;">{today}</strong>
        &nbsp;&middot;&nbsp; HAULTRA AI SYSTEMS &nbsp;&middot;&nbsp; Virginia, USA</p>
    </div>

    <div class="card" style="max-width:820px;line-height:1.8;">

        <div style="background:rgba(63,210,255,0.07);border:1px solid rgba(63,210,255,0.18);
                    border-radius:10px;padding:14px 18px;margin-bottom:24px;font-size:14px;">
            This policy describes how <strong>HAULTRA AI SYSTEMS</strong>, headquartered in
            <strong>Virginia, USA</strong>, collects, uses, and protects your information when
            you use our dispatch and route management platform. Please read it carefully before
            creating an account.
        </div>

        <h2>1. Who We Are</h2>
        <p>HAULTRA AI SYSTEMS ("HAULTRA", "we", "our", "us") is a software company incorporated
        in the Commonwealth of Virginia, United States. We provide dispatch and route management
        software built for the hauling and roll-off trucking industry. Our registered mailing
        address for privacy matters is:</p>
        <p style="margin-left:18px;color:#9dc8f0;">
            HAULTRA AI SYSTEMS<br>
            Virginia, USA<br>
            <a href="mailto:info@haultraai.com">info@haultraai.com</a>
        </p>

        <h2>2. Age Requirement</h2>
        <p>You must be at least <strong>18 years of age</strong> to create an account or use the
        HAULTRA platform. By registering, you represent and warrant that you are 18 or older. We
        do not knowingly collect personal information from anyone under 18. If we become aware that
        a user is under 18, we will promptly close the account and delete associated data.</p>

        <h2>3. Information We Collect</h2>
        <ul>
            <li><strong>Account data</strong> — company name, owner name, username, and password
            (stored as a bcrypt hash; we never store your plaintext password).</li>
            <li><strong>Operational data</strong> — routes, stops, customer addresses, order notes,
            and driver assignments you enter into the system.</li>
            <li><strong>Photos</strong> — images uploaded by drivers at job sites, stored on our
            servers and associated only with your company account.</li>
            <li><strong>Billing data</strong> — subscription plan selections and plan change history.
            We do not currently store credit card numbers directly; payment processing is handled
            by contracted processors under their own privacy policies.</li>
            <li><strong>Usage data</strong> — standard server logs including IP addresses, browser
            type, and pages visited, used solely for security and diagnostics.</li>
        </ul>

        <h2>4. How We Use Your Information</h2>
        <ul>
            <li>To provision and operate your HAULTRA company account.</li>
            <li>To authenticate users and enforce role-based access controls.</li>
            <li>To process and manage your subscription plan and billing status.</li>
            <li>To send transactional communications (account notices, trial expiry alerts,
            support replies).</li>
            <li>To improve the service — we analyze aggregated, anonymized usage patterns only
            and never sell individual data for advertising.</li>
        </ul>

        <h2>5. Billing and Subscription Data</h2>
        <p>When you select a paid subscription plan (Starter, Pro, or Enterprise), we record your
        plan type, activation date, and plan change history in our systems. This information is
        used to enforce access controls and maintain an audit trail for your account. Billing
        inquiries and disputes should be directed to
        <a href="mailto:info@haultraai.com">info@haultraai.com</a>.</p>
        <ul>
            <li>Trial accounts expire after 14 days. No payment data is collected during the
            free trial.</li>
            <li>Subscription records are retained for 7 years for accounting and legal compliance
            purposes, even after account cancellation.</li>
            <li>Payment card data is processed by our payment processor and is never stored on
            HAULTRA servers.</li>
        </ul>

        <h2>6. Account Responsibility</h2>
        <p>You are responsible for all activity that occurs under your company account, including
        actions taken by drivers and other users you add. Specifically:</p>
        <ul>
            <li>Keep your credentials confidential and do not share your password.</li>
            <li>Notify us immediately at <a href="mailto:info@haultraai.com">info@haultraai.com</a>
            if you suspect unauthorized access to your account.</li>
            <li>You are responsible for ensuring that users you add to your account (drivers,
            dispatchers) are authorized to access your company data.</li>
            <li>You must not add users who are under 18 years of age.</li>
            <li>HAULTRA is not liable for losses caused by unauthorized account access resulting
            from your failure to maintain credential security.</li>
        </ul>

        <h2>7. Data Isolation</h2>
        <p>Every company on HAULTRA operates in a fully isolated data environment. Your routes,
        drivers, orders, and uploaded photos are never visible to other companies on the platform.
        Technical access controls enforce this at the database layer on every request.</p>

        <h2>8. International Data Processing</h2>
        <p>HAULTRA is based in Virginia, USA, and your data is stored and processed on servers
        located in the United States. If you access the platform from outside the United States,
        your information will be transferred to and processed in the US, where data protection
        laws may differ from those in your country.</p>
        <p>For users in the European Economic Area (EEA), United Kingdom, or other jurisdictions
        with data transfer restrictions, we rely on Standard Contractual Clauses (SCCs) or
        equivalent mechanisms as the legal basis for transferring personal data to the US.
        By using the platform, you acknowledge and consent to this transfer. To inquire about
        our data transfer mechanisms, contact
        <a href="mailto:info@haultraai.com">info@haultraai.com</a>.</p>

        <h2>9. Third-Party Services</h2>
        <p>We use Nominatim (OpenStreetMap) for address geocoding. Stop addresses submitted for
        route optimization are sent to this service. No account credentials or driver names are
        included. We do not sell or rent your data to any third party for marketing purposes.</p>

        <h2>10. Data Retention</h2>
        <p>Your operational data (routes, stops, photos) is retained for as long as your account
        is active. Upon cancellation you may request a full export within 30 days, after which
        operational data is deleted from production systems. Backups are purged within 90 days.
        Billing and subscription records are retained for 7 years per section 5 above.</p>

        <h2>11. Security</h2>
        <p>All data is transmitted over HTTPS/TLS. Passwords are hashed with bcrypt. Sessions
        use cryptographically signed cookies with CSRF protection on all state-changing requests.
        We perform regular internal security reviews.</p>

        <h2>12. Your Rights</h2>
        <p>You may request access to, correction of, or deletion of your personal data at any
        time by contacting <a href="mailto:info@haultraai.com">info@haultraai.com</a>. We will
        respond within 30 days. Residents of California (CCPA) and the EEA/UK (GDPR) have
        additional rights including portability and the right to object to processing — contact
        us to exercise these rights.</p>

        <h2>13. Changes to This Policy</h2>
        <p>We will post updates to this page with a revised effective date. For material changes,
        we will notify account owners by email at least 14 days before the change takes effect.
        Continued use of the Service after the effective date constitutes acceptance.</p>

        <h2>14. Contact</h2>
        <p>
            Privacy questions: <a href="mailto:info@haultraai.com">info@haultraai.com</a><br>
            Billing questions: <a href="mailto:info@haultraai.com">info@haultraai.com</a><br>
            Security concerns: <a href="mailto:info@haultraai.com">info@haultraai.com</a>
        </p>

        <div style="margin-top:28px;padding-top:16px;border-top:1px solid rgba(100,160,220,0.15);
                    font-size:12px;color:#6a9bc0;">
            &copy; {datetime.now().year} HAULTRA AI SYSTEMS &mdash; Virginia, USA.
            All rights reserved.
        </div>
    </div>
    """
    return render_template_string(shell_page("Privacy Policy", body))


# =========================================================
# TERMS OF SERVICE
# =========================================================
@app.route("/terms")
def terms_of_service():
    today = datetime.now().strftime("%B %d, %Y")
    year  = datetime.now().year
    body = f"""
    <div class="hero">
        <h1>Terms of Service</h1>
        <p class="muted small">Effective date: <strong style="color:#e0f0ff;">{today}</strong>
        &nbsp;&middot;&nbsp; HAULTRA AI SYSTEMS &nbsp;&middot;&nbsp; Virginia, USA</p>
    </div>

    <div class="card" style="max-width:820px;line-height:1.8;">

        <div style="background:rgba(63,210,255,0.07);border:1px solid rgba(63,210,255,0.18);
                    border-radius:10px;padding:14px 18px;margin-bottom:24px;font-size:14px;">
            Welcome to <strong>HAULTRA Systems</strong> ("HAULTRA", "we", "our", "us"). By
            accessing or using our platform, you agree to these Terms of Service. If you do
            not agree, do not use the platform.
        </div>

        <h2>1. Use of Service</h2>
        <p>HAULTRA provides dispatch, routing, and operational management software for trucking
        and hauling businesses. You agree to use the platform only for lawful business purposes
        and in compliance with all applicable federal, state, and local laws.</p>

        <h2>2. Accounts</h2>
        <ul>
            <li>You are responsible for maintaining the security of your account credentials.</li>
            <li>You must provide accurate and complete information when registering.</li>
            <li>You are responsible for all activity that occurs under your account.</li>
            <li>Notify us immediately at
            <a href="mailto:info@haultraai.com">info@haultraai.com</a> if you suspect
            unauthorized access.</li>
        </ul>

        <h2>3. Company Accounts (Multi-Tenant)</h2>
        <p>Each company account operates independently. You are responsible for managing your
        users (drivers, dispatchers, etc.) and their level of access within your account.</p>
        <p>HAULTRA is not responsible for actions taken by users within your company account.
        You bear full responsibility for ensuring your users comply with these Terms.</p>

        <h2>4. Subscriptions &amp; Billing</h2>
        <ul>
            <li>Certain features require a paid subscription (Starter, Pro, or Enterprise).</li>
            <li>New accounts receive a <strong>14-day free trial</strong> with up to 5 driver
            seats — no credit card required.</li>
            <li>Subscription fees are billed on a recurring monthly basis unless canceled.</li>
            <li>Failure to maintain an active subscription may result in restricted or suspended
            access. Data is retained for 30 days after suspension before permanent deletion.</li>
            <li>All payments are <strong>non-refundable</strong> unless otherwise required by
            applicable law.</li>
            <li>Prices are subject to change with 30 days' advance notice to account owners.</li>
        </ul>

        <h2>5. Data &amp; Content</h2>
        <p>You retain full ownership of your data, including routes, customer information,
        driver records, and uploaded images. By using HAULTRA, you grant us a limited,
        non-exclusive license to store and process your data solely to provide the Service.</p>
        <p>You are responsible for ensuring you have the legal right to upload and use any
        data, addresses, or images submitted to the platform.</p>

        <h2>6. Acceptable Use</h2>
        <p>You agree <strong>not</strong> to:</p>
        <ul>
            <li>Use the platform for any illegal, fraudulent, or unauthorized purpose.</li>
            <li>Attempt to hack, probe, disrupt, or reverse-engineer the system or its
            underlying infrastructure.</li>
            <li>Access or attempt to access another company's data without authorization.</li>
            <li>Upload or transmit harmful, malicious, or offensive content.</li>
            <li>Resell or sublicense access to the Service without written consent from
            HAULTRA.</li>
        </ul>

        <h2>7. Service Availability</h2>
        <p>We aim to provide reliable, uninterrupted service but do not guarantee 100% uptime.
        HAULTRA may be temporarily unavailable due to scheduled maintenance, technical issues,
        or circumstances beyond our control. Scheduled maintenance windows will be announced
        in advance when possible.</p>

        <h2>8. Limitation of Liability</h2>
        <p>THE SERVICE IS PROVIDED "AS IS" WITHOUT WARRANTIES OF ANY KIND, EXPRESS OR IMPLIED.
        TO THE MAXIMUM EXTENT PERMITTED BY LAW, HAULTRA SHALL NOT BE LIABLE FOR:</p>
        <ul>
            <li>Business losses or lost profits</li>
            <li>Data loss or corruption</li>
            <li>Service interruptions or downtime</li>
            <li>Indirect, incidental, special, or consequential damages</li>
        </ul>
        <p>OUR AGGREGATE LIABILITY SHALL NOT EXCEED THE AMOUNTS PAID BY YOU IN THE PRIOR
        THREE (3) MONTHS.</p>

        <h2>9. Termination</h2>
        <p>We may suspend or terminate accounts that violate these Terms, with or without
        prior notice. You may cancel your account at any time by contacting us at
        <a href="mailto:info@haultraai.com">info@haultraai.com</a>. Upon cancellation,
        your data will be retained for 30 days before permanent deletion.</p>

        <h2>10. Changes to Terms</h2>
        <p>We may update these Terms at any time. We will post the revised Terms with an
        updated effective date. Continued use of the platform after the effective date
        constitutes your acceptance of the updated Terms.</p>

        <h2>11. Governing Law</h2>
        <p>These Terms are governed by the laws of the <strong>State of Virginia,
        United States</strong>, without regard to conflict-of-law principles. Any disputes
        shall be resolved in the courts of Virginia.</p>

        <h2>12. Contact</h2>
        <p>Questions about these Terms? Contact us at:<br>
        <a href="mailto:info@haultraai.com">info@haultraai.com</a><br>
        HAULTRA AI SYSTEMS &mdash; Virginia, USA</p>

        <div style="margin-top:28px;padding-top:16px;border-top:1px solid rgba(100,160,220,0.15);
                    font-size:12px;color:#6a9bc0;">
            &copy; {year} HAULTRA AI SYSTEMS &mdash; Virginia, USA. All rights reserved.
        </div>
    </div>
    """
    return render_template_string(shell_page("Terms of Service", body))


# =========================================================
# DUMP LOCATIONS
# =========================================================
@app.route("/dump-locations")
@boss_required
def dump_locations_page():
    conn = get_db()
    locs = conn.execute(
        "SELECT * FROM dump_locations ORDER BY active DESC, name ASC"
    ).fetchall()
    conn.close()

    rows = ""
    for dl in locs:
        addr = ", ".join(p for p in [dl["address"], dl["city"], dl["state"], dl["zip_code"]] if p)
        active_badge = (
            '<span class="badge completed">Active</span>'
            if dl["active"]
            else '<span class="badge" style="opacity:0.5;">Inactive</span>'
        )
        toggle_label = "Deactivate" if dl["active"] else "Activate"
        toggle_style = (
            'background:transparent;color:#fbbf24;border:1px solid rgba(251,191,36,0.4);'
            'border-radius:6px;padding:3px 10px;font-size:11px;cursor:pointer;'
        ) if dl["active"] else (
            'background:transparent;color:#4ade80;border:1px solid rgba(74,222,128,0.4);'
            'border-radius:6px;padding:3px 10px;font-size:11px;cursor:pointer;'
        )
        _dlid   = dl["id"]
        _dlname = e(dl["name"])
        rows += f"""
        <tr>
            <td><strong>{_dlname}</strong></td>
            <td class="muted small">{e(addr)}</td>
            <td class="muted small">{e(dl['notes'] or '')}</td>
            <td>{active_badge}</td>
            <td style="text-align:right;white-space:nowrap;">
                <a href="{url_for('edit_dump_location', loc_id=_dlid)}"
                   style="color:#3fd2ff;font-size:12px;margin-right:10px;">Edit</a>
                <form method="POST" action="{url_for('toggle_dump_location', loc_id=_dlid)}" style="display:inline;">
                    <button type="submit" style="{toggle_style}">{toggle_label}</button>
                </form>
                <form method="POST" action="{url_for('delete_dump_location', loc_id=_dlid)}" style="display:inline;margin-left:6px;"
                      onsubmit="return confirm('Delete {_dlname}?');">
                    <button type="submit"
                       style="background:transparent;color:#f87171;border:1px solid rgba(248,113,113,0.4);
                              border-radius:6px;padding:3px 10px;font-size:11px;cursor:pointer;">Delete</button>
                </form>
            </td>
        </tr>"""

    body = f"""
    <div class="hero">
        <h1>Dump Locations</h1>
        <p>Manage the disposal sites available for route assignment.</p>
    </div>
    <div class="card">
        <div class="row between" style="margin-bottom:16px;">
            <h2 style="margin:0;">All Locations</h2>
            <a class="btn" href="{url_for('add_dump_location')}">+ Add Location</a>
        </div>
        <div class="table-wrap">
            <table>
                <thead>
                    <tr><th>Name</th><th>Address</th><th>Notes</th><th>Status</th><th style="width:200px;"></th></tr>
                </thead>
                <tbody>
                    {rows or '<tr><td colspan="5" class="muted">No dump locations found.</td></tr>'}
                </tbody>
            </table>
        </div>
    </div>
    """
    return render_template_string(shell_page("Dump Locations", body))


@app.route("/dump-locations/add", methods=["GET", "POST"])
@boss_required
def add_dump_location():
    if request.method == "POST":
        name     = request.form.get("name", "").strip()
        address  = request.form.get("address", "").strip()
        city     = request.form.get("city", "").strip()
        state    = request.form.get("state", "").strip()
        zip_code = request.form.get("zip_code", "").strip()
        notes    = request.form.get("notes", "").strip()

        if not name:
            flash("Location name is required.", "error")
            return redirect(url_for("add_dump_location"))

        conn = get_db()
        conn.execute(
            "INSERT INTO dump_locations (name, address, city, state, zip_code, notes, active, created_at) VALUES (?,?,?,?,?,?,1,?)",
            (name, address, city, state, zip_code, notes, now_ts())
        )
        conn.commit()
        conn.close()
        flash(f"Dump location '{name}' added.", "success")
        return redirect(url_for("dump_locations_page"))

    body = """
    <div class="hero"><h1>Add Dump Location</h1></div>
    <div class="card" style="max-width:560px;">
        <form method="POST">
            <label>Name *</label>
            <input name="name" required placeholder="e.g. Bay">
            <label>Address</label>
            <input name="address" placeholder="Street address">
            <div class="grid">
                <div><label>City</label><input name="city"></div>
                <div><label>State</label><input name="state" value="VA" maxlength="2"></div>
                <div><label>ZIP</label><input name="zip_code" maxlength="10"></div>
            </div>
            <label>Notes</label>
            <textarea name="notes" placeholder="Any special instructions..."></textarea>
            <div style="margin-top:12px;display:flex;gap:10px;">
                <button type="submit">Save Location</button>
                <a class="btn secondary" href="/dump-locations">Cancel</a>
            </div>
        </form>
    </div>
    """
    return render_template_string(shell_page("Add Dump Location", body))


@app.route("/dump-locations/<int:loc_id>/edit", methods=["GET", "POST"])
@boss_required
def edit_dump_location(loc_id):
    conn = get_db()
    dl = conn.execute("SELECT * FROM dump_locations WHERE id=?", (loc_id,)).fetchone()
    if not dl:
        conn.close()
        flash("Location not found.", "error")
        return redirect(url_for("dump_locations_page"))

    if request.method == "POST":
        name     = request.form.get("name", "").strip()
        address  = request.form.get("address", "").strip()
        city     = request.form.get("city", "").strip()
        state    = request.form.get("state", "").strip()
        zip_code = request.form.get("zip_code", "").strip()
        notes    = request.form.get("notes", "").strip()

        if not name:
            flash("Location name is required.", "error")
            conn.close()
            return redirect(url_for("edit_dump_location", loc_id=loc_id))

        conn.execute(
            "UPDATE dump_locations SET name=?, address=?, city=?, state=?, zip_code=?, notes=? WHERE id=?",
            (name, address, city, state, zip_code, notes, loc_id)
        )
        conn.commit()
        conn.close()
        flash("Location updated.", "success")
        return redirect(url_for("dump_locations_page"))

    conn.close()
    body = f"""
    <div class="hero"><h1>Edit Dump Location</h1></div>
    <div class="card" style="max-width:560px;">
        <form method="POST">
            <label>Name *</label>
            <input name="name" required value="{e(dl['name'])}">
            <label>Address</label>
            <input name="address" value="{e(dl['address'] or '')}">
            <div class="grid">
                <div><label>City</label><input name="city" value="{e(dl['city'] or '')}"></div>
                <div><label>State</label><input name="state" value="{e(dl['state'] or 'VA')}" maxlength="2"></div>
                <div><label>ZIP</label><input name="zip_code" value="{e(dl['zip_code'] or '')}" maxlength="10"></div>
            </div>
            <label>Notes</label>
            <textarea name="notes">{e(dl['notes'] or '')}</textarea>
            <div style="margin-top:12px;display:flex;gap:10px;">
                <button type="submit">Save Changes</button>
                <a class="btn secondary" href="{url_for('dump_locations_page')}">Cancel</a>
            </div>
        </form>
    </div>
    """
    return render_template_string(shell_page("Edit Dump Location", body))


@app.route("/dump-locations/<int:loc_id>/toggle", methods=["POST"])
@boss_required
def toggle_dump_location(loc_id):
    conn = get_db()
    dl = conn.execute("SELECT active, name FROM dump_locations WHERE id=?", (loc_id,)).fetchone()
    if not dl:
        conn.close()
        flash("Location not found.", "error")
        return redirect(url_for("dump_locations_page"))
    new_active = 0 if dl["active"] else 1
    conn.execute("UPDATE dump_locations SET active=? WHERE id=?", (new_active, loc_id))
    conn.commit()
    conn.close()
    status_word = "activated" if new_active else "deactivated"
    flash(f"'{dl['name']}' {status_word}.", "success")
    return redirect(url_for("dump_locations_page"))


@app.route("/dump-locations/<int:loc_id>/delete", methods=["POST"])
@boss_required
def delete_dump_location(loc_id):
    conn = get_db()
    dl = conn.execute("SELECT name FROM dump_locations WHERE id=?", (loc_id,)).fetchone()
    if not dl:
        conn.close()
        flash("Location not found.", "error")
        return redirect(url_for("dump_locations_page"))
    # Unlink from any routes that reference this location
    conn.execute("UPDATE routes SET dump_location_id=NULL WHERE dump_location_id=?", (loc_id,))
    conn.execute("DELETE FROM dump_locations WHERE id=?", (loc_id,))
    conn.commit()
    conn.close()
    flash(f"'{dl['name']}' deleted.", "success")
    return redirect(url_for("dump_locations_page"))


# =========================================================
# RUN APP
# =========================================================
if __name__ == "__main__":
    debug = os.environ.get("FLASK_DEBUG", "0") == "1"
    port  = int(os.environ.get("PORT", 5000))
    app.run(host="0.0.0.0", port=port, debug=debug)