"""Cans on site must come from both real records, not a parsed note.

2026-10-31, from the Customers list on the iPad: live job sites reading
"0 cans on site" when a container was physically there.

The count came from the fleet table alone, where a can's customer is PARSED
OUT OF A FREE-TEXT NOTE (_fleet_site_of). Three of the note shapes that
function handles carry no customer at all:

    'On site at ADDR (Bin Tracker)'     -> site only
    'Placed <date> — Site'              -> site only
    'Bulk deployed … — via Deploy all'  -> neither

so a can on a job site was attributed to nobody and its customer read 0.

The fix reads both records that actually know: the fleet knows each physical
can, and the daily log (completed stops) knows which customer holds a can at
which address.

The assertions that matter most are the ones proving it does NOT invent: a
customer whose can was pulled still reads 0, because for a finished job that
is the correct answer.

Run:  python3 tests/test_cans_on_site_attribution.py
"""
import os
import sys
import tempfile
import importlib

TMP = tempfile.mkdtemp(prefix="haultra-cans-")
os.environ["DATABASE_PATH"] = os.path.join(TMP, "c.db")
os.environ["SECRET_KEY"] = "c"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")

FAILURES = []


def ok(cond, label):
    print(("PASS" if cond else "FAIL") + " - " + label, flush=True)
    if not cond:
        FAILURES.append(label)


app.init_db()
conn = app.get_db()
cur = conn.cursor()
ts = app.now_ts()
today = app.today_str()
cur.execute("INSERT INTO companies (name, slug, subscription_plan, subscription_status,"
            " max_drivers, created_at) VALUES (?,?,?,?,?,?)",
            ("Cans Co", "cansco", "pro", "active", 10, ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
            " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
            ("cboss", "x", "boss", "C Boss", co, ts))
boss = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
            " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
            ("cdrv", "x", "driver", "C Driver", co, ts))
drv = cur.lastrowid
cur.execute("INSERT INTO routes (company_id, route_date, route_name, created_by,"
            " assigned_to, status, created_at) VALUES (?,?,?,?,?,'completed',?)",
            (co, today, "Cans route", boss, drv, ts))
rid = cur.lastrowid
conn.commit()


def mkstop(action, customer, address, size="30yd", completed=True):
    cur.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address, city,
                   state, action, container_size, status, completed_at, created_at)
                   VALUES (?,?,?,?, 'Norfolk','VA',?,?,?,?,?)""",
                (rid, 0, customer, address, action, size,
                 "completed" if completed else "open",
                 ts if completed else None, ts))
    conn.commit()
    return cur.lastrowid


def mkcan(label, notes, status="deployed"):
    cur.execute("INSERT INTO containers (company_id, label, size, status, notes, created_at)"
                " VALUES (?,?,?,?,?,?)", (co, label, "30yd", status, notes, ts))
    conn.commit()
    return cur.lastrowid


def mkcust(name):
    import secrets as _s
    cur.execute("INSERT INTO customers (company_id, business_name, contact_name, phone,"
                " portal_token, is_active, created_at) VALUES (?,?,?,?,?,1,?)",
                (co, name, name, "7575550000", _s.token_hex(12), ts))
    conn.commit()
    return cur.lastrowid


# ── The three situations on the real board ─────────────────────────
# A: fleet note NAMES the customer — worked before, must keep working.
mkcust("757 Restoration")
mkstop("Delivery", "757 Restoration", "100 Resto Way")
mkcan("3001", "Returned %s — 757 Restoration, 100 Resto Way" % today)

# B: fleet note names only the SITE (Bin Tracker / Placed). This is the bug:
#    a can is physically there, attributed to nobody.
mkcust("Adrian Tile")
mkstop("Delivery", "Adrian Tile", "200 Tile Rd")
mkcan("3002", "On site at 200 Tile Rd (Bin Tracker)")

mkcust("AMERICAN MARINE")
mkstop("Delivery", "AMERICAN MARINE", "300 Marine Blvd")
mkcan("3003", "Placed %s — 300 Marine Blvd" % today)

# C: the customer holds a can per the log, but the fleet has no row at all.
mkcust("BRICKNER")
mkstop("Delivery", "BRICKNER", "400 Brick St")

# D: FINISHED job — delivered, then pulled. Must stay 0.
mkcust("Finished Co")
mkstop("Delivery", "Finished Co", "500 Done Ln")
mkstop("Pull", "Finished Co", "500 Done Ln")

# E: a customer who never had anything. Must stay 0.
mkcust("Never Had One")

counts = app._cans_on_site_by_customer(conn, co)


def n(name):
    return counts.get(app._norm_cust_key(name), 0)


print("\n-- already worked, must not regress --")
ok(n("757 Restoration") == 1,
   "a fleet can whose note names the customer still counts (got %d)" % n("757 Restoration"))

print("\n-- the reported bug: a can on site attributed to nobody --")
ok(n("Adrian Tile") == 1,
   "a Bin Tracker can is attributed through the daily log (got %d)" % n("Adrian Tile"))
ok(n("AMERICAN MARINE") == 1,
   "a 'Placed — site' can is attributed too (got %d)" % n("AMERICAN MARINE"))

print("\n-- the fleet has no row at all --")
ok(n("BRICKNER") == 1,
   "the daily log alone still shows the can (got %d)" % n("BRICKNER"))

print("\n-- and it must NOT invent --")
ok(n("Finished Co") == 0,
   "a pulled can reads 0, because the job is done (got %d)" % n("Finished Co"))
ok(n("Never Had One") == 0,
   "a customer who never had one reads 0 (got %d)" % n("Never Had One"))

print("\n-- no double counting --")
# The same customer, named in the fleet AND present in the log, counts once.
mkcust("Double Co")
mkstop("Delivery", "Double Co", "600 Twice Ave")
mkcan("3004", "Returned %s — Double Co, 600 Twice Ave" % today)
counts = app._cans_on_site_by_customer(conn, co)
ok(n("Double Co") == 1,
   "a can known to both records counts once, not twice (got %d)" % n("Double Co"))

print("\n-- two cans at one site --")
mkcust("Two Can Co")
mkstop("Delivery", "Two Can Co", "700 Pair St")
mkcan("3005", "Returned %s — Two Can Co, 700 Pair St" % today)
mkcan("3006", "Returned %s — Two Can Co, 700 Pair St" % today)
counts = app._cans_on_site_by_customer(conn, co)
ok(n("Two Can Co") == 2, "two cans at one site count as two (got %d)" % n("Two Can Co"))

print("\n-- the page renders it --")
app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=boss, company_id=co, role="boss",
             roles=["boss", "owner", "customer_manager"], _csrf_token="tok")
r = cl.get("/customers")
html = r.get_data(as_text=True)
ok(r.status_code == 200, "the customers page renders (got %d)" % r.status_code)
_seg = html.split("Adrian Tile", 1)[1][:400] if "Adrian Tile" in html else ""
ok("0 cans on site" not in _seg,
   "Adrian Tile no longer reads 0 cans on site")
_fin = html.split("Finished Co", 1)[1][:400] if "Finished Co" in html else ""
ok("0 cans on site" in _fin, "a finished job still correctly reads 0")

print("\n%d failure(s)" % len(FAILURES))
for f in FAILURES:
    print("  FAILED: " + f)
sys.exit(1 if FAILURES else 0)
