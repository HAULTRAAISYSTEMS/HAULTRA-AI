"""All-done screen: a "Navigate to Yard" button must appear once every stop is
done, honoring the driver's nav preference, built from the company's yard
address in Company Settings. When no yard address is set, a muted hint shows
instead of a broken link.

Run:  ~/workspace/.haultra-venv/bin/python tests/test_yard_nav.py
"""
import os
import sys
import tempfile
import urllib.parse

TMPDIR = tempfile.mkdtemp(prefix="haultra-yardnav-")
os.environ["DATABASE_PATH"] = os.path.join(TMPDIR, "yardnav.db")
os.environ["SECRET_KEY"] = "testsecret123"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMPDIR, "uploads")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import app  # noqa: E402

FAILURES = []


def ok(cond, label):
    print(("PASS" if cond else "FAIL") + " - " + label, flush=True)
    if not cond:
        FAILURES.append(label)


# ── Seed ───────────────────────────────────────────────────────────────
app.init_db()
conn = app.get_db()
cur = conn.cursor()
ts = app.now_ts()
today = app.today_str()
cur.execute(
    "INSERT INTO companies (name, slug, subscription_plan, subscription_status,"
    " max_drivers, created_at) VALUES (?,?,?,?,?,?)",
    ("Yard Co", "yardco", "pro", "active", 10, ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, company_id, created_at)"
            " VALUES (?,?,?,?,?)", ("y_boss", "x", "boss", co, ts))
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id, created_at)"
            " VALUES (?,?,?,?,?,?)", ("y_drv", "x", "driver", "Yara", co, ts))
drv = cur.lastrowid


def mkroute(name, yard_addr=None, yard_city=None, yard_state=None, yard_zip=None,
            nav_pref=""):
    if yard_addr is None and yard_city is None:
        cur.execute(
            "UPDATE companies SET yard_address=NULL, yard_city=NULL,"
            " yard_state=NULL, yard_zip=NULL WHERE id=?", (co,))
    else:
        cur.execute(
            "UPDATE companies SET yard_address=?, yard_city=?, yard_state=?,"
            " yard_zip=? WHERE id=?", (yard_addr, yard_city, yard_state, yard_zip, co))
    cur.execute("INSERT INTO routes (company_id, route_date, route_name, created_by,"
                " assigned_to, status, started_at, created_at)"
                " VALUES (?,?,?,?,?,'completed',?,?)",
                (co, today, name, drv, drv, ts, ts))
    cur.execute("UPDATE users SET nav_preference=? WHERE id=?", (nav_pref, drv))
    rid = cur.lastrowid
    for i, nm in enumerate(("Stop A", "Stop B")):
        cur.execute(
            "INSERT INTO stops (route_id, stop_order, customer_name, address, city,"
            " state, action, container_size, status, driver_status, created_at)"
            " VALUES (?,?,?,?,?,'VA','Pickup and Return','30yd',"
            " 'completed','completed',?)",
            (rid, i + 1, nm, "%d Test Way" % (i + 1), "Virginia Beach", ts))
    conn.commit()
    return rid


app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=drv, company_id=co, role="driver", _csrf_token="tok")


def get_alldone(rid, ua=None):
    hdrs = {}
    if ua:
        hdrs["User-Agent"] = ua
    return cl.get("/driver/route/%d" % rid, headers=hdrs)


# ── 1. Yard set, no nav preference → plain Google web link ──────────────
r1 = mkroute("Y1", yard_addr="100 Industrial Blvd", yard_city="Virginia Beach",
             yard_state="VA", yard_zip="23452")
r = get_alldone(r1)
ok(r.status_code == 200, "all-done page renders (yard set, no pref)")
html = r.get_data(as_text=True)
ok("Navigate to Yard" in html, "Navigate to Yard button present")
want = ("https://www.google.com/maps/dir/?api=1&amp;destination="
        + urllib.parse.quote_plus("100 Industrial Blvd, Virginia Beach, VA, 23452"))
ok(want in html, "no-pref yard link is the Google web fallback URL")

# ── 2. Yard missing → muted hint, no button ─────────────────────────────
r2 = mkroute("Y2")
r = get_alldone(r2)
html = r.get_data(as_text=True)
ok("Navigate to Yard" not in html, "no yard button when yard address unset")
ok("Yard address not set" in html, "muted hint shown when yard unset")

# ── 3. nav_preference=google ────────────────────────────────────────────
r3 = mkroute("Y3", yard_addr="9 Yard Rd", yard_city="Norfolk", yard_state="VA",
             nav_pref="google")
r = get_alldone(r3)
html = r.get_data(as_text=True)
ok("https://maps.google.com/?daddr=" + urllib.parse.quote_plus("9 Yard Rd, Norfolk, VA") in html,
   "google pref → maps.google.com daddr link")

# ── 4. nav_preference=apple ─────────────────────────────────────────────
r4 = mkroute("Y4", yard_addr="9 Yard Rd", yard_city="Norfolk", yard_state="VA",
             nav_pref="apple")
r = get_alldone(r4)
html = r.get_data(as_text=True)
ok("https://maps.apple.com/?daddr=" + urllib.parse.quote_plus("9 Yard Rd, Norfolk, VA") in html,
   "apple pref → maps.apple.com daddr link")

# ── 5. nav_preference=waze ──────────────────────────────────────────────
r5 = mkroute("Y5", yard_addr="9 Yard Rd", yard_city="Norfolk", yard_state="VA",
             nav_pref="waze")
r = get_alldone(r5)
html = r.get_data(as_text=True)
ok("https://waze.com/ul?q=" + urllib.parse.quote_plus("9 Yard Rd, Norfolk, VA")
   + "&amp;navigate=yes" in html, "waze pref → waze.com link")

# ── 6. device_default on iPhone → Apple Maps ────────────────────────────
r6 = mkroute("Y6", yard_addr="9 Yard Rd", yard_city="Norfolk", yard_state="VA",
             nav_pref="device_default")
r = get_alldone(r6, ua="Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X)")
html = r.get_data(as_text=True)
ok("https://maps.apple.com/?daddr=" + urllib.parse.quote_plus("9 Yard Rd, Norfolk, VA") in html,
   "device_default + iPhone UA → Apple Maps")

# ── 7. device_default on Android → geo: link ────────────────────────────
r = get_alldone(r6, ua="Mozilla/5.0 (Linux; Android 14; Pixel 8)")
html = r.get_data(as_text=True)
ok("geo:0,0?q=" + urllib.parse.quote_plus("9 Yard Rd, Norfolk, VA") in html,
   "device_default + Android UA → geo: link")

# ── 8. address HTML-escaped (no attribute breakout) ─────────────────────
r8 = mkroute("Y8", yard_addr='7 Yard "St"', yard_city="Norfolk", yard_state="VA")
r = get_alldone(r8)
html = r.get_data(as_text=True)
ok('7 Yard &quot;St&quot;' in html or "7+Yard+%22St%22" in html,
   "quote in yard address is escaped/encoded")

print()
if FAILURES:
    print("FAILURES: %d" % len(FAILURES))
    sys.exit(1)
print("all yard-nav checks passed")
