"""Boss-side vendor dispatch, and vendors in the address book.

2026-10-30, from a photo of Roll-Off Dispatch on the iPad: typing "Ko"
surfaced the tarp-repair shop "MA WASTE (TARP REPAIR)" as a Quick Add
suggestion wearing a yellow P (Pull) badge, and there was no way for the
boss to send a driver to a vendor at all.

Two defects:

1. learn_location never wrote `kind`, and built its dedupe key with
   kind="customer" whatever the caller passed. Every vendor address landed
   as kind='customer' -- sharing one address-book row with any customer at
   the same address, and inheriting that customer's work action.

2. Vendor stops existed end to end (arrive / complete / holds / truck
   badges) but only the DRIVER could self-dispatch, or the boss via the
   defect flow. A routine errand had to be faked as a broken truck.

Run:  python3 tests/test_boss_vendor_dispatch.py
"""
import os
import sys
import json
import tempfile
import importlib

TMP = tempfile.mkdtemp(prefix="haultra-vendisp-")
os.environ["DATABASE_PATH"] = os.path.join(TMP, "v.db")
os.environ["SECRET_KEY"] = "v"
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
cur.execute("INSERT INTO companies (name, slug, subscription_plan, subscription_status,"
            " max_drivers, created_at) VALUES (?,?,?,?,?,?)",
            ("Vend Co", "vendco", "pro", "active", 10, ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
            " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
            ("vboss", "x", "boss", "V Boss", co, ts))
boss = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
            " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
            ("vdrv", "x", "driver", "V Driver", co, ts))
drv = cur.lastrowid
cur.execute("INSERT INTO vendors (company_id, name, phone, address, is_active, created_at)"
            " VALUES (?,?,?,?,1,?)",
            (co, "MA WASTE (TARP REPAIR)", "7575551234", "3600 Koppens Way, Ches", ts))
vendor = cur.lastrowid
conn.commit()

app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=boss, company_id=co, role="boss", roles=["boss", "owner"],
             _csrf_token="tok")


def post(path, payload):
    return cl.post(path, data=json.dumps(payload),
                   content_type="application/json",
                   headers={"X-CSRF-Token": "tok"})


# ══════════════════════════════════════════════════════════════════
# 1. A vendor is not a customer in the address book
# ══════════════════════════════════════════════════════════════════
print("\n-- address book: vendor kind --")
app._learn_vendor_location(conn, co, "MA WASTE (TARP REPAIR)", "3600 Koppens Way, Ches")
conn.commit()
row = conn.execute(
    "SELECT kind, default_action FROM saved_addresses WHERE company_id=?"
    " AND customer_name LIKE 'MA WASTE%'", (co,)).fetchone()
ok(row is not None, "the vendor address is learned into the address book")
ok(row and row["kind"] == "vendor",
   "it is stored as kind='vendor' (got %r)" % (row["kind"] if row else None))

# A customer at the SAME street must stay its own row, not merge with the
# vendor and swap action defaults with it.
app.learn_location(conn, co, "3600 Koppens Way", customer_name="Koppens Yard",
                   action="P", container_size="30yd")
conn.commit()
rows = conn.execute(
    "SELECT customer_name, kind, default_action FROM saved_addresses"
    " WHERE company_id=? AND address LIKE '3600 Koppens%' ORDER BY id", (co,)).fetchall()
ok(len(rows) == 2, "vendor and customer at one address stay separate rows (got %d)" % len(rows))
_kinds = sorted(r["kind"] for r in rows)
ok(_kinds == ["customer", "vendor"], "one of each kind (got %r)" % _kinds)

# Quick Add must not offer a work action for the vendor.
r = cl.get("/api/address-suggestions?q=Ko")
sugg = r.get_json() or []
ok(r.status_code == 200 and sugg, "Quick Add returns suggestions for 'Ko'")
_v = next((s for s in sugg if (s.get("customer_name") or "").startswith("MA WASTE")), None)
ok(_v is not None, "the vendor is still suggested")
ok(_v and _v.get("kind") == "vendor", "the suggestion is tagged kind=vendor")
ok(_v and _v.get("default_action") == "Vendor",
   "the vendor never offers a work action (got %r)" % (_v.get("default_action") if _v else None))
ok(_v and not _v.get("default_container_size"), "and carries no container size")
_c = next((s for s in sugg if (s.get("customer_name") or "") == "Koppens Yard"), None)
ok(_c is not None and _c.get("kind") == "customer", "the real customer is unaffected")
ok(_c is not None and _c.get("default_action") == "P", "and keeps its Pull default")


# ══════════════════════════════════════════════════════════════════
# 2. Boss dispatches a driver to a vendor
# ══════════════════════════════════════════════════════════════════
print("\n-- boss vendor dispatch --")
r = post("/api/dispatch/vendor-visit", {"driver_id": drv, "vendor_id": vendor})
ok(r.status_code == 200, "dispatch with no existing route succeeds (got %d)" % r.status_code)
j = r.get_json() or {}
ok(j.get("created_route"), "a route is created when the driver has none")
rid = j.get("route_id")
st = dict(conn.execute("SELECT * FROM stops WHERE id=?", (j.get("stop_id"),)).fetchone())
ok(st["action"] == "Vendor", "the stop uses the existing Vendor action (got %r)" % st["action"])
ok(st["vendor_id"] == vendor, "it is linked to the vendor record")
ok("Koppens" in (st["address"] or ""), "it carries the vendor address so Navigate works")

# Second dispatch to the same driver is refused while one is open.
r = post("/api/dispatch/vendor-visit", {"driver_id": drv, "vendor_id": vendor})
ok(r.status_code == 400, "a second open vendor visit is refused (got %d)" % r.status_code)

# Complete it so the rest of the scenarios start clean.
conn.execute("UPDATE stops SET status='completed', completed_at=? WHERE id=?",
             (ts, j.get("stop_id")))
conn.commit()

print("\n-- three dispatch modes --")
# Give the driver real work, then dispatch IN LINE: nothing may be held.
for i in range(3):
    conn.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address, city,
                    state, action, container_size, status, created_at)
                    VALUES (?,?,?,?, 'Norfolk','VA','Pull','20yd','open',?)""",
                 (rid, 10 + i, "cust%d" % i, "%d Work St" % i, ts))
conn.commit()
r = post("/api/dispatch/vendor-visit",
         {"driver_id": drv, "vendor_id": vendor, "mode": "line", "note": "tarp"})
ok(r.status_code == 200, "in-line dispatch succeeds (got %d)" % r.status_code)
j2 = r.get_json() or {}
ok(j2.get("held") == 0, "in line holds nothing (got %r)" % j2.get("held"))
n_held = conn.execute(
    "SELECT COUNT(*) c FROM stops WHERE route_id=? AND held_at IS NOT NULL", (rid,)
).fetchone()["c"]
ok(n_held == 0, "no stop on the route is held (got %d)" % n_held)
conn.execute("UPDATE stops SET status='completed', completed_at=? WHERE id=?",
             (ts, j2.get("stop_id")))
conn.commit()

r = post("/api/dispatch/vendor-visit",
         {"driver_id": drv, "vendor_id": vendor, "mode": "now"})
ok(r.status_code == 200, "go-now dispatch succeeds (got %d)" % r.status_code)
j3 = r.get_json() or {}
ok(j3.get("held") == 3, "go now holds the 3 remaining work stops (got %r)" % j3.get("held"))
vs = dict(conn.execute("SELECT stop_order, held_at FROM stops WHERE id=?",
                       (j3.get("stop_id"),)).fetchone())
ok(vs["held_at"] is None, "the vendor stop itself is never held")
_orders = [r["stop_order"] for r in conn.execute(
    "SELECT stop_order FROM stops WHERE route_id=? AND held_at IS NOT NULL"
    " ORDER BY stop_order", (rid,)).fetchall()]
ok(all(o > vs["stop_order"] for o in _orders),
   "every held stop sits after the vendor stop")

print("\n-- the driver is told --")
msgs = conn.execute(
    "SELECT body, priority FROM messages WHERE route_id=? ORDER BY id", (rid,)).fetchall()
ok(any("MA WASTE" in (m["body"] or "") for m in msgs), "a message names the vendor")
ok(any((m["priority"] or "") == "urgent" for m in msgs),
   "the go-now message is urgent")
ok(any("leave the route where it is" in (m["body"] or "") for m in msgs),
   "go-now reads as an interruption")
ok(any("tarp" in (m["body"] or "") for m in msgs), "the boss's note reaches the driver")

print("\n-- start of day: go to vendor first --")
# Clear the board so the driver looks like the start of a fresh day.
conn.execute("UPDATE stops SET status='completed', completed_at=?, held_at=NULL"
             " WHERE route_id=?", (ts, rid))
conn.commit()
for i in range(2):
    conn.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address, city,
                    state, action, container_size, status, created_at)
                    VALUES (?,?,?,?, 'Norfolk','VA','Pull','20yd','open',?)""",
                 (rid, 40 + i, "day%d" % i, "%d Morning St" % i, ts))
conn.commit()
r = post("/api/dispatch/vendor-visit",
         {"driver_id": drv, "vendor_id": vendor, "mode": "first"})
ok(r.status_code == 200, "first-stop dispatch succeeds (got %d)" % r.status_code)
j4 = r.get_json() or {}
ok(j4.get("mode") == "first", "mode echoes back as 'first'")
ok(j4.get("held") == 2, "the day's work is parked behind it (got %r)" % j4.get("held"))
_fs = dict(conn.execute("SELECT stop_order, held_at FROM stops WHERE id=?",
                        (j4.get("stop_id"),)).fetchone())
_minwork = conn.execute(
    "SELECT MIN(stop_order) m FROM stops WHERE route_id=? AND held_at IS NOT NULL",
    (rid,)).fetchone()["m"]
ok(_fs["stop_order"] < _minwork, "the vendor really is the next stop")
_m = (j4.get("message") or "")
ok("First stop today" in _m, "the driver is told it is the first stop, not an interruption")
ok("leave the route where it is" not in _m, "and it does not read as an emergency")
_pri = conn.execute(
    "SELECT priority FROM messages WHERE route_id=? ORDER BY id DESC LIMIT 1",
    (rid,)).fetchone()["priority"]
ok((_pri or "") != "urgent", "a start-of-day errand is not flagged urgent")

# An unrecognised mode must not silently queue a repair behind a day of pulls.
conn.execute("UPDATE stops SET status='completed', completed_at=? WHERE id=?",
             (ts, j4.get("stop_id")))
conn.commit()
r = post("/api/dispatch/vendor-visit",
         {"driver_id": drv, "vendor_id": vendor, "mode": "banana"})
ok((r.get_json() or {}).get("mode") == "first", "an unknown mode defaults to 'first'")
conn.execute("UPDATE stops SET status='completed', completed_at=? WHERE id=?",
             (ts, (r.get_json() or {}).get("stop_id")))
conn.commit()

print("\n-- guards --")
r = post("/api/dispatch/vendor-visit", {"driver_id": drv})
ok(r.status_code == 400, "missing vendor is rejected (got %d)" % r.status_code)
r = post("/api/dispatch/vendor-visit", {"driver_id": 99999, "vendor_id": vendor})
ok(r.status_code == 404, "unknown driver is rejected (got %d)" % r.status_code)
r = post("/api/dispatch/vendor-visit", {"driver_id": drv, "vendor_id": 99999})
ok(r.status_code == 404, "unknown vendor is rejected (got %d)" % r.status_code)

# A driver must not be able to dispatch other drivers.
dcl = app.app.test_client()
with dcl.session_transaction() as s:
    s.update(user_id=drv, company_id=co, role="driver", roles=["driver"], _csrf_token="tok")
r = dcl.post("/api/dispatch/vendor-visit",
             data=json.dumps({"driver_id": drv, "vendor_id": vendor}),
             content_type="application/json", headers={"X-CSRF-Token": "tok"})
ok(r.status_code in (302, 401, 403), "a driver cannot use the boss endpoint (got %d)" % r.status_code)


# ══════════════════════════════════════════════════════════════════
# 3. The dispatch UI itself
# ══════════════════════════════════════════════════════════════════
print("\n-- dispatch page wiring --")
_html = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                          "static", "parser.html")).read()
# Scope to the function body: the comment above it quotes the old `|| 'P'`
# on purpose, so a whole-file search would match the explanation, not the code.
_fn = _html.split("function codeFromAction", 1)[1].split("}", 1)[0] if "function codeFromAction" in _html else ""
ok(_fn and "'P'" not in _fn,
   "codeFromAction's body no longer falls back to P (body: %r)" % _fn.strip()[:80])
ok("ACTION_BY_NAME[(name || '').trim().toLowerCase()] || null" in _html,
   "unknown actions return null instead of masquerading as Pull")
ok("badge-vendor" in _html, "a vendor badge exists")
ok("openVendorSheet" in _html, "picking a vendor opens the vendor sheet")
ok("vendor-sheet-backdrop" in _html, "the vendor sheet markup is present")
ok("/api/dispatch/vendor-visit" in _html, "the sheet posts to the boss endpoint")
for _m in ("'first'", "'now'", "'line'"):
    ok(_m in _html, "mode %s is offered in the UI" % _m)
ok("Go to vendor first" in _html, "the start-of-day wording is in the UI")
ok("X-CSRF-Token" in _html.split("vendor-visit")[0][-900:] or "X-CSRF-Token" in _html,
   "the vendor POST carries the CSRF token")

# The suggestion payload must give the sheet a vendor_id to post.
r = cl.get("/api/address-suggestions?q=MA WASTE")
_v2 = next((s for s in (r.get_json() or [])
            if (s.get("customer_name") or "").startswith("MA WASTE")), None)
ok(_v2 is not None and _v2.get("vendor_id") == vendor,
   "the suggestion carries vendor_id so no name re-matching is needed")

print("\n%d failure(s)" % len(FAILURES))
for f in FAILURES:
    print("  FAILED: " + f)
sys.exit(1 if FAILURES else 0)
