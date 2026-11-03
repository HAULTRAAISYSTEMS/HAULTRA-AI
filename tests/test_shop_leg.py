"""A shop visit in the middle of a Pickup-and-Return.

2026-11-03, from the road. Alix texted mid-route: swing by Gregory's and have
them shorten the cable on the can. The driver had already boxed out at
PRO-MIT, so his actual sequence was

    pick up can 2058  ->  dump at United  ->  Gregory's  ->  return the can

and there was nowhere in the app to put Gregory's. A Pickup-and-Return is ONE
stop row carrying legs (primary / dump / return), navigated by tapping a chip,
so there is no position in stop_order between the dump and the return. The
existing vendor stop can only land before or after the whole PR stop:

  - after it  -> the can is already returned. Too late.
  - "go now"  -> holds the PR stop mid-leg with the can on the truck, and
                 locks the driver out of the stop he is working.

So the shop visit is a LEG, not a stop. _cab_stop_legs already builds the leg
list generically and the header counts len(legs), so a fourth leg slots in and
navigation, Copy Address and the Maps links follow it for free.

The order varies -- the driver said this shape is "sometimes", not always --
so the leg is placed on either side of the dump rather than hardcoded after it.

Run:  python3 tests/test_shop_leg.py
"""
import os
import sys
import json
import tempfile
import importlib

TMP = tempfile.mkdtemp(prefix="haultra-shopleg-")
os.environ["DATABASE_PATH"] = os.path.join(TMP, "s.db")
os.environ["SECRET_KEY"] = "s"
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
            ("Shop Co", "shopco", "pro", "active", 10, ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
            " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
            ("s_boss", "x", "boss", "S Boss", co, ts))
boss = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
            " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
            ("s_drv", "x", "driver", "S Driver", co, ts))
drv = cur.lastrowid
cur.execute("INSERT INTO vendors (company_id, name, address, is_active, created_at)"
            " VALUES (?,?,?,1,?)", (co, "Gregory's", "9 Shop Rd, Norfolk", ts))
ven = cur.lastrowid
conn.commit()

scols = {r["name"] for r in conn.execute("PRAGMA table_info(stops)").fetchall()}
for c in ("shop_leg", "shop_addr", "shop_vendor_id", "shop_leg_pos", "shop_can", "shop_done_at"):
    ok(c in scols, "stops.%s column exists" % c)


# One route per driver per date, so each fixture gets its own day.
_DAY = [0]


def _next_day():
    _DAY[0] += 1
    return "2026-11-%02d" % _DAY[0]


def fresh_route(status="in_progress"):
    c = app.get_db()
    cu = c.cursor()
    cu.execute("INSERT INTO routes (company_id, route_date, route_name, created_by,"
               " assigned_to, status, created_at) VALUES (?,?,?,?,?,?,?)",
               (co, _next_day(), "R", boss, drv, status, ts))
    rid = cu.lastrowid
    cu.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address, city,
                  state, action, container_size, dump_location, return_destination,
                  assigned_can, status, driver_status, created_at)
                  VALUES (?,1,'PRO-MIT','440 Mariners Way','Norfolk','VA',
                          'Pickup and Return','20yd','United','PRO-MIT','2058',
                          'open','arrived',?)""", (rid, ts))
    sid = cu.lastrowid
    cu.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address, city,
                  state, action, container_size, status, driver_status, created_at)
                  VALUES (?,2,'Later Stop','9 Later Rd','Norfolk','VA','Pull','20yd',
                          'open','pending',?)""", (rid, ts))
    later = cu.lastrowid
    c.commit()
    return c, rid, sid, later


def legs_of(c, sid):
    s = dict(c.execute("SELECT * FROM stops WHERE id=?", (sid,)).fetchone())
    legs, active = app._cab_stop_legs(s, s.get("address") or "", {}, {})
    return [l["key"] for l in legs], legs


# ── 1. Without a shop leg, nothing changes ─────────────────────────
print("\n-- the stop as it is today --")
c, rid, sid, later = fresh_route()
keys, legs = legs_of(c, sid)
ok(keys == ["primary", "dump", "return"],
   "a PR stop still reads primary/dump/return (got %r)" % (keys,))
c.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()


def as_driver():
    with cl.session_transaction() as s:
        s.update(user_id=drv, company_id=co, role="driver", roles=["driver"],
                 _csrf_token="tok")


HJ = {"X-CSRF-Token": "tok"}

# ── 2. Gregory's AFTER the dump — the reported case ────────────────
print("\n-- dump, then Gregory's, then return --")
c, rid, sid, later = fresh_route()
c.close()
as_driver()
r = cl.post("/api/stops/%d/shop-leg" % sid,
            json={"vendor_id": ven, "position": "after_dump", "can": "2058",
                  "note": "shorten the cable"}, headers=HJ)
ok(r.status_code == 200, "shop leg accepted (got %d: %s)" % (r.status_code, r.get_data(as_text=True)[:120]))
c = app.get_db()
keys, legs = legs_of(c, sid)
ok(keys == ["primary", "dump", "shop", "return"],
   "the shop leg sits between the dump and the return (got %r)" % (keys,))
_shop = next((l for l in legs if l["key"] == "shop"), None)
ok(_shop and _shop["name"] == "Gregory's",
   "it carries the vendor's name (got %r)" % (_shop.get("name") if _shop else None))
ok(_shop and "9 Shop Rd" in (_shop["address"] or ""),
   "and the vendor's address, so Navigate works (got %r)" % (_shop.get("address") if _shop else None))
ok(_shop and _shop["label"] == "SHOP", "the chip reads SHOP (got %r)"
   % (_shop.get("label") if _shop else None))
_row = dict(c.execute("SELECT * FROM stops WHERE id=?", (sid,)).fetchone())
ok((_row.get("shop_can") or "") == "2058",
   "the can going to the shop is recorded (got %r)" % _row.get("shop_can"))
ok(_row["status"] == "open" and _row["driver_status"] == "arrived",
   "the stop the driver is working is untouched -- not held, not reset")
ok(not _row.get("held_at"), "and it is not held")
_later = dict(c.execute("SELECT held_at, stop_order FROM stops WHERE id=?", (later,)).fetchone())
ok(not _later["held_at"], "the rest of the route is not held either")
c.close()

# ── 3. Gregory's BEFORE the dump ───────────────────────────────────
# The driver said this shape is "sometimes", not always: a full can can go to
# the shop before it is emptied.
print("\n-- Gregory's before the dump --")
c, rid2, sid2, later2 = fresh_route()
c.close()
as_driver()
r = cl.post("/api/stops/%d/shop-leg" % sid2,
            json={"vendor_id": ven, "position": "before_dump"}, headers=HJ)
ok(r.status_code == 200, "accepted (got %d)" % r.status_code)
c = app.get_db()
keys, _ = legs_of(c, sid2)
ok(keys == ["primary", "shop", "dump", "return"],
   "the shop leg sits before the dump (got %r)" % (keys,))
c.close()

# ── 4. A stop with no dump leg still takes a shop leg ──────────────
print("\n-- a plain Pull, no dump leg --")
c = app.get_db()
cu = c.cursor()
cu.execute("INSERT INTO routes (company_id, route_date, route_name, created_by,"
           " assigned_to, status, created_at) VALUES (?,?,?,?,?,'in_progress',?)",
           (co, _next_day(), "R3", boss, drv, ts))
rid3 = cu.lastrowid
cu.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address, city,
              state, action, container_size, status, driver_status, created_at)
              VALUES (?,1,'Plain','1 Plain St','Norfolk','VA','Pull','20yd',
                      'open','pending',?)""", (rid3, ts))
sid3 = cu.lastrowid
c.commit()
c.close()
as_driver()
r = cl.post("/api/stops/%d/shop-leg" % sid3,
            json={"vendor_name": "Maypaw Diesel", "position": "after_dump"}, headers=HJ)
ok(r.status_code == 200, "accepted on a stop with no dump (got %d)" % r.status_code)
c = app.get_db()
keys, legs = legs_of(c, sid3)
ok(keys == ["primary", "shop"],
   "it lands after the primary leg when there is no dump (got %r)" % (keys,))
_s3 = next((l for l in legs if l["key"] == "shop"), None)
ok(_s3 and _s3["name"] == "Maypaw Diesel",
   "a typed vendor name works too (got %r)" % (_s3.get("name") if _s3 else None))
c.close()

# ── 5. Clearing it — plans change mid-route ────────────────────────
print("\n-- clearing the shop leg --")
as_driver()
r = cl.post("/api/stops/%d/shop-leg" % sid, json={"clear": True}, headers=HJ)
ok(r.status_code == 200, "clear accepted (got %d)" % r.status_code)
c = app.get_db()
keys, _ = legs_of(c, sid)
ok(keys == ["primary", "dump", "return"],
   "the leg is gone and the stop reads as before (got %r)" % (keys,))
c.close()

# ── 6. What must be refused ────────────────────────────────────────
print("\n-- refusals --")
as_driver()
r = cl.post("/api/stops/%d/shop-leg" % sid, json={"position": "after_dump"}, headers=HJ)
ok(r.status_code == 400, "no vendor at all is refused (got %d)" % r.status_code)
r = cl.post("/api/stops/%d/shop-leg" % sid,
            json={"vendor_id": 999999, "position": "after_dump"}, headers=HJ)
ok(r.status_code in (400, 404), "an unknown vendor id is refused (got %d)" % r.status_code)

# Another company's driver must not touch this stop.
c = app.get_db()
cu = c.cursor()
cu.execute("INSERT INTO companies (name, slug, subscription_plan, subscription_status,"
           " max_drivers, created_at) VALUES (?,?,?,?,?,?)",
           ("Other Co", "otherco", "pro", "active", 5, ts))
oco = cu.lastrowid
cu.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
           " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
           ("o_drv", "x", "driver", "O Drv", oco, ts))
odrv = cu.lastrowid
c.commit()
c.close()
with cl.session_transaction() as s:
    s.update(user_id=odrv, company_id=oco, role="driver", roles=["driver"],
             _csrf_token="tok")
r = cl.post("/api/stops/%d/shop-leg" % sid,
            json={"vendor_id": ven, "position": "after_dump"}, headers=HJ)
ok(r.status_code in (403, 404),
   "a driver from another company cannot add a leg to this stop (got %d)" % r.status_code)

# A completed stop is history; it does not take a new errand.
c = app.get_db()
c.execute("UPDATE stops SET status='completed' WHERE id=?", (later,))
c.commit()
c.close()
as_driver()
r = cl.post("/api/stops/%d/shop-leg" % later,
            json={"vendor_id": ven, "position": "after_dump"}, headers=HJ)
ok(r.status_code == 400, "a completed stop is refused (got %d)" % r.status_code)

# ── 7. The boss is told ────────────────────────────────────────────
print("\n-- the boss hears about it --")
c, rid4, sid4, later4 = fresh_route()
c.close()
as_driver()
cl.post("/api/stops/%d/shop-leg" % sid4,
        json={"vendor_id": ven, "position": "after_dump", "can": "2058"}, headers=HJ)
c = app.get_db()
msgs = [dict(m) for m in c.execute(
    "SELECT body FROM messages WHERE route_id=? ORDER BY id DESC", (rid4,)).fetchall()]
c.close()
ok(msgs, "a message lands on the route thread")
_joined = " ".join(m["body"] for m in msgs)
ok("Gregory" in _joined, "it names the vendor (got %r)" % (_joined[:140],))
ok("2058" in _joined, "and the can going with him (got %r)" % (_joined[:140],))

# ── 8. The cab actually renders it ─────────────────────────────────
print("\n-- cab view --")
as_driver()
html = cl.get("/driver/route/%d" % rid4).get_data(as_text=True)
if "LEG 1 OF" not in html:
    html = cl.get("/cab/%d" % rid4).get_data(as_text=True)
ok("LEG 1 OF 4" in html,
   "the header counts the new leg: primary + dump + shop + return (expected 'LEG 1 OF 4')")
ok("SHOP" in html, "a SHOP chip is rendered")
ok("Gregory" in html, "naming the vendor")
ok("9 Shop Rd" in html, "and the shop's address is on the page for Navigate")
ok("Remove shop stop" in html,
   "the menu offers to take it off again once there is one")

# And on a stop WITHOUT one, the menu offers to add it.
print("\n-- the control to add one --")
c, rid5, sid5, later5 = fresh_route()
c.close()
as_driver()
html5 = cl.get("/driver/route/%d" % rid5).get_data(as_text=True)
ok("Shop stop on this job" in html5,
   "a stop with no shop leg offers 'Shop stop on this job'")
ok("openShopLeg" in html5, "wired to the shop-leg modal")
ok("After the dump" in html5 and "Before the dump" in html5,
   "and the modal lets the driver pick which side of the dump it goes")

print("\n%d failure(s)" % len(FAILURES))
for f in FAILURES:
    print("  FAILED: " + f)
sys.exit(1 if FAILURES else 0)
