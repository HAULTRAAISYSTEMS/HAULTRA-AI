"""A can dropped at a return destination is OFF the truck (fix/can-left-at-drop-destination).

Reported from the cab 2026-11-18, two screenshots a minute apart:

    SUSSEX · PULL → DUMP Branscome → RETURN Dominion
    "After dumping take the container to dominion landfill and leave it there"

    velocity · PICKUP AND RETURN → DUMP HRRC
    [ Bin In - Place Empty Bin ]

    "It's still saying bin in for velocity but I'm just PR"

He is right. He left the can at Dominion. He pulled into velocity with an
empty truck, so there is no empty to set off there -- velocity is a plain
pickup-and-return: box out the full, dump it, bring the same can back.

Why the app thought otherwise: _next_can_state models every Pull as ending
with the emptied can still on the truck ("After dump the driver keeps the
emptied can"), which is true of an ordinary pull and false of this one. The
can-flow walk never read return_destination at all, so it carried a phantom
empty forward, and the next PR saw can_state_before='empty_can' and derived
swap_with_prev_pull=1 -- the swap wf_map, whose box_out step is exactly the
"Bin In - Place Empty Bin" button he was staring at.

A return destination is the mirror of a Delivery: the can leaves the truck.

And, for the fourth time, the values are STAMPED at dispatch, so the parse-time
fix alone would never reach the route he is driving today. _heal_drop_can_destination
(shipped hours earlier) writes the destination onto old stops but does not
recompute the flow that depends on it, which leaves exactly this route in a
half-healed state. So the heal closes its own loop.
"""
import os, sys, tempfile, importlib
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "candrop.db")
os.environ["SECRET_KEY"] = "candrop"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")

def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c:
        raise SystemExit("FAILED: " + m)

_TODAY = app.now_ts()[:10]

app.init_db()
conn = app.get_db(); cur = conn.cursor(); ts = app.now_ts()
cur.execute("""INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,
               yard_address,yard_city,created_at) VALUES (?,?,?,?,?,?,?,?)""",
            ("DropCo", "dropco", "pro", "active", 10, "2545 Squadron Ct", "Virginia Beach", ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("d_boss", "x", "boss", "Boss", co, ts)); boss = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("d_drv", "x", "driver", "Tim", co, ts)); drv = cur.lastrowid
for _n, _a, _c in (("Dominion", "5444 Bainbridge Blvd", "Chesapeake"),
                   ("Branscome", "5225 Learning Cir", "Virginia Beach"),
                   ("HRRC", "1613 Centerville Tpk", "Virginia Beach")):
    cur.execute("""INSERT INTO dump_locations (company_id,name,address,city,state,active,created_at)
                   VALUES (?,?,?,?,?,1,?)""", (co, _n, _a, _c, "VA", ts))
conn.commit(); conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()
HJ = {"X-CSRF-Token": "tok"}
def as_boss():
    with cl.session_transaction() as s:
        s.update(user_id=boss, company_id=co, role="boss", roles=["owner", "dispatcher"], _csrf_token="tok")
def as_driver():
    with cl.session_transaction() as s:
        s.update(user_id=drv, company_id=co, role="driver", roles=["driver"], _csrf_token="tok")


# =========================================================================
# 1. the unit: a stop that leaves its can somewhere ends with an empty truck
# =========================================================================
ok(app._next_can_state("pull", "no_can") == "empty_can",
   "an ORDINARY pull still ends holding the empty — the swap stock that "
   "makes the next PR a swap is not being taken away")
ok(app._next_can_state("pull", "no_can", leaves_can=True) == "no_can",
   "a pull that drops its can at a return destination ends with nothing "
   "on the truck — the reported bug, at the unit level")
ok(app._next_can_state("pickup and return", "empty_can", leaves_can=True) == "no_can",
   "and so does a PR told to leave its empty somewhere else")
ok(app._next_can_state("delivery", "empty_can", leaves_can=True) == "no_can",
   "a delivery was already no_can and stays that way")


# =========================================================================
# 2. the walk: Tim's actual two stops
# =========================================================================
as_boss()
r = cl.post("/api/dispatch", json={"driver_id": drv, "route_date": _TODAY, "stops": [
    {"action": "P", "address": "3425 Westminister Ave, Norfolk", "customer": "Sussex",
     "container_size": "20yd", "dump_leg": "Branscome",
     "notes": "After dumping take the container to dominion landfill and leave it there"},
    {"action": "PR", "address": "1613 Centerville Tpk, Virginia Beach", "customer": "velocity",
     "container_size": "30yd", "dump_leg": "HRRC", "notes": ""},
]}, headers=HJ)
ok(r.status_code == 200, "the day dispatches — status %s" % r.status_code)

c = app.get_db()
rid = c.execute("SELECT id FROM routes WHERE company_id=?", (co,)).fetchone()["id"]
def _stop(name):
    return c.execute("SELECT * FROM stops WHERE route_id=? AND customer_name=?",
                     (rid, name)).fetchone()

# The drop-off destination reaches a stop either from the parser (#151) or
# from _heal_drop_can_destination (#152). Both write this column; the walk
# below is what has to read it.
ok(app._heal_drop_can_destination(c, rid) == 1,
   "Sussex picks up its drop-off at Dominion — the #151/#152 behaviour, "
   "still working; this fix is built on top of it, not instead of it")
c.commit()
_sx = _stop("Sussex")
ok((app._row_get(_sx, "return_destination") or "") == "Dominion",
   "and the destination is on the stop")

app.compute_can_flow(c, rid); c.commit()
_v = _stop("velocity")
ok((app._row_get(_v, "can_state_before") or "") == "no_can",
   "velocity is reached with an EMPTY truck — the can is sitting at Dominion")
ok(not app._row_get(_v, "swap_with_prev_pull"),
   "so velocity is NOT a swap — this is the line that was wrong in the cab")
c.close()


# =========================================================================
# 3. the control: nothing was taken away from the ordinary case
# =========================================================================
as_boss()
r = cl.post("/api/dispatch", json={"driver_id": drv, "route_date": "2026-12-04", "stops": [
    {"action": "P", "address": "3425 Westminister Ave, Norfolk", "customer": "Plain",
     "container_size": "20yd", "dump_leg": "Branscome", "notes": "concrete"},
    {"action": "PR", "address": "1613 Centerville Tpk, Virginia Beach", "customer": "After",
     "container_size": "30yd", "dump_leg": "HRRC", "notes": ""},
]}, headers=HJ)
ok(r.status_code == 200, "a day with a plain pull dispatches too")
c = app.get_db()
rid2 = c.execute("SELECT id FROM routes WHERE company_id=? AND route_date=?",
                 (co, "2026-12-04")).fetchone()["id"]
_after = c.execute("SELECT * FROM stops WHERE route_id=? AND customer_name='After'",
                   (rid2,)).fetchone()
ok((app._row_get(_after, "can_state_before") or "") == "empty_can",
   "after a plain pull the truck still carries the empty")
ok(app._row_get(_after, "swap_with_prev_pull") == 1,
   "and the PR after it is still a swap — the designed behaviour is intact, "
   "this fix only removes the can that was never on the truck")
c.close()


# =========================================================================
# 4. the cab: the button he was actually looking at
# =========================================================================
as_driver()
cl.post("/driver/clock/in", data={"_csrf_token": "tok", "next": "/driver/route/%d" % rid})
cl.post("/route/%d/start" % rid, data={"_csrf_token": "tok"})
c = app.get_db()
vid = c.execute("SELECT id FROM stops WHERE route_id=? AND customer_name='velocity'",
                (rid,)).fetchone()["id"]
c.execute("UPDATE stops SET driver_status='box_out' WHERE id=?", (vid,))
c.commit(); c.close()

_h = cl.get("/driver/route/%d?show_stop=%d" % (rid, vid)).get_data(as_text=True)
ok('class="cab-card' in _h and "PRE-FLIGHT" not in _h, "the cab card renders")
ok("Place Empty Bin" not in _h,
   "boxed out at velocity, the cab does NOT offer to set an empty down — "
   "he has no empty; that button was the whole report")
ok("Go To Dump" in _h,
   "it offers the step that is actually next: take the full one to HRRC")


# =========================================================================
# 5. the heal: the route he is driving RIGHT NOW
# =========================================================================
# Exactly the half-healed state _heal_drop_can_destination leaves behind:
# the destination is on the stop, the flow that depends on it is not.
c = app.get_db()
c.execute("UPDATE stops SET can_state_before='empty_can', swap_with_prev_pull=1 WHERE id=?", (vid,))
c.commit()
ok(app._heal_can_flow_after_drop(c, rid) is True,
   "the heal recognises a route whose can flow predates the fix")
c.commit()
_v2 = c.execute("SELECT * FROM stops WHERE id=?", (vid,)).fetchone()
ok(not app._row_get(_v2, "swap_with_prev_pull"),
   "and velocity stops being a swap without anyone re-dispatching the day")
ok(app._heal_can_flow_after_drop(c, rid) is False,
   "running it again writes nothing — a healthy route costs one SELECT")
c.close()

# And from a cold page load, which is the only version that helps him.
c = app.get_db()
c.execute("UPDATE stops SET can_state_before='empty_can', swap_with_prev_pull=1 WHERE id=?", (vid,))
c.commit(); c.close()
_h2 = cl.get("/driver/route/%d?show_stop=%d" % (rid, vid)).get_data(as_text=True)
ok("Place Empty Bin" not in _h2,
   "opening the cab heals the stamp in passing — nothing for the driver to do")

print("ALL CAN-LEFT-AT-DROP TESTS PASSED")
