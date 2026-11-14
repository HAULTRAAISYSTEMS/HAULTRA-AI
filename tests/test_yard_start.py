"""Start-of-day yard load is a YARD stop, not a Delivery (fix/yard-start-not-delivery).

Reported 2026-11-14: "Start with #30115 at the yard" parsed as

    D  ·  2545 Squadron Ct, Virginia Beach  ·  "start of day — pick up can 30115 from yard"

The address was right (2545 Squadron Ct IS the yard) but the action was not.
The driver is ALREADY at the yard at 6am — there is nothing to drive to and
nothing is being delivered. The can is being LOADED onto the truck.

The badge was the visible half. The expensive half was downstream: a completed
Delivery marks its can 'deployed' at the stop address, so can 30115 would read
as sitting out at the yard address as if it were a job site -- gone from yard
inventory, and wrong on the Bin Tracker.

The invariant this file pins: a Delivery whose address is the company's OWN
yard is never a Delivery. Both ends of the day are covered by it -- a morning
load and an evening drop-off are both YARD.
"""
import os, sys, tempfile, importlib
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "yardstart.db")
os.environ["SECRET_KEY"] = "yardstart"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")

def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c:
        raise SystemExit("FAILED: " + m)

app.init_db()
conn = app.get_db(); cur = conn.cursor(); ts = app.now_ts()
cur.execute("""INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,
               yard_address,yard_city,created_at) VALUES (?,?,?,?,?,?,?,?)""",
            ("YardCo", "yardco", "pro", "active", 10, "2545 Squadron Ct", "Virginia Beach", ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("y_boss", "x", "boss", "Boss", co, ts)); boss = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("y_drv", "x", "driver", "Tim", co, ts)); drv = cur.lastrowid
# The yard in the address book, the way a real company has it.
cur.execute("""INSERT INTO saved_addresses (company_id,customer_name,address,full_address,kind,norm_key,hidden,times_used,last_used_at,created_at)
               VALUES (?,?,?,?,?,?,0,1,?,?)""",
            (co, "Yard", "2545 Squadron Ct", "2545 Squadron Ct, Virginia Beach", "yard",
             app._address_book_key("Yard", "2545 Squadron Ct", "yard"), ts, ts))
conn.commit(); conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()
def as_boss():
    with cl.session_transaction() as s:
        s.update(user_id=boss, company_id=co, role="boss", roles=["owner", "dispatcher"], _csrf_token="tok")
HJ = {"X-CSRF-Token": "tok"}


# ── 1. the yard-address test itself ────────────────────────────────────────
c = app.get_db()
ok(app._is_company_yard_address(c, co, "2545 Squadron Ct, Virginia Beach"),
   "the yard's own address is recognized as the yard (full address)")
ok(app._is_company_yard_address(c, co, "2545 squadron ct"),
   "recognized with no city and in lower case — formatting must not hide the yard")
ok(app._is_company_yard_address(c, co, "2545 Squadron Court, VB"),
   "recognized through a spelled-out street type and a city abbreviation")
ok(not app._is_company_yard_address(c, co, "11496 Shiloh Dr, Virginia Beach"),
   "a customer address is NOT the yard")
ok(not app._is_company_yard_address(c, co, "2547 Squadron Ct, Virginia Beach"),
   "the house number still matters — 2547 is not 2545")
ok(not app._is_company_yard_address(c, co, ""),
   "a blank address is not the yard")
c.close()


# ── 2. the guard: a D at the yard becomes YARD ─────────────────────────────
# Tim's exact text, shaped the way the model returned it.
_reported = [{
    "action": "D", "address": "2545 Squadron Ct, Virginia Beach", "customer": "",
    "container_size": None, "dump_leg": None, "return_leg": None,
    "assigned_can": "", "raw": "Start with #30115 at the yard",
    "confidence": "high", "notes": "start of day — pick up can 30115 from yard",
}]
out = app._ensure_yard_not_delivery(list(_reported), co)
ok(len(out) == 1, "the guard keeps the stop — it rewrites the action, it never drops work")
ok(out[0]["action"] == "YARD",
   "'Start with #30115 at the yard' is a YARD stop, not a D (the reported bug)")
ok(out[0]["address"] == "2545 Squadron Ct, Virginia Beach",
   "the address is left alone — the yard IS where the driver is")
ok("30115" in (out[0].get("notes") or ""),
   "the note survives the rewrite, so the driver still knows which can to hook")
ok((out[0].get("assigned_can") or "") == "30115",
   "the can number is lifted out of the note onto assigned_can — the fleet needs it structured")

# A real delivery is untouched.
_real = [{"action": "D", "address": "11496 Shiloh Dr, Virginia Beach", "customer": "Ashdon",
          "notes": "drop the 30yd", "assigned_can": "3124"}]
out2 = app._ensure_yard_not_delivery(list(_real), co)
ok(out2[0]["action"] == "D",
   "a Delivery to a real customer address stays a Delivery")

# Other actions at the yard are left alone: a Pull from the yard is a real
# errand (go get a can that is sitting there), and so is a Relocate.
for _act in ("P", "PR", "R", "S"):
    _o = app._ensure_yard_not_delivery(
        [{"action": _act, "address": "2545 Squadron Ct", "customer": "", "notes": ""}], co)
    ok(_o[0]["action"] == _act,
       "a %s at the yard is left alone — only a Delivery to your own yard is impossible" % _act)

# End of day: dropping the empty back at the yard is also not a Delivery.
_eod = [{"action": "D", "address": "2545 Squadron Ct", "customer": "",
         "notes": "end of day", "assigned_can": ""}]
ok(app._ensure_yard_not_delivery(list(_eod), co)[0]["action"] == "YARD",
   "an end-of-day drop at the yard is YARD too — the invariant holds at both ends of the day")


# ── 3. the prompt teaches the model the same thing ─────────────────────────
c = app.get_db()
prompt = app._build_parse_system_prompt(c, co)
c.close()
ok("YARD" in prompt, "YARD is an action code the model is told about")
ok("start of day" in prompt.lower(),
   "the prompt names the start-of-day yard load explicitly")


# ── 4. it survives the insert ──────────────────────────────────────────────
as_boss()
r = cl.post("/api/dispatch", json={"driver_id": drv, "route_date": "2026-11-14", "stops": [
    {"action": "YARD", "address": "2545 Squadron Ct, Virginia Beach", "customer": "",
     "container_size": "30yd", "notes": "start of day — load can 30115"},
    {"action": "D", "address": "11496 Shiloh Dr, Virginia Beach", "customer": "Ashdon",
     "container_size": "30yd", "notes": "drop it here"},
]}, headers=HJ)
ok(r.status_code == 200, "a YARD stop dispatches (HTTP 200) — status %s" % r.status_code)
c = app.get_db()
rid = c.execute("SELECT id FROM routes WHERE company_id=? ORDER BY id DESC LIMIT 1", (co,)).fetchone()["id"]
rows = [dict(x) for x in c.execute(
    "SELECT action, address, assigned_can, notes FROM stops WHERE route_id=? ORDER BY stop_order, id",
    (rid,)).fetchall()]
ok([x["action"] for x in rows] == ["Yard", "Delivery"],
   "the YARD stop lands as action 'Yard' and the real drop stays 'Delivery'")
ok(rows[0]["assigned_can"] == "30115",
   "insert reads the can out of a YARD note too — not only a Delivery note "
   "(the gap that lost the lot number in #133)")

# ── 5. the fleet never deploys a can at the yard ───────────────────────────
c.execute("UPDATE stops SET status='completed' WHERE route_id=?", (rid,))
c.commit()
app._sync_fleet_from_history(c, co)
_row = c.execute("SELECT status, notes FROM containers WHERE company_id=? AND label=?",
                 (co, "30115")).fetchone()
ok(_row is not None, "can 30115 is learned into the fleet from the yard load")
ok(_row["status"] == "loaded_at_yard",
   "a completed yard load puts can 30115 ON THE TRUCK, not 'deployed' at the yard "
   "(the expensive half of the bug)")
c.close()


# ── 6. the yard load is pinned to the front of the route ───────────────────
_kw = " ".join(app._FIRST_KEYWORDS).lower()
ok("start of day" in _kw,
   "'start of day' pins a stop first when the route is optimized — the yard "
   "load cannot be optimized into the middle of the day")
ok("start with" in _kw,
   "so does the boss's own wording, 'Start with #30115 container at yard' — "
   "Optimize must agree with the insert pass, not fight it")


# ── 7. start-of-day vs end-of-day yard stops ───────────────────────────────
ok(app._is_yard_start_stop("Yard", "Start with #30115 container at yard"),
   "a yard stop with the boss's own wording is a START-of-day load")
ok(app._is_yard_start_stop("Yard", ""),
   "a bare yard stop with no note is a load — the common case")
ok(not app._is_yard_start_stop("Yard", "end of day"),
   "a yard stop marked end of day is NOT a start — it stays where it is")
ok(not app._is_yard_start_stop("Yard", "take to yard, back to yard after the last pull"),
   "an end-of-day return phrase keeps it out of the morning")
ok(not app._is_yard_start_stop("Delivery", "start of day"),
   "only a YARD action qualifies — a real Delivery is never pulled to the front")


# ── 8. added AFTER the day is built, it still goes first ───────────────────
# Tim's report, verbatim: "If I put in start with container at the yard after
# putting in some routes the parser or route board should recognize what is
# going on an put that on the first one."  It was landing LAST.
as_boss()
r = cl.post("/api/dispatch", json={"driver_id": drv, "route_date": "2026-11-15", "stops": [
    {"action": "P",  "address": "401 Clearfield Ave, Chesapeake",    "customer": "Balicore", "container_size": "30yd"},
    {"action": "PR", "address": "529 Whispering Oaks Cir, Chesapeake", "customer": "Oaks",   "container_size": "30yd"},
]}, headers=HJ)
ok(r.status_code == 200, "two ordinary stops dispatch first — status %s" % r.status_code)
c = app.get_db()
rid2 = c.execute("SELECT id FROM routes WHERE company_id=? AND route_date=?",
                 (co, "2026-11-15")).fetchone()["id"]
c.close()

# ...and NOW the boss adds the yard load, the way he actually did it.
r = cl.post("/api/route/%d/insert-stops" % rid2, json={"stops": [
    {"action": "YARD", "address": "2545 Squadron Ct, Virginia Beach, VA",
     "customer": "The yard", "container_size": "30yd",
     "notes": "Start with #30115 container at yard", "confidence": "high",
     "insert_before": "end"},
]}, headers=HJ)
ok(r.status_code == 200, "the late yard load inserts — status %s" % r.status_code)
c = app.get_db()
rows2 = [dict(x) for x in c.execute(
    "SELECT action, customer_name, stop_order FROM stops WHERE route_id=? ORDER BY stop_order, id",
    (rid2,)).fetchall()]
ok([x["action"] for x in rows2] == ["Yard", "Pull", "Pickup and Return"],
   # api_insert_stops is what the confirm sheet's Add Stop actually posts to.
   "added LAST, the yard load is reordered to stop 1 — the reported bug "
   "(order was %s)" % [x["action"] for x in rows2])
ok(rows2[0]["stop_order"] == 1, "its stop_order really is 1, not just its list position")

# Idempotent: running the pass again changes nothing.
_before = [x["stop_order"] for x in rows2]
app._pin_yard_start_first(c, rid2)
c.commit()
_after = [dict(x)["stop_order"] for x in c.execute(
    "SELECT stop_order FROM stops WHERE route_id=? ORDER BY stop_order, id", (rid2,)).fetchall()]
ok(_before == _after, "running the pass twice changes nothing — it is idempotent")
c.close()

# ...and a yard stop the boss put in the MIDDLE on purpose (a swing back for a
# second can) stays there when the next stop is added. Without the only_ids
# scope a yard stop could never live anywhere but first: every later Add Stop
# would drag it back to breakfast.
as_boss()
r = cl.post("/api/route/%d/insert-stops" % rid2, json={"stops": [
    {"action": "P", "address": "1994 Tiger Dr, Virginia Beach", "customer": "Tiger",
     "container_size": "30yd", "confidence": "high", "insert_before": "end"},
]}, headers=HJ)
ok(r.status_code == 200, "one more ordinary stop goes in — status %s" % r.status_code)
c = app.get_db()
_mid = c.execute("SELECT id FROM stops WHERE route_id=? AND action='Yard'", (rid2,)).fetchone()["id"]
# The boss drags the yard stop to the middle himself.
c.execute("UPDATE stops SET stop_order=99 WHERE id=?", (_mid,))
c.commit()
_ids_before = [dict(x)["id"] for x in c.execute(
    "SELECT id FROM stops WHERE route_id=? ORDER BY stop_order, id", (rid2,)).fetchall()]
c.close()
r = cl.post("/api/route/%d/insert-stops" % rid2, json={"stops": [
    {"action": "P", "address": "11496 Shiloh Dr, Virginia Beach", "customer": "Ashdon",
     "container_size": "30yd", "confidence": "high", "insert_before": "end"},
]}, headers=HJ)
ok(r.status_code == 200, "and another — status %s" % r.status_code)
c = app.get_db()
_ids_after = [dict(x)["id"] for x in c.execute(
    "SELECT id FROM stops WHERE route_id=? ORDER BY stop_order, id", (rid2,)).fetchall()]
ok(_ids_after[:len(_ids_before)] == _ids_before,
   "a yard stop the boss placed on purpose keeps its slot when a later stop "
   "is added — only a JUST-INSERTED yard load is pulled to the front")
c.close()


# ── 9. a stop the driver has STARTED is never jumped ───────────────────────
# He may be boxed out somewhere. The yard is not more urgent than the can
# under his feet — same rule _reprioritize_for_vendor follows.
as_boss()
r = cl.post("/api/dispatch", json={"driver_id": drv, "route_date": "2026-11-16", "stops": [
    {"action": "P", "address": "401 Clearfield Ave, Chesapeake", "customer": "Balicore", "container_size": "30yd"},
    {"action": "P", "address": "1994 Tiger Dr, Virginia Beach",  "customer": "Tiger",    "container_size": "30yd"},
]}, headers=HJ)
ok(r.status_code == 200, "a third route dispatches — status %s" % r.status_code)
c = app.get_db()
rid3 = c.execute("SELECT id FROM routes WHERE company_id=? AND route_date=?",
                 (co, "2026-11-16")).fetchone()["id"]
_first_id = c.execute("SELECT id FROM stops WHERE route_id=? ORDER BY stop_order LIMIT 1",
                      (rid3,)).fetchone()["id"]
# The driver is physically at it — boxed out, can on the hook.
c.execute("UPDATE stops SET driver_status='box_out' WHERE id=?", (_first_id,))
c.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address, action,
             container_size, notes, status, created_at)
             VALUES (?,?,?,?,?,?,?, 'open', ?)""",
          (rid3, 99, "The yard", "2545 Squadron Ct", "Yard", "30yd",
           "Start with #30115 container at yard", app.now_ts()))
c.commit()
app._pin_yard_start_first(c, rid3)
c.commit()
_ord3 = [dict(x) for x in c.execute(
    "SELECT id, action FROM stops WHERE route_id=? ORDER BY stop_order, id", (rid3,)).fetchall()]
ok(_ord3[0]["id"] == _first_id,
   "the stop he is BOXED OUT at keeps the lead — the yard never jumps work "
   "already under his feet")
ok(_ord3[1]["action"] == "Yard",
   "the yard load takes the next slot instead — first of what is still ahead")
c.close()


# ── 10. the cab stops asking him to arrive somewhere he already is ─────────
# "And it's saying arrive at stop when the driver is already starting at the
# yard in the truck" — reported from the cab, 2026-11-14.
c = app.get_db()
_yard_stop_id = c.execute(
    "SELECT id FROM stops WHERE route_id=? AND action='Yard'", (rid2,)).fetchone()["id"]
_srow = c.execute("SELECT * FROM stops WHERE id=?", (_yard_stop_id,)).fetchone()
ok(app._effective_can(_srow) == "30115",
   "the cab reads the can out of a hand-typed YARD note — the 'Hook can #...' "
   "banner was blank on the one stop whose whole job is naming the can")
# A second driver with a route dated TODAY: the cab (and the clock) work off
# today's route, and the first driver's today slot is already taken.
c2 = app.get_db()
_cur = c2.cursor()
_cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at)"
             " VALUES (?,?,?,?,?,?)", ("y_drv2", "x", "driver", "Cab", co, app.now_ts()))
drv2 = _cur.lastrowid
c2.commit(); c2.close(); c.close()

_today = app.now_ts()[:10]
as_boss()
r = cl.post("/api/dispatch", json={"driver_id": drv2, "route_date": _today, "stops": [
    {"action": "YARD", "address": "2545 Squadron Ct, Virginia Beach", "customer": "The yard",
     "container_size": "30yd", "notes": "Start with #30115 container at yard"},
    {"action": "P", "address": "401 Clearfield Ave, Chesapeake", "customer": "Balicore",
     "container_size": "30yd"},
]}, headers=HJ)
ok(r.status_code == 200, "today's cab route dispatches — status %s" % r.status_code)
c = app.get_db()
rid4 = c.execute("SELECT id FROM routes WHERE company_id=? AND assigned_to=? AND route_date=?",
                 (co, drv2, _today)).fetchone()["id"]
c.close()

with cl.session_transaction() as s:
    s.update(user_id=drv2, company_id=co, role="driver", roles=["driver"], _csrf_token="tok")
# The cab card only renders once he is on the clock — off the clock the page
# is the PRE-FLIGHT gate, and asserting against that would pass for the wrong
# reason (every needle absent).
# Two taps stand between a parked truck and the cab card: clock in at the
# truck, then START ROUTE. Both, or the page below is the pre-flight card.
cl.post("/driver/clock/in", data={"_csrf_token": "tok", "next": "/driver/route/%d" % rid4})
cl.post("/route/%d/start" % rid4, data={"_csrf_token": "tok"})
page = cl.get("/driver/route/%d" % rid4)
ok(page.status_code == 200, "the cab page renders with a yard stop on it — status %s" % page.status_code)
_html = page.get_data(as_text=True)
ok('class="cab-card' in _html and "PRE-FLIGHT" not in _html,
   "the cab CARD is really on the page — off the clock this route shows the "
   "pre-flight gate instead, where every needle below would be absent for "
   "the wrong reason")
ok("Arrived at Stop" not in _html,
   "no 'Arrived at Stop' on a yard load — he never left the yard to arrive at it")
ok('id="cab-nav-btn"' not in _html,
   "no Navigate button either — there is nowhere to drive to")
ok("Can Hooked" in _html,
   "one honest tap instead: 'Can Hooked — Start Route'")
ok("Hook can #30115" in _html,
   "and the can number is on the card in the green banner, which is the "
   "whole point of the stop")

# The ordinary stop behind it still has both, so the branch above is scoped
# to the yard load and has not quietly disarmed the rest of the cab.
_next_id = [x for x in app.get_db().execute(
    "SELECT id, action FROM stops WHERE route_id=? ORDER BY stop_order", (rid4,)).fetchall()
    if dict(x)["action"] != "Yard"][0]["id"]
_h2 = cl.get("/driver/route/%d?show_stop=%d" % (rid4, _next_id)).get_data(as_text=True)
ok("Arrived at Stop" in _h2 and 'id="cab-nav-btn"' in _h2,
   "a normal stop still shows Navigate and Arrived at Stop — the yard branch "
   "is scoped, not a cab-wide change")

# ── 11. the can he hooked at the yard RIDES to the next stop ──────────────
# Reported from the cab 2026-11-14: "So I started with the can from the yard
# but the next route don't show that I brought that can to this route. It's
# acting as if this is an regular PR."
#
# It was. compute_can_flow walks the stops tracking whether the truck holds an
# empty, and 'yard' was not one of the actions it knew, so the state stayed
# no_can and the next PR derived return-same-can mode. The engine already had
# the right shape for this — a Pull leaves the truck holding an empty, which
# the very next PR consumes as a swap — a yard load just never joined it.
_cur2 = app.get_db(); _c2 = _cur2.cursor()
_c2.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at)"
            " VALUES (?,?,?,?,?,?)", ("y_drv3", "x", "driver", "Flow", co, app.now_ts()))
drv3 = _c2.lastrowid
_cur2.commit(); _cur2.close()

as_boss()
r = cl.post("/api/dispatch", json={"driver_id": drv3, "route_date": "2026-11-17", "stops": [
    {"action": "YARD", "address": "2545 Squadron Ct, Virginia Beach", "customer": "The yard",
     "container_size": "30yd", "notes": "Start with #30115 container at yard"},
    {"action": "PR", "address": "401 Clearfield Ave, Chesapeake", "customer": "Balicore",
     "container_size": "30yd", "dump_leg": "Dominion"},
]}, headers=HJ)
ok(r.status_code == 200, "yard load + PR dispatches — status %s" % r.status_code)
c = app.get_db()
rid5 = c.execute("SELECT id FROM routes WHERE company_id=? AND route_date=?",
                 (co, "2026-11-17")).fetchone()["id"]
_fl = [dict(x) for x in c.execute(
    "SELECT action, can_state_before, swap_with_prev_pull FROM stops"
    " WHERE route_id=? ORDER BY stop_order, id", (rid5,)).fetchall()]
ok(_fl[0]["can_state_before"] == "no_can",
   "he reaches the yard with an empty truck — nothing on it yet")
ok(_fl[1]["can_state_before"] == "empty_can",
   "he reaches Balicore CARRYING the empty he hooked at the yard (was 'no_can')")
ok(_fl[1]["swap_with_prev_pull"] == 1,
   "so Balicore is a SWAP, not a regular PR — set the empty off, box out the "
   "full (the reported bug)")
c.close()

# An END-of-day yard stop is the opposite: he drops the empty off and leaves
# the yard with an empty truck. It must not pretend he is still carrying one.
c = app.get_db()
ok(app._next_can_state("yard", "no_can", yard_loads=True) == "empty_can",
   "a yard LOAD leaves the truck holding an empty")
ok(app._next_can_state("yard", "empty_can", yard_loads=False) == "no_can",
   "a yard DROP-OFF leaves the truck empty — the can stayed at the yard")
c.close()

# The can is spoken for: a later Delivery assigned that exact can means the
# yard load is a courier run, not a swap feed. Swapping it off at an
# intervening PR would hand the wrong customer's can to the delivery.
as_boss()
r = cl.post("/api/dispatch", json={"driver_id": drv3, "route_date": "2026-11-18", "stops": [
    {"action": "YARD", "address": "2545 Squadron Ct, Virginia Beach", "customer": "The yard",
     "container_size": "30yd", "notes": "Start with #30115 container at yard"},
    {"action": "PR", "address": "401 Clearfield Ave, Chesapeake", "customer": "Balicore",
     "container_size": "30yd", "dump_leg": "Dominion"},
    {"action": "D", "address": "11496 Shiloh Dr, Virginia Beach", "customer": "Ashdon",
     "container_size": "30yd", "assigned_can": "30115"},
]}, headers=HJ)
ok(r.status_code == 200, "yard load + PR + a Delivery of that same can — status %s" % r.status_code)
c = app.get_db()
rid6 = c.execute("SELECT id FROM routes WHERE company_id=? AND route_date=?",
                 (co, "2026-11-18")).fetchone()["id"]
_fl6 = [dict(x) for x in c.execute(
    "SELECT action, can_state_before, swap_with_prev_pull FROM stops"
    " WHERE route_id=? ORDER BY stop_order, id", (rid6,)).fetchall()]
ok(_fl6[1]["swap_with_prev_pull"] == 0,
   "when a later Delivery claims can 30115, the PR stays a regular PR — the "
   "yard can is being couriered, not fed to a swap")
c.close()

# And the cab says so out loud on the next stop.
with cl.session_transaction() as s:
    s.update(user_id=drv3, company_id=co, role="driver", roles=["driver"], _csrf_token="tok")
as_boss()
r = cl.post("/api/dispatch", json={"driver_id": drv3, "route_date": _today, "stops": [
    {"action": "YARD", "address": "2545 Squadron Ct, Virginia Beach", "customer": "The yard",
     "container_size": "30yd", "notes": "Start with #30115 container at yard"},
    {"action": "PR", "address": "401 Clearfield Ave, Chesapeake", "customer": "Balicore",
     "container_size": "30yd", "dump_leg": "Dominion"},
]}, headers=HJ)
ok(r.status_code == 200, "today's flow route dispatches — status %s" % r.status_code)
c = app.get_db()
rid7 = c.execute("SELECT id FROM routes WHERE company_id=? AND assigned_to=? AND route_date=?",
                 (co, drv3, _today)).fetchone()["id"]
_pr_id = c.execute("SELECT id FROM stops WHERE route_id=? AND action='Pickup and Return'",
                   (rid7,)).fetchone()["id"]
c.close()
with cl.session_transaction() as s:
    s.update(user_id=drv3, company_id=co, role="driver", roles=["driver"], _csrf_token="tok")
cl.post("/driver/clock/in", data={"_csrf_token": "tok", "next": "/driver/route/%d" % rid7})
cl.post("/route/%d/start" % rid7, data={"_csrf_token": "tok"})
_h3 = cl.get("/driver/route/%d?show_stop=%d" % (rid7, _pr_id)).get_data(as_text=True)
ok('class="cab-card' in _h3 and "PRE-FLIGHT" not in _h3,
   "the PR card is really rendered — not the pre-flight gate")
ok("Can on board" in _h3 and "30115" in _h3,
   "the next stop's card says the can rode along, and names it: "
   "'Can on board #30115'")
# The swap step only shows once he taps Arrived (before that every PR shows
# "Arrived at Stop"), so arrive and check the step he actually gets.
cl.post("/stop/%d/driver-action" % _pr_id, data={"_csrf_token": "tok", "action": "arrived"})
_h4 = cl.get("/driver/route/%d?show_stop=%d" % (rid7, _pr_id)).get_data(as_text=True)
ok("Remove Old Container" in _h4,
   "and the work step is the SWAP one — 'Bin Out — Remove Old Container' — "
   "instead of a plain PR's 'Box Out — Remove Container'")
# (The rest of the swap sequence — Bin In, Place Empty Bin — only appears at
# later driver_status steps and is already covered by the swap-PR suites.)

# ── 12. a route dispatched BEFORE the fix heals itself ────────────────────
# Reported from the cab 2026-11-14, mid-route: the board still read
# "#3143 · returning empty" at Clearfield and would not let the stop finish,
# while the driver was already carrying 3143 to Cadence Way.
#
# can_state_before / swap_with_prev_pull are STAMPED at dispatch, not derived
# at read time. His route was dispatched before the yard fix deployed, so it
# carried the old stamp all day and the cab kept running the non-swap PR
# flow — "Return Bin — Place Empty Bin" at a customer whose empty he had
# already set down. Rendering fixes reached that route; stamped ones did not.
as_boss()
r = cl.post("/api/dispatch", json={"driver_id": drv3, "route_date": "2026-11-19", "stops": [
    {"action": "YARD", "address": "2545 Squadron Ct, Virginia Beach", "customer": "The yard",
     "container_size": "30yd", "notes": "Start with #30115 container at yard"},
    {"action": "PR", "address": "401 Clearfield Ave, Chesapeake", "customer": "Balicore",
     "container_size": "30yd", "dump_leg": "Dominion"},
    {"action": "PR", "address": "3388 Cadence Way, Virginia Beach", "customer": "Cadence",
     "container_size": "30yd", "dump_leg": "Dominion"},
]}, headers=HJ)
ok(r.status_code == 200, "a three-stop yard route dispatches — status %s" % r.status_code)
c = app.get_db()
rid8 = c.execute("SELECT id FROM routes WHERE company_id=? AND route_date=?",
                 (co, "2026-11-19")).fetchone()["id"]
# Put it back the way the OLD code left it: nothing knew about the yard load.
c.execute("""UPDATE stops SET can_state_before='no_can', swap_with_prev_pull=0
             WHERE route_id=? AND action='Pickup and Return'""", (rid8,))
c.commit()
_stale = [dict(x) for x in c.execute(
    "SELECT action, swap_with_prev_pull FROM stops WHERE route_id=? ORDER BY stop_order, id",
    (rid8,)).fetchall()]
ok(_stale[1]["swap_with_prev_pull"] == 0, "fixture really is stamped the old way")

ok(app._heal_yard_can_flow(c, rid8) is True,
   "the healer recognizes a route stamped before the yard fix and recomputes it")
c.commit()
_healed = [dict(x) for x in c.execute(
    "SELECT action, can_state_before, swap_with_prev_pull FROM stops"
    " WHERE route_id=? ORDER BY stop_order, id", (rid8,)).fetchall()]
ok(_healed[1]["can_state_before"] == "empty_can" and _healed[1]["swap_with_prev_pull"] == 1,
   "the already-dispatched route now knows he left the yard carrying a can")

# Second call writes nothing — a read-time heal must not churn every page load.
ok(app._heal_yard_can_flow(c, rid8) is False,
   "a route that is already correct is left alone — the heal only fires on "
   "stale data, so it costs a read on every other page load")

# A route with no yard stop is never touched.
ok(app._heal_yard_can_flow(c, rid3) is False,
   "a route with no yard load is not a candidate at all")
c.close()

with cl.session_transaction() as s:
    s.update(user_id=boss, company_id=co, role="boss", roles=["owner", "dispatcher"], _csrf_token="tok")
_dl = cl.get("/route/%d/daily-log" % rid8)
ok(_dl.status_code == 200, "the daily log opens on a yard route — status %s" % _dl.status_code)


# ── 13. the truck still shows a can after the yard load completes ─────────
# "It don't show that I have an container on for the next route." The carried
# bin walk (_route_final_bin_detail) had no yard branch, so a completed yard
# load fell through to the else, found no dump ticket, and set the carried bin
# to '' — the truck pill went blank at the exact moment the can went ON.
c = app.get_db()
_y8 = c.execute("SELECT id FROM stops WHERE route_id=? AND action='Yard'", (rid8,)).fetchone()["id"]
c.execute("UPDATE stops SET status='completed' WHERE id=?", (_y8,))
c.commit()
_bin, _bsize = app._route_final_bin_detail(c, rid8)
ok(_bin == "30115",
   "with only the yard load done, the truck is carrying 30115 — it was "
   "reading '' (the reported blank truck pill)")

# Then the swap PR completes with its own dump ticket: the truck now carries
# the can pulled THERE, not the one dropped off.
_pr8 = c.execute("SELECT id FROM stops WHERE route_id=? AND address LIKE '401 Clearfield%'",
                 (rid8,)).fetchone()["id"]
c.execute("UPDATE stops SET status='completed' WHERE id=?", (_pr8,))
c.execute("""INSERT INTO dump_tickets (company_id, route_id, stop_id, can_number, dump_site, created_at)
             VALUES (?,?,?,?,?,?)""", (co, rid8, _pr8, "3143", "Dominion", app.now_ts()))
c.commit()
_bin2, _ = app._route_final_bin_detail(c, rid8)
ok(_bin2 == "3143",
   "after the swap at Clearfield he carries 3143 onward to Cadence Way — "
   "not '' and not the 30115 he set down")

# An end-of-day yard stop is the opposite: the can stays at the yard.
c.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address, action,
             container_size, notes, assigned_can, status, created_at)
             VALUES (?,?,?,?,?,?,?,?, 'completed', ?)""",
          (rid8, 98, "The yard", "2545 Squadron Ct", "Yard", "30yd",
           "end of day", "3143", app.now_ts()))
c.commit()
_bin3, _ = app._route_final_bin_detail(c, rid8)
ok(_bin3 == "",
   "and an end-of-day yard drop leaves the truck empty — the can stayed there")
c.close()

print("ALL YARD-START TESTS PASSED")
