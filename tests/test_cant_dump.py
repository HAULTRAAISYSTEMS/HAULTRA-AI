"""Couldn't dump — landfill closed, can goes home full (feat/couldnt-dump-take-to-yard).

Reported from the cab, 2026-11-14, at stop 5 of 5:

    "So when an driver can't dump the last container because the landfill
     closed. The container is full and I'm taking it back to the yard .. i
     think we should add this."

and, on whether the customer was left short:

    "I swapped it out so it's one there"

So the CUSTOMER side of that job is finished — on a swap they already have
their empty. This is emphatically not a cancel: cancelling would erase a
completed service and a real haul. What is outstanding is the dump, and with
it the ticket and the tonnage.

Three facts have to survive the night, and none of them did before:
  1. the job is done and billable (minus its disposal line)
  2. the dump is still owed — _stop_disposal_cents is tons x rate, so
     invoicing before the ticket exists bills short
  3. the can is in the yard but NOT available — handing it to tomorrow's
     delivery as an empty is the expensive mistake

The schema for this was scaffolded long ago and never wired: route_exceptions
already had type='DISPOSAL_CLOSED' and resolution='TAKE_TO_YARD' as CHECK
values with nothing in the app able to produce them. The only writer was the
App Store demo seeder.
"""
import os, sys, tempfile, importlib
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "cantdump.db")
os.environ["SECRET_KEY"] = "cantdump"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")

def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c:
        raise SystemExit("FAILED: " + m)

# 2026-11-17: fixture dates are derived from today, never written literally.
# A driver may hold only one route per date, and this file also needs a route
# dated TODAY for the cab. Hard-coded dates meant that on one particular day of
# the year the two collided and the suite failed with nothing in the app
# changed — which is exactly what happened to test_yard_start.
import datetime as _dt
_TODAY = app.now_ts()[:10]
def _day(n):
    return (_dt.date.fromisoformat(_TODAY) + _dt.timedelta(days=n)).isoformat()

app.init_db()
conn = app.get_db(); cur = conn.cursor(); ts = app.now_ts()
cur.execute("""INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,
               yard_address,yard_city,created_at) VALUES (?,?,?,?,?,?,?,?)""",
            ("DumpCo", "dumpco", "pro", "active", 10, "2545 Squadron Ct", "Virginia Beach", ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("d_boss", "x", "boss", "Boss", co, ts)); boss = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("d_drv", "x", "driver", "Tim", co, ts)); drv = cur.lastrowid
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


# ── 1. the fleet state exists and means "not available" ───────────────────
c = app.get_db()
_sql = c.execute("SELECT sql FROM sqlite_master WHERE type='table' AND name='containers'").fetchone()["sql"]
ok("full_at_yard" in _sql,
   "containers accepts 'full_at_yard' — the comment in the migration asked for "
   "this state years before the rebuild actually added it")
c.execute("""INSERT INTO containers (company_id,size,label,status,created_at)
             VALUES (?,?,?,?,?)""", (co, "30yd", "9001", "full_at_yard", app.now_ts()))
c.execute("""INSERT INTO containers (company_id,size,label,status,created_at)
             VALUES (?,?,?,?,?)""", (co, "30yd", "9002", "yard", app.now_ts()))
c.commit()
_avail = [dict(x)["label"] for x in c.execute(
    "SELECT label FROM containers WHERE company_id=? AND status='yard'", (co,)).fetchall()]
ok(_avail == ["9002"],
   "a full can is NOT in the available-at-yard list — every picker, count and "
   "bulk-deploy filters status='yard' exactly, so it is excluded by being its "
   "own state (handing it out as an empty is the expensive mistake)")
c.close()


# ── 2. the driver reports it ───────────────────────────────────────────────
as_boss()
r = cl.post("/api/dispatch", json={"driver_id": drv, "route_date": _day(1), "stops": [
    {"action": "PR", "address": "529 Whispering Oaks Cir, Chesapeake", "customer": "Craftsman",
     "container_size": "30yd", "dump_leg": "Dominion"},
    {"action": "D", "address": "11496 Shiloh Dr, Virginia Beach", "customer": "Ashdon",
     "container_size": "30yd"},
]}, headers=HJ)
ok(r.status_code == 200, "the day dispatches — status %s" % r.status_code)
c = app.get_db()
rid = c.execute("SELECT id FROM routes WHERE company_id=?", (co,)).fetchone()["id"]
_pr = c.execute("SELECT id FROM stops WHERE route_id=? AND customer_name='Craftsman'",
                (rid,)).fetchone()["id"]
_del = c.execute("SELECT id FROM stops WHERE route_id=? AND customer_name='Ashdon'",
                 (rid,)).fetchone()["id"]
c.close()

as_driver()
r = cl.post("/api/stops/%d/cant-dump" % _pr,
            json={"can": "3143", "note": "Dominion shut at noon", "client_uuid": "u-1"},
            headers=HJ)
ok(r.status_code == 200 and r.get_json().get("success"),
   "the driver can report it — status %s %s" % (r.status_code, r.get_json()))

c = app.get_db()
_ex = c.execute("SELECT * FROM route_exceptions WHERE company_id=? AND stop_id=?",
                (co, _pr)).fetchone()
ok(_ex is not None, "a route_exceptions row is written — the table finally has a real writer")
ok(dict(_ex)["type"] == "DISPOSAL_CLOSED",
   "typed DISPOSAL_CLOSED, the CHECK value that was already waiting for it")
ok(dict(_ex)["resolution"] == "TAKE_TO_YARD",
   "resolved TAKE_TO_YARD — the driver already decided by driving home")
ok("3143" in (dict(_ex)["container_state_at_time"] or ""),
   "and it records what was on the truck at the time")

_st = dict(c.execute("SELECT * FROM stops WHERE id=?", (_pr,)).fetchone())
ok(_st["status"] == "completed",
   "the STOP completes — he swapped, so Craftsman has their can. This is not "
   "a cancel; cancelling would erase a finished service and a real haul")
ok((_st["dump_deferred_at"] or "") != "" and _st["dump_deferred_can"] == "3143",
   "but it is flagged as owing a dump, naming the can")

_can = dict(c.execute("SELECT * FROM containers WHERE company_id=? AND label='3143'",
                      (co,)).fetchone())
ok(_can["status"] == "full_at_yard",
   "can 3143 is in the yard FULL — not 'yard', which would offer it to the "
   "next customer as an empty")

_msg = c.execute("SELECT body FROM messages WHERE route_id=? ORDER BY id DESC LIMIT 1",
                 (rid,)).fetchone()
ok(_msg is not None and "3143" in _msg["body"],
   "the boss is told, with the can number")
c.close()

# Retry from a dead zone is the same exception, not a second one.
r = cl.post("/api/stops/%d/cant-dump" % _pr,
            json={"can": "3143", "client_uuid": "u-1"}, headers=HJ)
ok(r.status_code == 200 and r.get_json().get("duplicate") is True,
   "a replayed POST is recognised as the same report — the table's "
   "UNIQUE(company_id, client_uuid) is what makes that possible")
c = app.get_db()
ok(c.execute("SELECT COUNT(*) n FROM route_exceptions WHERE company_id=?",
             (co,)).fetchone()["n"] == 1, "still exactly one exception on file")
c.close()

# A Delivery has nothing on the truck to defer.
r = cl.post("/api/stops/%d/cant-dump" % _del,
            json={"can": "3143", "client_uuid": "u-2"}, headers=HJ)
ok(r.status_code == 400,
   "a Delivery is refused — it drops a can off and drives away empty, so "
   "there is nothing to fail to dump")

# No can number, no report: the whole point is knowing which can is full.
r = cl.post("/api/stops/%d/cant-dump" % _pr,
            json={"can": "", "client_uuid": "u-3"}, headers=HJ)
ok(r.status_code == 400, "a blank can number is refused")


# ── 3. the invoice says the ticket is still owed ───────────────────────────
# A real rate card, or there would be no haul line to compare against and the
# assertion below would pass for the wrong reason (an empty invoice).
c = app.get_db()
c.execute("INSERT INTO rate_cards (company_id, service, tier, cents) VALUES (?,?,?,?)",
          (co, "swap", "standard", 45000))
c.execute("INSERT INTO rate_cards (company_id, service, tier, cents) VALUES (?,?,?,?)",
          (co, "disposal", "*", 5500))
c.commit()
_lines = app._build_invoice_lines_for_route(c, co, rid)
c.close()
_pending = [l for l in _lines if "Disposal pending" in (l.get("description") or "")]
ok(len(_pending) == 1,
   "the invoice carries a 'Disposal pending' line for the undumped job — "
   "_stop_disposal_cents is tons x rate, so without this the sheet just "
   "silently omits disposal and nobody notices until the month closes")
ok(_pending[0]["amount_cents"] == 0,
   "it is a zero line — a note that a ticket is owed, never an invented charge")
ok("3143" in _pending[0]["description"], "and it names the can")
ok(any(l.get("amount_cents") == 45000 for l in _lines),
   "the haul still bills at full price — the work happened, he swapped the "
   "can; only the disposal is outstanding")
ok(not any(l.get("kind") == "disposal" for l in _lines),
   "and no disposal is charged yet — there are no tons to charge for, which "
   "is exactly the silence the pending line breaks")


# ── 4. it rolls onto the next route dispatched ─────────────────────────────
as_boss()
r = cl.post("/api/dispatch", json={"driver_id": drv, "route_date": _day(2), "stops": [
    {"action": "P", "address": "401 Clearfield Ave, Chesapeake", "customer": "Balicore",
     "container_size": "30yd"},
]}, headers=HJ)
ok(r.status_code == 200, "the next day dispatches — status %s" % r.status_code)
c = app.get_db()
rid2 = c.execute("SELECT id FROM routes WHERE company_id=? AND route_date=?",
                 (co, _day(2))).fetchone()["id"]
_catch = c.execute(
    "SELECT * FROM stops WHERE route_id=? AND deferred_for_stop_id IS NOT NULL",
    (rid2,)).fetchone()
ok(_catch is not None,
   "a catch-up dump is waiting on the next route — at 6pm when he reported it "
   "there was no tomorrow to put it on, so it is added when one exists")
_catch = dict(_catch)
ok(_catch["deferred_for_stop_id"] == _pr,
   "and it points back at Craftsman's job, which is whose tonnage this is")
ok(_catch["assigned_can"] == "3143", "carrying the right can")
ok("Craftsman" in (_catch["notes"] or ""),
   "the note says where it came from, so the driver knows why he is at the dump")
c.close()

# Dispatching again must not queue the same can twice.
as_boss()
r = cl.post("/api/dispatch", json={"driver_id": drv, "route_date": _day(3), "stops": [
    {"action": "P", "address": "1994 Tiger Dr, Virginia Beach", "customer": "Tiger",
     "container_size": "30yd"},
]}, headers=HJ)
ok(r.status_code == 200, "and a third day dispatches — status %s" % r.status_code)
c = app.get_db()
_n = c.execute(
    """SELECT COUNT(*) n FROM stops s JOIN routes r ON r.id=s.route_id
        WHERE r.company_id=? AND s.deferred_for_stop_id IS NOT NULL""", (co,)).fetchone()["n"]
ok(_n == 1,
   "still ONE catch-up stop — a can already queued is not dumped twice")
c.close()


# ── 5. the ticket settles on the ORIGINAL job ─────────────────────────────
as_driver()
r = cl.post("/stop/%d/dump-ticket" % _catch["id"], data={
    "_csrf_token": "tok", "dump_site": "Dominion", "can_number": "3143",
    "net_tons": "6.4", "ticket_number": "T-777",
}, follow_redirects=True)
ok(r.status_code in (200, 302), "the catch-up dump's ticket saves — status %s" % r.status_code)

c = app.get_db()
_orig = dict(c.execute("SELECT * FROM stops WHERE id=?", (_pr,)).fetchone())
ok(float(_orig["weight_tons"] or 0) == 6.4,
   "the tonnage lands on CRAFTSMAN's job, not on the catch-up stop — that is "
   "whose disposal it is, and the catch-up stop belongs to no customer")
ok((_orig["dump_deferred_at"] or "") == "",
   "and the job stops owing a ticket")
_can2 = dict(c.execute("SELECT * FROM containers WHERE company_id=? AND label='3143'",
                       (co,)).fetchone())
ok(_can2["status"] == "yard",
   "can 3143 is finally a plain empty in the yard — available again now that "
   "it is actually empty")
c.close()

# And the invoice stops saying a ticket is owed.
c = app.get_db()
_lines2 = app._build_invoice_lines_for_route(c, co, rid)
c.close()
ok(not any("Disposal pending" in (l.get("description") or "") for l in _lines2),
   "the 'Disposal pending' line is gone once the ticket exists")


# ── 6. the cab offers it, and only where it makes sense ───────────────────
as_boss()
_today = _TODAY
r = cl.post("/api/dispatch", json={"driver_id": drv, "route_date": _today, "stops": [
    {"action": "PR", "address": "529 Whispering Oaks Cir, Chesapeake", "customer": "Craftsman",
     "container_size": "30yd", "dump_leg": "Dominion"},
    {"action": "D", "address": "11496 Shiloh Dr, Virginia Beach", "customer": "Ashdon",
     "container_size": "30yd"},
]}, headers=HJ)
ok(r.status_code == 200, "today's route dispatches — status %s" % r.status_code)
c = app.get_db()
rid3 = c.execute("SELECT id FROM routes WHERE company_id=? AND route_date=?",
                 (co, _today)).fetchone()["id"]
_pr3 = c.execute("SELECT id FROM stops WHERE route_id=? AND customer_name='Craftsman'",
                 (rid3,)).fetchone()["id"]
_del3 = c.execute("SELECT id FROM stops WHERE route_id=? AND customer_name='Ashdon'",
                  (rid3,)).fetchone()["id"]
c.close()
as_driver()
cl.post("/driver/clock/in", data={"_csrf_token": "tok", "next": "/driver/route/%d" % rid3})
cl.post("/route/%d/start" % rid3, data={"_csrf_token": "tok"})
_h = cl.get("/driver/route/%d?show_stop=%d" % (rid3, _pr3)).get_data(as_text=True)
ok('class="cab-card' in _h and "PRE-FLIGHT" not in _h, "the cab card renders")
# Match the BUTTON, not the phrase: the Cancel modal's help text also says
# "Couldn't dump" (pointing the driver here instead), and it is on every page.
ok('onclick="cabCantDump(' in _h,
   "the PR stop offers 'Couldn't dump — landfill closed'")
_hd = cl.get("/driver/route/%d?show_stop=%d" % (rid3, _del3)).get_data(as_text=True)
ok('onclick="cabCantDump(' not in _hd,
   "a Delivery does not — there is nothing on the truck to dump")


# ── 7. the rename ──────────────────────────────────────────────────────────
ok(">Cancel<" in _h,
   "'Can't run this' now reads 'Cancel' — honest only now that a driver who "
   "couldn't dump has somewhere else to go")
ok("run this" not in _h, "and the old wording is gone from the cab")

print("ALL CANT-DUMP TESTS PASSED")
