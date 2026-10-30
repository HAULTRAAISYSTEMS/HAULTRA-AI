"""Truck-to-truck meets: hand a can over, or carry a driver.

2026-10-30. Neither was dispatchable. A can handed between trucks had to be
typed as a Delivery plus a Pull at a made-up address, which told the bin
tracker the can had gone to a customer; a driver whose truck was down and
needed carrying to a spare had no stop at all, so neither board showed where
he was.

Both are "meet the other truck", so both are one mechanism: a PAIR of stops,
one per driver, tied by transfer_group_id and pointing at each other, so a
meeting can never exist on one board and not the other.

The load-following assertions matter most. The truck's load is replayed from
completed stops, so a Transfer that the replay ignores leaves the giver
holding a can he physically handed away -- the same phantom-can shape as the
chained-Delivery bug fixed on 2026-10-27.

Run:  python3 tests/test_truck_meets.py
"""
import os
import sys
import json
import tempfile
import importlib

TMP = tempfile.mkdtemp(prefix="haultra-meet-")
os.environ["DATABASE_PATH"] = os.path.join(TMP, "m.db")
os.environ["SECRET_KEY"] = "m"
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
            ("Meet Co", "meetco", "pro", "active", 10, ts))
co = cur.lastrowid


def mkuser(uname, role, full):
    cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
                " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
                (uname, "x", role, full, co, ts))
    conn.commit()
    return cur.lastrowid


boss = mkuser("mboss", "boss", "M Boss")
tim = mkuser("mtim", "driver", "TIM")
malik = mkuser("mmalik", "driver", "Malik Freeman")
spare = mkuser("mspare", "driver", "Spare Driver")

app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=boss, company_id=co, role="boss", roles=["boss", "owner"],
             _csrf_token="tok")


def post(path, payload, client=None):
    c = client or cl
    return c.post(path, data=json.dumps(payload), content_type="application/json",
                  headers={"X-CSRF-Token": "tok"})


def stop(sid):
    return dict(conn.execute("SELECT * FROM stops WHERE id=?", (sid,)).fetchone())


# ══════════════════════════════════════════════════════════════════
# 1. Handing a can to another driver
# ══════════════════════════════════════════════════════════════════
print("\n-- can transfer --")
r = post("/api/dispatch/truck-meet", {
    "kind": "can", "from_driver_id": tim, "to_driver_id": malik,
    "address": "Dominion Landfill", "can": "3080", "note": "he needs it for Heartland"})
ok(r.status_code == 200, "dispatch succeeds (got %d)" % r.status_code)
j = r.get_json() or {}
a, b = stop(j["from_stop_id"]), stop(j["to_stop_id"])

ok(a["route_id"] != b["route_id"], "the pair lands on two different routes")
ok(a["action"] == "Transfer" and b["action"] == "Transfer", "both halves are Transfer stops")
ok(a["transfer_role"] == "give" and b["transfer_role"] == "take",
   "roles are give / take (got %r / %r)" % (a["transfer_role"], b["transfer_role"]))
ok(a["transfer_group_id"] == b["transfer_group_id"], "both carry one group id")
ok(a["transfer_peer_stop_id"] == b["id"] and b["transfer_peer_stop_id"] == a["id"],
   "each half points at the other")
ok(a["transfer_user_id"] == malik and b["transfer_user_id"] == tim,
   "each half names the other driver")
ok(a["transfer_can"] == "3080" and b["transfer_can"] == "3080", "both record the can")
ok("Dominion" in (a["address"] or "") and "Dominion" in (b["address"] or ""),
   "both carry the meeting place so Navigate works on each side")
ok("Malik" in (a["customer_name"] or ""), "the giver's card names who is taking it")
ok("TIM" in (b["customer_name"] or ""), "the taker's card names who is giving it")

# Both drivers are told, in their own words.
msgs_a = [m["body"] for m in conn.execute(
    "SELECT body FROM messages WHERE route_id=?", (a["route_id"],)).fetchall()]
msgs_b = [m["body"] for m in conn.execute(
    "SELECT body FROM messages WHERE route_id=?", (b["route_id"],)).fetchall()]
ok(any("hand over" in m for m in msgs_a), "the giver is told to hand it over")
ok(any("pick up" in m for m in msgs_b), "the taker is told to pick it up")
ok(any("Heartland" in m for m in msgs_a), "the boss's note reaches both")
ok(any("Heartland" in m for m in msgs_b), "the boss's note reaches both (2)")


# ══════════════════════════════════════════════════════════════════
# 2. The can actually moves trucks
# ══════════════════════════════════════════════════════════════════
print("\n-- the bin tracker follows the can --")
# TIM pulls 3080 and dumps it, so it is genuinely on his truck.
cur.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address, city, state,
               action, container_size, status, completed_at, created_at)
               VALUES (?,0,'Heartland','630 Washington Park','Norfolk','VA','Pull','30yd',
                       'completed',?,?)""", (a["route_id"], ts, ts))
pull_id = cur.lastrowid
cur.execute("INSERT INTO dump_tickets (stop_id, route_id, company_id, dump_site, can_number,"
            " created_at) VALUES (?,?,?,?,?,?)",
            (pull_id, a["route_id"], co, "Dominion", "3080", ts))
conn.commit()
bin_tim, _ = app._route_final_bin_detail(conn, a["route_id"])
ok(bin_tim == "3080", "TIM is carrying 3080 after the pull (got %r)" % bin_tim)
bin_malik, _ = app._route_final_bin_detail(conn, b["route_id"])
ok(bin_malik == "", "Malik is empty before the meet (got %r)" % bin_malik)

# The meet happens.
conn.execute("UPDATE stops SET status='completed', completed_at=? WHERE id IN (?,?)",
             (ts, a["id"], b["id"]))
conn.commit()
bin_tim2, _ = app._route_final_bin_detail(conn, a["route_id"])
ok(bin_tim2 == "",
   "TIM's truck is empty after handing it over — no phantom can (got %r)" % bin_tim2)
bin_malik2, sz = app._route_final_bin_detail(conn, b["route_id"])
ok(bin_malik2 == "3080", "the can is now on Malik's truck (got %r)" % bin_malik2)


# ══════════════════════════════════════════════════════════════════
# 3. Carrying a driver
# ══════════════════════════════════════════════════════════════════
print("\n-- driver ride --")
r = post("/api/dispatch/truck-meet", {
    "kind": "ride", "from_driver_id": malik, "to_driver_id": spare,
    "address": "770 Industrial Pkwy", "note": "his truck is down"})
ok(r.status_code == 200, "ride dispatch succeeds (got %d)" % r.status_code)
j2 = r.get_json() or {}
ra, rb = stop(j2["from_stop_id"]), stop(j2["to_stop_id"])
ok(ra["action"] == "Ride" and rb["action"] == "Ride", "both halves are Ride stops")
ok(ra["transfer_role"] == "driver" and rb["transfer_role"] == "rider",
   "roles are driver / rider (got %r / %r)" % (ra["transfer_role"], rb["transfer_role"]))
ok("Spare" in (ra["customer_name"] or ""), "the driver's card says who to pick up")
ok((ra["transfer_can"] or "") == "" and (rb["transfer_can"] or "") == "",
   "a ride records no can")

# A ride must not disturb the truck's load.
_before, _ = app._route_final_bin_detail(conn, rb["route_id"])
conn.execute("UPDATE stops SET status='completed', completed_at=? WHERE id IN (?,?)",
             (ts, ra["id"], rb["id"]))
conn.commit()
_after_driver, _ = app._route_final_bin_detail(conn, ra["route_id"])
_after_rider, _ = app._route_final_bin_detail(conn, rb["route_id"])
ok(_after_rider == _before,
   "a completed ride leaves the rider's load untouched (%r -> %r)" % (_before, _after_rider))
ok(_after_driver == "3080",
   "and the carrying driver keeps whatever was on his truck (got %r)" % _after_driver)


# ══════════════════════════════════════════════════════════════════
# 4. Guards
# ══════════════════════════════════════════════════════════════════
print("\n-- guards --")
r = post("/api/dispatch/truck-meet",
         {"kind": "can", "from_driver_id": tim, "to_driver_id": tim, "address": "Yard"})
ok(r.status_code == 400, "a driver cannot meet himself (got %d)" % r.status_code)
r = post("/api/dispatch/truck-meet",
         {"kind": "can", "from_driver_id": tim, "to_driver_id": malik})
ok(r.status_code == 400, "a meeting place is required (got %d)" % r.status_code)
r = post("/api/dispatch/truck-meet",
         {"kind": "teleport", "from_driver_id": tim, "to_driver_id": malik, "address": "Yard"})
ok(r.status_code == 400, "an unknown kind is rejected (got %d)" % r.status_code)
r = post("/api/dispatch/truck-meet",
         {"kind": "can", "from_driver_id": tim, "to_driver_id": 99999, "address": "Yard"})
ok(r.status_code == 404, "an unknown driver is rejected (got %d)" % r.status_code)
# The boss of another company must not reach these drivers.
cur.execute("INSERT INTO companies (name, slug, subscription_plan, subscription_status,"
            " max_drivers, created_at) VALUES (?,?,?,?,?,?)",
            ("Other Co", "otherco", "pro", "active", 10, ts))
co2 = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
            " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
            ("oboss", "x", "boss", "O Boss", co2, ts))
oboss = cur.lastrowid
conn.commit()
ocl = app.app.test_client()
with ocl.session_transaction() as s:
    s.update(user_id=oboss, company_id=co2, role="boss", roles=["boss", "owner"],
             _csrf_token="tok")
r = post("/api/dispatch/truck-meet",
         {"kind": "can", "from_driver_id": tim, "to_driver_id": malik, "address": "Yard"},
         client=ocl)
ok(r.status_code == 404, "another company's boss cannot pair our drivers (got %d)" % r.status_code)
# A driver cannot dispatch meets.
dcl = app.app.test_client()
with dcl.session_transaction() as s:
    s.update(user_id=tim, company_id=co, role="driver", roles=["driver"], _csrf_token="tok")
r = post("/api/dispatch/truck-meet",
         {"kind": "can", "from_driver_id": tim, "to_driver_id": malik, "address": "Yard"},
         client=dcl)
ok(r.status_code in (302, 401, 403), "a driver cannot dispatch a meet (got %d)" % r.status_code)

print("\n-- the driver screens survive the new stop types --")
# A new action that renders fine on the boss board but 500s in the cab is a
# driver stranded mid-route, so both sides get smoked out here.
for _uid, _name in ((tim, "TIM"), (malik, "Malik"), (spare, "Spare")):
    _c = app.app.test_client()
    with _c.session_transaction() as s:
        s.update(user_id=_uid, company_id=co, role="driver", roles=["driver"],
                 _csrf_token="tok")
    _rid = app.driver_active_route_id(conn, _uid)
    if not _rid:
        continue
    _r = _c.get("/driver/route/%d" % _rid)
    ok(_r.status_code == 200,
       "%s's cab view renders with meet stops (got %d)" % (_name, _r.status_code))
    _r2 = _c.get("/driver")
    ok(_r2.status_code in (200, 302),
       "%s's driver dashboard renders (got %d)" % (_name, _r2.status_code))

_bc = app.app.test_client()
with _bc.session_transaction() as s:
    s.update(user_id=boss, company_id=co, role="boss", roles=["boss", "owner"],
             _csrf_token="tok")
for _rid in {a["route_id"], b["route_id"], ra["route_id"], rb["route_id"]}:
    _r = _bc.get("/route/%d" % _rid)
    ok(_r.status_code == 200, "the boss route board renders route %d (got %d)" % (_rid, _r.status_code))
ok(_bc.get("/boss").status_code == 200, "the owner dashboard still renders")
ok(_bc.get("/dashboard").status_code == 200, "the dispatch dashboard still renders")

print("\n-- no orphans --")
_orphans = conn.execute(
    """SELECT COUNT(*) c FROM stops
        WHERE transfer_group_id IS NOT NULL
          AND (transfer_peer_stop_id IS NULL
               OR transfer_peer_stop_id NOT IN (SELECT id FROM stops))"""
).fetchone()["c"]
ok(_orphans == 0, "every meet stop has a live peer (got %d orphans)" % _orphans)
_groups = conn.execute(
    """SELECT transfer_group_id, COUNT(*) c FROM stops
        WHERE transfer_group_id IS NOT NULL GROUP BY transfer_group_id"""
).fetchall()
ok(_groups and all(g["c"] == 2 for g in _groups),
   "every group is exactly two stops (%r)" % [g["c"] for g in _groups])

print("\n%d failure(s)" % len(FAILURES))
for f in FAILURES:
    print("  FAILED: " + f)
sys.exit(1 if FAILURES else 0)
