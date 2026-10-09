"""Can-swap chain fixes for the boss's 2026-10-09 dispatch text.

Route (5 PR stops):
  1. PR 3306 Peterson St, milspec, 20yd — "before you return it use it to"
  2. PR 3309 Country Mill Run, ashdon, 20yd — "then return to Peterson"
  3. PR 1013 Paragon Way, Napo, 24yd — "before you return it use it to"
  4. PR 18502 Battery Park Rd, Ew, (no size) — "then return to paragon"
  5. PR 1013 Paragon Way, Napo — standalone

Bug 1: stop 3's "use to swap" never linked to stop 4 — the positional "next"
  link was silently dropped because stop 4's size was blank (24 vs unknown).
  An unknown size can't prove a mismatch, so the boss's explicit "use it to"
  must stand.
Bug 2: "use to swap <name>" with no house number ("paragon", "Peterson")
  degraded to a positional "next", fabricating a wrong link (stop 4 -> stop 5)
  and swallowing the needs_link warning. Explicit must stay explicit.
Bug 2b: "then return to <head>" just restates the default head terminal — the
  tail->head closure already links it — so it must not nag via needs_link.

Run:  ~/workspace/.haultra-venv/bin/python tests/test_chain_swap_fixes.py
"""
import os
import sys
import tempfile
import importlib

TMP = tempfile.mkdtemp(prefix="haultra-chainfix-")
os.environ["DATABASE_PATH"] = os.path.join(TMP, "cf.db")
os.environ["SECRET_KEY"] = "cf"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import chain_resolver as cr

FAILURES = []


def ok(cond, label):
    print(("PASS" if cond else "FAIL") + " - " + label, flush=True)
    if not cond:
        FAILURES.append(label)


def mk(i, action, addr, size, note=""):
    return {"id": i, "action": action, "address": addr, "container_size": size,
            "note": note, "chain_hint": None, "manual_gives_to": None,
            "manual_delivery": None}


# ── Bug 1: "next" with unknown target size links ─────────────────────────
s = [mk(1, "Pickup and Return", "1013 Paragon Way", "24yd", note="use to swap"),
     mk(2, "Pickup and Return", "18502 Battery Park Rd", "", note="")]
res = cr.resolve_chain(s)
ok(s[0]["_chain_gives_to"] == 2 and s[1]["_chain_takes_from"] == 1,
   "bug1: 24yd 'use to swap' -> unknown-size next stop links")
ok(res["errors"] == [], "bug1: no errors from the unknown-size link")

# Unknown on the giver side also links.
s = [mk(1, "Pickup and Return", "18502 Battery Park Rd", "", note="use to swap"),
     mk(2, "Pickup and Return", "1013 Paragon Way", "24yd", note="")]
res = cr.resolve_chain(s)
ok(s[0]["_chain_gives_to"] == 2, "bug1: unknown-size giver 'use to swap' -> 24yd links")

# Guard: KNOWN mismatch still silently skips (documented behavior).
s = [mk(1, "Pull", "1 A St", "30yd", note="use to swap"),
     mk(2, "Pull", "2 B St", "20yd", note="")]
res = cr.resolve_chain(s)
ok(s[0]["_chain_gives_to"] is None and res["errors"] == [],
   "guard: known 30 vs 20 mismatch still silently skips the inferred link")

# ── Bug 2: explicit-with-nickname must not degrade to "next" ────────────
h = cr.detect_chain_hint("use to swap paragon")
ok(h == {"kind": "explicit", "target_text": "paragon"},
   "bug2: 'use to swap paragon' detects as explicit (not next)")
h = cr.detect_chain_hint("then return to Peterson")
ok(h is None or h.get("kind") != "next",
   "bug2: 'then return to Peterson' never detects as next")
h = cr.detect_chain_hint("use to swap")
ok(h == {"kind": "next"}, "bug2: bare 'use to swap' still detects as next")

s = [mk(1, "Pickup and Return", "18502 Battery Park Rd", "", note="use to swap paragon"),
     mk(2, "Pickup and Return", "1013 Paragon Way", "", note="")]
res = cr.resolve_chain(s)
ok(s[0]["_chain_gives_to"] is None,
   "bug2: unmatched nickname target creates NO fabricated link")
ok(any(n.get("target_text") == "paragon" for n in res["needs_link"]),
   "bug2: unmatched 'paragon' surfaces via needs_link for manual linking")

# ── Bug 2b: "return to <head>" restates the default — no nag ─────────────
s = [mk(1, "Pickup and Return", "3306 Peterson St", "20yd", note="use to swap"),
     mk(2, "Pickup and Return", "3309 Country Mill Run", "20yd", note="use to swap Peterson")]
res = cr.resolve_chain(s)
ok(s[0]["_chain_gives_to"] == 2 and s[1]["_chain_takes_from"] == 1,
   "bug2b: stop1 -> stop2 positional link forms")
ok(s[1]["_chain_gives_to"] == 1 and s[1]["_chain_terminal"] == "head",
   "bug2b: tail->head closure links stop2 back to stop1")
ok(not any(n.get("target_text") == "Peterson" for n in res["needs_link"]),
   "bug2b: 'return to Peterson' (== head) does not nag via needs_link")

# Non-head unmatched target still warns.
s = [mk(1, "Pickup and Return", "3306 Peterson St", "20yd", note="use to swap"),
     mk(2, "Pickup and Return", "3309 Country Mill Run", "20yd", note="use to swap nowhereville")]
res = cr.resolve_chain(s)
ok(any(n.get("target_text") == "nowhereville" for n in res["needs_link"]),
   "bug2b: genuinely unmatched target still warns via needs_link")

# ── End-to-end: the boss's 10/9 route resolves to two 2-stop chains ───────
s = [mk(1, "Pickup and Return", "3306 Peterson St", "20yd", note="use to swap"),
     mk(2, "Pickup and Return", "3309 Country Mill Run", "20yd", note="use to swap Peterson"),
     mk(3, "Pickup and Return", "1013 Paragon Way", "24yd",
        note="can ref 3089; vista site use to swap"),
     mk(4, "Pickup and Return", "18502 Battery Park Rd", "", note="use to swap paragon"),
     mk(5, "Pickup and Return", "1013 Paragon Way", "", note="")]
res = cr.resolve_chain(s)
ok(res["errors"] == [], "e2e: no blocking errors on the 10/9 route")
ok(s[0]["_chain_gives_to"] == 2 and s[1]["_chain_gives_to"] == 1,
   "e2e: stops 1<->2 form the milspec/ashdon chain")
ok(s[2]["_chain_gives_to"] == 4 and s[3]["_chain_gives_to"] == 3,
   "e2e: stops 3<->4 form the Napo/Ew chain (stop3's swap now shows)")
ok(s[4]["_chain_group_id"] is None and s[4]["_chain_gives_to"] is None,
   "e2e: stop 5 stands alone (not dragged into a bogus chain)")
ok(s[0]["_chain_group_id"] != s[2]["_chain_group_id"],
   "e2e: the two pairs are separate chains")
flows = cr.render_flows([dict(id=x["id"], address=x["address"],
                              chain_group_id=x["_chain_group_id"], chain_seq=x["_chain_seq"],
                              chain_gives_to_stop_id=x["_chain_gives_to"],
                              chain_takes_from_stop_id=x["_chain_takes_from"],
                              chain_terminal=x["_chain_terminal"], chain_start=x["_chain_start"],
                              chain_delivery_stop_id=x["_chain_delivery"]) for x in s])
ok("3309 Country Mill Run" in (flows[1]["gives"] or ""),
   "e2e: stop 1 renders 'Empty goes to 3309 Country Mill Run'")
ok("18502 Battery Park Rd" in (flows[3]["gives"] or ""),
   "e2e: stop 3 renders 'Empty goes to 18502 Battery Park Rd'")

print()
if FAILURES:
    print("FAILURES (%d):" % len(FAILURES))
    for f in FAILURES:
        print("  - " + f)
    sys.exit(1)
print("ALL CHECKS PASSED")

# ── Fix 3: pre-tap Navigate panel on the chained need_box_in card ────────
# The driver holds the empty and the deliver-step button both names the
# destination AND completes the stop — the card must offer navigation to the
# handoff stop BEFORE the confirming tap.
import app as _app

_app.init_db()
_conn = _app.get_db()
_cur = _conn.cursor()
_ts = _app.now_ts()
_cur.execute("INSERT INTO companies (name, slug, subscription_plan, subscription_status, max_drivers, created_at)"
             " VALUES (?,?,?,?,?,?)", ("Nav Co", "navco", "pro", "active", 10, _ts))
_nco = _cur.lastrowid
_cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id, created_at)"
             " VALUES (?,?,?,?,?,?)", ("nav_drv", "x", "driver", "Nav Driver", _nco, _ts))
_ndrv = _cur.lastrowid
_cur.execute("INSERT INTO routes (company_id, route_date, route_name, created_by, assigned_to, status, created_at)"
             " VALUES (?,?,?,?,?,'in_progress',?)", (_nco, "2026-10-09", "NAV", _ndrv, _ndrv, _ts))
_nrid = _cur.lastrowid
_cur.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address, city, state, action,
                container_size, dump_location, notes, driver_status, arrived_at, status, created_at)
                VALUES (?,?,?,?, '', 'VA','Pickup and Return', ?, 'D', ?, 'need_box_in', ?, 'open', ?)""",
             (_nrid, 1, "milspec", "3306 Peterson St", "20yd", "use to swap", _ts, _ts))
_ns1 = _cur.lastrowid
_cur.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address, city, state, action,
                container_size, dump_location, notes, driver_status, status, created_at)
                VALUES (?,?,?,?, '', 'VA','Pickup and Return', ?, 'D', ?, 'pending', 'open', ?)""",
             (_nrid, 2, "ashdon", "3309 Country Mill Run", "20yd", "use to swap Peterson", _ts))
_ns2 = _cur.lastrowid
_conn.commit()
_app._apply_route_chains(_conn, _nrid)
_conn.commit()
_conn.close()

_app.app.config["TESTING"] = True
_cl = _app.app.test_client()
with _cl.session_transaction() as _s:
    _s.update(user_id=_ndrv, company_id=_nco, role="driver", roles=["driver"], _csrf_token="tok")
_r = _cl.get("/driver/route/%d" % _nrid)
_html = _r.get_data(as_text=True)
ok(_r.status_code == 200, "fix3: driver route page renders (200)")
ok("Empty goes to" in _html and "3309 Country Mill Run" in _html,
   "fix3: need_box_in card shows the handoff destination before the tap")
ok("openNavStop" in _html, "fix3: handoff destination has a Navigate action")
# The confirming button is still there, unchanged.
ok("Deliver Empty to" in _html and "3309 Country Mill Run" in _html,
   "fix3: the confirming deliver-step button still renders")

print()
if FAILURES:
    print("FAILURES (%d):" % len(FAILURES))
    for f in FAILURES:
        print("  - " + f)
    sys.exit(1)
print("ALL CHECKS PASSED")
