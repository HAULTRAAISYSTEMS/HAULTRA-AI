import os, sys, tempfile, importlib, io
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "cs.db")
os.environ["SECRET_KEY"] = "cs"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")
import chain_resolver as cr

def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c:
        raise SystemExit("FAILED: " + m)

# ── 1) Idempotent migrations ────────────────────────────────────────────────
app.init_db(); app.init_db()
conn = app.get_db()
scol = {r[1] for r in conn.execute("PRAGMA table_info(stops)").fetchall()}
acol = {r[1] for r in conn.execute("PRAGMA table_info(saved_addresses)").fetchall()}
for c in ("chain_group_id", "chain_seq", "chain_gives_to_stop_id", "chain_takes_from_stop_id",
          "chain_terminal", "chain_target_ref", "chain_source", "ticket_source"):
    ok(c in scol, "stops.%s exists after repeated init_db (idempotent)" % c)
ok("issues_tickets" in acol, "saved_addresses.issues_tickets exists (idempotent)")
conn.close()

# ── resolver unit helpers ───────────────────────────────────────────────────
def mk(i, action, addr, size, note="", hint=None, manual=None):
    return {"id": i, "action": action, "address": addr, "container_size": size,
            "note": note, "chain_hint": hint, "manual_gives_to": manual}

# 2) The exact two-line input -> 2-stop chain, tail gives_to head.
s = [mk(1, "Pickup and Return", "1351 Virginia Beach Blvd", "30yd", note="use to swap"),
     mk(2, "Pickup and Return", "5125 Ballahack Rd", "30yd")]
cr.resolve_chain(s)
ok(s[0]["_chain_seq"] == 0 and s[1]["_chain_seq"] == 1, "2-line: seq 0,1")
ok(s[0]["_chain_gives_to"] == 2 and s[1]["_chain_gives_to"] == 1 and s[1]["_chain_terminal"] == "head",
   "2-line: tail gives_to = head, terminal head")

# 3) 4 consecutive PRs, "swap till end" on stop 1 -> seq 0..3, tail->head, 4 trips.
s = [mk(i, "Pickup and Return", "%d00 St" % i, "30yd", note=("swap till end" if i == 1 else "")) for i in range(1, 5)]
cr.resolve_chain(s)
ok([x["_chain_seq"] for x in s] == [0, 1, 2, 3], "swap-till-end: seq 0..3 across the full run")
ok(s[3]["_chain_gives_to"] == 1 and s[3]["_chain_terminal"] == "head", "swap-till-end: tail returns to head")
ok(len({x["_chain_group_id"] for x in s}) == 1, "swap-till-end: one chain group = 4 dump trips")

# 4) Same + "back to yard" on the tail -> terminal yard + INFO on head.
s = [mk(i, "Pickup and Return", "%d00 St" % i, "30yd",
        note=("swap till end" if i == 1 else ("back to yard" if i == 4 else ""))) for i in range(1, 5)]
res = cr.resolve_chain(s)
ok(s[3]["_chain_terminal"] == "yard" and s[3]["_chain_gives_to"] is None, "back-to-yard: terminal yard, no return link")
ok(any("no can" in inf["msg"] for inf in res["infos"]), "back-to-yard: INFO notice on the head")

# 5) Bare "use to swap" on stop 1 of a 4-PR run -> chain extends the full run.
s = [mk(i, "Pickup and Return", "%d00 St" % i, "30yd", note=("use to swap" if i == 1 else "")) for i in range(1, 5)]
cr.resolve_chain(s)
ok([x["_chain_seq"] for x in s] == [0, 1, 2, 3], "bare use-to-swap: extends the full run")

# 6) Run broken by a D stop mid-run -> two separate chains.
s = [mk(1, "Pickup and Return", "1 St", "30yd", note="swap till end"),
     mk(2, "Pickup and Return", "2 St", "30yd"),
     mk(3, "Delivery", "3 St", "30yd"),
     mk(4, "Pickup and Return", "4 St", "30yd"),
     mk(5, "Pickup and Return", "5 St", "30yd")]
cr.resolve_chain(s)
g1, g2 = s[0]["_chain_group_id"], s[3]["_chain_group_id"]
ok(g1 and g2 and g1 != g2, "D-break: two separate chains")
ok(s[2]["_chain_group_id"] is None, "D-break: the D stop is not in a chain")

# 7) 30yd -> 20yd link -> BLOCKING error, chain breaks, both stops flagged.
s = [mk(1, "Pickup and Return", "1 St", "30yd", note="swap till end"),
     mk(2, "Pickup and Return", "2 St", "20yd")]
res = cr.resolve_chain(s)
ok(len(res["errors"]) >= 2 and {e["stop_id"] for e in res["errors"]} == {1, 2}, "size mismatch: blocking error on BOTH")
ok(s[0]["_chain_gives_to"] != 2, "size mismatch: the bad link is not created")

# 8) Explicit address target skipping an intermediate stop.
s = [mk(1, "Pickup and Return", "1351 vb blvd", "30yd", hint={"kind": "explicit", "target_text": "6969 tidewater"}),
     mk(2, "Pickup and Return", "500 middle rd", "30yd"),
     mk(3, "Pickup and Return", "6969 Tidewater Dr", "30yd")]
cr.resolve_chain(s)
ok(s[0]["_chain_gives_to"] == 3, "explicit: links by address, skipping the intermediate stop")
ok(s[1]["_chain_group_id"] is None, "explicit: the skipped stop stays unchained")

# 9) Self-link + cycle rejected.
s = [mk(1, "Pull", "1 St", "30yd", manual=1)]
res = cr.resolve_chain(s)
ok(any("itself" in e["msg"] for e in res["errors"]) and s[0]["_chain_gives_to"] is None, "self-link rejected")
s = [mk(1, "Pull", "1 St", "30yd", manual=2), mk(2, "Pull", "2 St", "30yd", manual=1)]
res = cr.resolve_chain(s)
ok(len(res["errors"]) >= 1, "unintended cycle rejected")

# ── DB-level: fixture ───────────────────────────────────────────────────────
conn = app.get_db(); cur = conn.cursor(); ts = app.now_ts()
cur.execute("""INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,created_at)
               VALUES (?,?,?,?,?,?)""", ("Co", "cso", "pro", "active", 10, ts)); co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("cs_boss", "x", "boss", "Boss", co, ts)); boss = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("cs_drv", "x", "driver", "Dave Jones", co, ts)); drv = cur.lastrowid
conn.commit(); conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()
def as_boss():
    with cl.session_transaction() as s:
        s.update(user_id=boss, company_id=co, role="boss", roles=["owner", "dispatcher"], _csrf_token="tok")
def as_driver():
    with cl.session_transaction() as s:
        s.update(user_id=drv, company_id=co, role="driver", _csrf_token="tok")
HJ = {"X-CSRF-Token": "tok"}

def dispatch(stops, date):
    as_boss()
    return cl.post("/api/dispatch", json={"driver_id": drv, "route_date": date, "stops": stops}, headers=HJ)

def route_rows(rid):
    c = app.get_db()
    rows = [dict(r) for r in c.execute(
        "SELECT id,stop_order,address,container_size,chain_group_id,chain_seq,chain_gives_to_stop_id,"
        "chain_takes_from_stop_id,chain_terminal FROM stops WHERE route_id=? ORDER BY stop_order, id", (rid,)).fetchall()]
    c.close(); return rows

def last_route():
    c = app.get_db(); rid = c.execute("SELECT id FROM routes WHERE company_id=? ORDER BY id DESC LIMIT 1", (co,)).fetchone()["id"]; c.close(); return rid

# 10) Dispatch the two-line input end to end -> 2-stop chain, tail->head.
r = dispatch([
    {"action": "PR", "address": "1351 Virginia Beach Blvd", "customer": "REAP", "container_size": "30yd", "dump_leg": "Dominion", "notes": "use to swap"},
    {"action": "PR", "address": "5125 Ballahack Rd", "customer": "RES", "container_size": "30yd", "dump_leg": "Dominion", "notes": ""},
], "2026-09-01")
ok(r.status_code == 200, "dispatch two-line input succeeds")
rows = route_rows(last_route())
ok(rows[0]["chain_gives_to_stop_id"] == rows[1]["id"] and rows[1]["chain_gives_to_stop_id"] == rows[0]["id"]
   and rows[1]["chain_terminal"] == "head", "dispatched chain: tail returns to head")

# 11) Positional links follow the FINAL SAVED ORDER (the confirm-sheet reorder is
#     applied before dispatch), not parse order. Dispatch a run, then the same run
#     reversed, and confirm the head is always the physically-first stop.
dispatch([{"action": "PR", "address": "10 A St", "container_size": "30yd", "notes": "swap till end"},
          {"action": "PR", "address": "20 B St", "container_size": "30yd", "notes": ""}], "2026-09-02")
rows = route_rows(last_route())
ok(rows[0]["chain_seq"] == 0 and rows[0]["address"].startswith("10 A"), "saved order: first stop is the head")
dispatch([{"action": "PR", "address": "20 B St", "container_size": "30yd", "notes": ""},
          {"action": "PR", "address": "10 A St", "container_size": "30yd", "notes": "swap till end"}], "2026-09-12")
rows = route_rows(last_route())
ok(rows[0]["chain_seq"] == 0 and rows[0]["address"].startswith("20 B"),
   "reversed saved order: head follows the new order (positional, not parse order)")

# 12) 30->20 dispatch -> BLOCKING (400). Container-size mismatch is the ONLY chain
#     condition that may reject an insert — it would strand the truck.
r = dispatch([{"action": "PR", "address": "1 Big St", "container_size": "30yd", "notes": "swap till end"},
              {"action": "PR", "address": "2 Small St", "container_size": "20yd", "notes": ""}], "2026-09-03")
ok(r.status_code == 400 and "mismatch" in (r.get_json() or {}).get("error", "").lower(),
   "30->20 dispatch blocked with a size-mismatch error")

# 12a) FIX 1 — only a container-size mismatch is blocking; every other chain
#      finding is advisory. The API filters errors through _chain_blocking_errors,
#      so this MUST fail if anyone reverts to `if _chain_res["errors"]`.
_mixed = {"errors": [{"kind": "size", "msg": "Container size mismatch — bad."},
                     {"kind": "loop", "msg": "Swap links form a loop."},
                     {"kind": "self", "msg": "A stop can't swap with itself."},
                     {"kind": "double", "msg": "That stop already receives a can."}],
          "infos": [{"msg": "The head stop has no can until a delivery is scheduled."}],
          "needs_link": [{"target_text": "6969 Tidewater Dr"}]}
_blk = app._chain_blocking_errors(_mixed)
ok(len(_blk) == 1 and _blk[0]["kind"] == "size", "only the size mismatch is blocking; loop/self/double are not")
_ntc = app._chain_notices(_mixed)
ok(all("mismatch" not in m for m in _ntc), "size mismatch never appears as an advisory notice")
ok(any("loop" in m for m in _ntc) and any("itself" in m for m in _ntc)
   and any("already receives" in m for m in _ntc), "non-size errors surface as advisory notices")
ok(any("no can" in m for m in _ntc) and any("Tidewater" in m for m in _ntc),
   "INFO notices and unmatched targets fold into advisory notices")
# an error set with NO size mismatch is fully non-blocking
ok(app._chain_blocking_errors({"errors": [{"kind": "loop", "msg": "loop"}], "infos": [], "needs_link": []}) == [],
   "a loop with no size mismatch does not block the insert")

# 12b) FIX 1 end-to-end — a valid dispatch carries advisory notices in its 200
#      response (an unmatched explicit target is advisory, never a block).
r = dispatch([{"action": "PR", "address": "1 Head St", "container_size": "30yd", "notes": "use to swap 999 Nowhere Rd"},
              {"action": "PR", "address": "2 Tail St", "container_size": "30yd", "notes": ""}], "2026-09-13")
j = r.get_json() or {}
ok(r.status_code == 200 and j.get("success") is True, "dispatch with an unmatched swap target still succeeds (advisory)")
ok(isinstance(j.get("notices"), list) and any("Nowhere" in m for m in j["notices"]),
   "the unmatched target is returned as a non-blocking notice, not a 400")

# 13) Quick Add (manual note) identical to AI parse.
r = dispatch([{"action": "PR", "address": "77 Q St", "container_size": "30yd", "notes": "use to swap"},
              {"action": "PR", "address": "88 R St", "container_size": "30yd", "notes": ""}], "2026-09-04")
rows = route_rows(last_route())
ok(rows[0]["chain_gives_to_stop_id"] == rows[1]["id"] and rows[1]["chain_terminal"] == "head",
   "quick-add 'use to swap' typed as a note links exactly like AI parse")

# 14) Manual "Swaps with" override survives a subsequent Edit Stop save.
r = dispatch([{"action": "Pull", "address": "100 M St", "container_size": "30yd"},
              {"action": "Pull", "address": "200 N St", "container_size": "30yd"}], "2026-09-05")
rid = last_route(); rows = route_rows(rid); a, b = rows[0]["id"], rows[1]["id"]
as_boss()
cl.post("/stop/%d/edit" % a, data={"_csrf_token": "tok", "customer_name": "M", "address": "100 M St",
        "action": "Pull", "container_size": "30yd", "chain_gives_to_stop_id": str(b)})
rows = route_rows(rid)
ok(rows[0]["chain_gives_to_stop_id"] == b, "manual Swaps-with sets the link")
# a later unrelated edit to the OTHER stop must keep the manual link
cl.post("/stop/%d/edit" % b, data={"_csrf_token": "tok", "customer_name": "N2", "address": "200 N St",
        "action": "Pull", "container_size": "30yd"})
rows = route_rows(rid)
ok([x for x in rows if x["id"] == a][0]["chain_gives_to_stop_id"] == b,
   "manual Swaps-with survives a subsequent Edit Stop save")

# ── Optional tickets (unchanged behavior, still required) ────────────────────
conn = app.get_db(); cur = conn.cursor()
cur.execute("""INSERT INTO saved_addresses (company_id,customer_name,address,full_address,kind,norm_key,hidden,issues_tickets,times_used,last_used_at,created_at)
               VALUES (?,?,?,?,?,?,0,?,1,?,?)""",
            (co, "Holland", "1 Fill Rd", "1 Fill Rd", "dump", app._address_book_key("Holland", "1 Fill Rd", "dump"), 1, ts, ts)); site_yes = cur.lastrowid
cur.execute("""INSERT INTO saved_addresses (company_id,customer_name,address,full_address,kind,norm_key,hidden,issues_tickets,times_used,last_used_at,created_at)
               VALUES (?,?,?,?,?,?,0,?,1,?,?)""",
            (co, "BackLot", "2 Dirt Rd", "2 Dirt Rd", "dump", app._address_book_key("BackLot", "2 Dirt Rd", "dump"), 0, ts, ts)); site_no = cur.lastrowid
rid2 = cur.execute("""INSERT INTO routes (company_id,route_date,route_name,created_by,assigned_to,status,started_at,created_at)
                      VALUES (?,?,?,?,?,?,?,?) RETURNING id""", (co, "2026-09-06", "R2", boss, drv, "in_progress", ts, ts)).fetchone()["id"]
def dstop(site):
    return cur.execute("""INSERT INTO stops (route_id,stop_order,customer_name,address,action,container_size,dump_location,dump_site_id,status,driver_status,created_at)
                          VALUES (?,?,?,?,?,?,?,?,?,?,?) RETURNING id""",
                       (rid2, 1, "C", "1 Job St", "Pull", "30yd", "Site", site, "open", "going_to_dump", ts)).fetchone()["id"]
s_yes = dstop(site_yes); s_no = dstop(site_no)
conn.commit(); conn.close()
as_driver()
HF = {"X-Requested-With": "fetch", "X-CSRF-Token": "tok"}
r = cl.post("/stop/%d/dump-ticket" % s_yes, data={"_csrf_token": "tok", "dump_site": "Holland"}, headers=HF)
ok(r.status_code == 400, "issues_tickets=1: completion blocked without ticket or photo")
data = {"_csrf_token": "tok", "dump_site": "BackLot", "ticket_photo": (io.BytesIO(b"\xff\xd8\xffx"), "d.jpg")}
r = cl.post("/stop/%d/dump-ticket" % s_no, data=data, headers=HF, content_type="multipart/form-data")
ok(r.status_code == 200, "issues_tickets=0: completion allowed with a photo, no typed ticket")
c = app.get_db()
tn = c.execute("SELECT ticket_number FROM dump_tickets WHERE stop_id=?", (s_no,)).fetchone()["ticket_number"]
c.close()
ok(tn and tn.startswith("HT-") and "DJ" in tn, "issues_tickets=0: auto HT-…-{initials}-{seq} reference (%s)" % tn)

# ── Legacy stops (NULL chain fields) render on the board unchanged ───────────
conn = app.get_db(); cur = conn.cursor()
lrid = cur.execute("""INSERT INTO routes (company_id,route_date,route_name,created_by,assigned_to,status,started_at,created_at)
                      VALUES (?,?,?,?,?,?,?,?) RETURNING id""", (co, app.today_str(), "Legacy", boss, drv, "in_progress", ts, ts)).fetchone()["id"]
cur.execute("""INSERT INTO stops (route_id,stop_order,customer_name,address,action,container_size,status,driver_status,created_at)
               VALUES (?,?,?,?,?,?,?,?,?)""", (lrid, 1, "Legacy Cust", "77 Old Way", "Pickup and Return", "20yd", "open", "pending", ts))
conn.commit(); conn.close()
as_boss()
board = cl.get("/routes").get_data(as_text=True)
ok("77 Old Way" in board and "SWAP" not in board.split("77 Old Way")[0][-400:],
   "legacy stop renders on the board with no chain badge")

# 15) Pre-insert chain preview (parser confirm sheet) reuses the one resolver.
as_boss()
pv = cl.post("/api/chain-preview", json={"stops": [
    {"action": "PR", "address": "1 P St", "container_size": "30yd", "notes": "swap till end"},
    {"action": "PR", "address": "2 Q St", "container_size": "30yd", "notes": ""},
    {"action": "PR", "address": "3 R St", "container_size": "30yd", "notes": "back to yard"}]}, headers=HJ).get_json()
ok(len(pv["chains"]) == 1 and pv["chains"][0]["trips"] == 3 and pv["chains"][0]["terminal"] == "yard",
   "chain-preview: 3-stop chain, 3 dump trips, yard terminal, before insert")
ok(any("no can" in m for m in pv["infos"]), "chain-preview: INFO surfaced for the head")
pv2 = cl.post("/api/chain-preview", json={"stops": [
    {"action": "PR", "address": "1 Big St", "container_size": "30yd", "notes": "swap till end"},
    {"action": "PR", "address": "2 Small St", "container_size": "20yd", "notes": ""}]}, headers=HJ).get_json()
ok(len(pv2["errors"]) >= 1, "chain-preview: size mismatch surfaced as a blocking error before insert")

print("\nALL CHAINED-SWAP (two-FK) / OPTIONAL-TICKET TESTS PASSED")
