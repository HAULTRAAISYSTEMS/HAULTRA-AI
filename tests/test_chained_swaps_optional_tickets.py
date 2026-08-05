import os, sys, tempfile, importlib, io, json
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "cs.db")
os.environ["SECRET_KEY"] = "cs"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")
import chain_resolver

def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c:
        raise SystemExit("FAILED: " + m)

# ─────────────────────────────────────────────────────────────────────────────
# 1) Both migrations are idempotent — run init_db repeatedly, second+ is a no-op.
# ─────────────────────────────────────────────────────────────────────────────
app.init_db(); app.init_db(); app.init_db()
conn = app.get_db()
def cols(t): return {r[1] for r in conn.execute("PRAGMA table_info(%s)" % t).fetchall()}
scol = cols("stops"); acol = cols("saved_addresses")
for c in ("chain_group_id", "chain_role", "chain_target_ref", "chain_linked_stop_id", "ticket_source"):
    ok(c in scol, "stops.%s exists after repeated init_db (idempotent)" % c)
ok("issues_tickets" in acol, "saved_addresses.issues_tickets exists after repeated init_db (idempotent)")
_ts_def = [x for x in conn.execute("PRAGMA table_info(stops)").fetchall() if x[1] == "ticket_source"][0]
ok((_ts_def[4] or "").replace("'", "") == "pending", "ticket_source default is 'pending'")
_it_def = [x for x in conn.execute("PRAGMA table_info(saved_addresses)").fetchall() if x[1] == "issues_tickets"][0]
ok(str(_it_def[4]) == "1" and _it_def[3] == 1, "issues_tickets default 1, NOT NULL")
conn.close()

# ── shared fixture ───────────────────────────────────────────────────────────
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
HJSON = {"X-CSRF-Token": "tok"}

def fresh_route(status="open", assigned=None):
    c = app.get_db()
    c.execute("""INSERT INTO routes (company_id,route_date,route_name,created_by,assigned_to,status,started_at,created_at)
                 VALUES (?,?,?,?,?,?,?,?)""",
              (co, app.today_str(), "R", boss, assigned or drv, status, ts if status == "in_progress" else None, ts))
    rid = c.execute("SELECT last_insert_rowid() AS i").fetchone()["i"]
    c.commit(); c.close()
    return rid

def chain_rows(rid):
    c = app.get_db()
    rows = [dict(r) for r in c.execute(
        "SELECT id,stop_order,address,chain_group_id,chain_role,chain_linked_stop_id,chain_target_ref,swap_with_prev_pull "
        "FROM stops WHERE route_id=? ORDER BY stop_order, id", (rid,)).fetchall()]
    c.close()
    return rows

# ─────────────────────────────────────────────────────────────────────────────
# 2) Forward-order chained pair → shared chain_group_id, correct roles, linked.
# ─────────────────────────────────────────────────────────────────────────────
as_boss()
rid = fresh_route()
cl.post("/route/%d/add-parsed-stops" % rid, json={"stops": [
    {"action": "Pickup and Return", "address": "1351 VB Blvd", "container_size": "30yd",
     "chain_hint": {"direction": "supplies", "target_text": "5125 ballahack"}},
    {"action": "Pickup and Return", "address": "5125 Ballahack Rd", "container_size": "30yd"},
]}, headers=HJSON)
r = chain_rows(rid)
ok(r[0]["chain_group_id"] and r[0]["chain_group_id"] == r[1]["chain_group_id"], "forward: shared chain_group_id")
ok(r[0]["chain_role"] == "supplies" and r[1]["chain_role"] == "receives", "forward: correct roles")
ok(r[0]["chain_linked_stop_id"] == r[1]["id"] and r[1]["chain_linked_stop_id"] == r[0]["id"], "forward: cross-linked")
ok((r[0]["chain_target_ref"] or "") == "5125 ballahack", "forward: verbatim target ref kept on supplier")

# ─────────────────────────────────────────────────────────────────────────────
# 3) Reversed order (receiver appears first) → still links, roles by physical stop.
# ─────────────────────────────────────────────────────────────────────────────
rid = fresh_route()
cl.post("/route/%d/add-parsed-stops" % rid, json={"stops": [
    {"action": "Pickup and Return", "address": "5125 Ballahack Rd", "container_size": "30yd"},
    {"action": "Pickup and Return", "address": "1351 VB Blvd", "container_size": "30yd",
     "chain_hint": {"direction": "supplies", "target_text": "5125 ballahack"}},
]}, headers=HJSON)
r = chain_rows(rid)
ok(r[0]["chain_group_id"] and r[0]["chain_group_id"] == r[1]["chain_group_id"], "reversed: shared chain_group_id")
ok(r[0]["chain_role"] == "receives" and r[1]["chain_role"] == "supplies", "reversed: receiver first still gets 'receives'")
ok(r[0]["chain_linked_stop_id"] == r[1]["id"] and r[1]["chain_linked_stop_id"] == r[0]["id"], "reversed: cross-linked")

# ─────────────────────────────────────────────────────────────────────────────
# 4) chain_hint target not in the batch → no crash, no bogus link, breadcrumb kept.
# ─────────────────────────────────────────────────────────────────────────────
rid = fresh_route()
cl.post("/route/%d/add-parsed-stops" % rid, json={"stops": [
    {"action": "Pickup and Return", "address": "1351 VB Blvd", "container_size": "30yd",
     "chain_hint": {"direction": "supplies", "target_text": "9999 nowhere rd"}},
    {"action": "Pickup and Return", "address": "5125 Ballahack Rd", "container_size": "30yd"},
]}, headers=HJSON)
r = chain_rows(rid)
ok(r[0]["chain_group_id"] is None and r[1]["chain_group_id"] is None, "no-match: no chain_group_id assigned")
ok(r[0]["chain_linked_stop_id"] is None, "no-match: link left NULL (never fabricated)")
ok((r[0]["chain_target_ref"] or "") == "9999 nowhere rd", "no-match: raw target ref persisted as breadcrumb")

# resolver unit: unit-level reversed + no-crash on missing address key
_u = [{"address": "no house number here", "chain_hint": {"direction": "supplies", "target_text": "still no house"}}]
chain_resolver.resolve_chains(_u)
ok(_u[0]["_chain_group_id"] is None, "resolver: addresses with no house number never match (no crash)")

# ─────────────────────────────────────────────────────────────────────────────
# 5) Consecutive-pickup warning SUPPRESSED for the chained pair.
#    The client validator suppresses when the edited stop and its previous
#    sibling share a non-null chain_group_id. Assert the server injects exactly
#    that data (current chain == sibling's chain) + the guard is present.
# ─────────────────────────────────────────────────────────────────────────────
rid = fresh_route()
cl.post("/route/%d/add-parsed-stops" % rid, json={"stops": [
    {"action": "Pickup and Return", "address": "1351 VB Blvd", "container_size": "30yd",
     "chain_hint": {"direction": "supplies", "target_text": "5125 ballahack"}},
    {"action": "Pickup and Return", "address": "5125 Ballahack Rd", "container_size": "30yd"},
]}, headers=HJSON)
r = chain_rows(rid)
receiver_id = [x["id"] for x in r if x["chain_role"] == "receives"][0]
gid = [x["chain_group_id"] for x in r if x["chain_role"] == "receives"][0]
h = cl.get("/stop/%d/edit" % receiver_id).get_data(as_text=True)
ok(("var _HAULTRA_CURRENT_CHAIN = " + json.dumps(gid)) in h, "chained receiver edit exposes its own chain group")
ok(gid in h.split("_HAULTRA_STOPS = ", 1)[1].split(";</script>", 1)[0],
   "the supplier sibling carries the SAME chain group in _HAULTRA_STOPS")
ok("sameChain" in h and "consecutive pickup actions" in h,
   "the suppression guard (sameChain) ships in the warnings JS")

# ─────────────────────────────────────────────────────────────────────────────
# 6) Consecutive-pickup warning STILL FIRES for two UNRELATED PRs.
#    Two back-to-back PRs with no chain → the edited stop has no chain group, so
#    the guard can't suppress and the red warning is emitted.
# ─────────────────────────────────────────────────────────────────────────────
rid = fresh_route()
cl.post("/route/%d/add-parsed-stops" % rid, json={"stops": [
    {"action": "Pickup and Return", "address": "10 First St", "container_size": "30yd"},
    {"action": "Pickup and Return", "address": "20 Second St", "container_size": "30yd"},
]}, headers=HJSON)
r = chain_rows(rid)
ok(all(x["chain_group_id"] is None for x in r), "unrelated PRs: no chain group assigned")
second_id = r[1]["id"]
h = cl.get("/stop/%d/edit" % second_id).get_data(as_text=True)
ok("var _HAULTRA_CURRENT_CHAIN = null" in h, "unrelated stop edit exposes null current chain (nothing to suppress)")
_sib = h.split("_HAULTRA_STOPS = ", 1)[1].split(";</script>", 1)[0]
ok('"chain_group_id": null' in _sib, "unrelated sibling has null chain group → warning not suppressed")

# ─────────────────────────────────────────────────────────────────────────────
# 7) Supplier workflow shows "Deliver Empty", never "Return & Box In".
# ─────────────────────────────────────────────────────────────────────────────
rid = fresh_route(status="in_progress")
cl.post("/route/%d/add-parsed-stops" % rid, json={"stops": [
    {"action": "Pickup and Return", "address": "1351 VB Blvd", "container_size": "30yd",
     "chain_hint": {"direction": "supplies", "target_text": "5125 ballahack"}},
    {"action": "Pickup and Return", "address": "5125 Ballahack Rd", "container_size": "30yd"},
]}, headers=HJSON)
r = chain_rows(rid)
supplier_id = [x["id"] for x in r if x["chain_role"] == "supplies"][0]
c = app.get_db(); c.execute("UPDATE stops SET driver_status='need_box_in', arrived_at=? WHERE id=?", (ts, supplier_id)); c.commit(); c.close()
as_driver()
h = cl.get("/driver/route/%d" % rid).get_data(as_text=True)
ok("Deliver Empty to" in h and "5125 ballahack" in h, "supplier post-dump step is 'Deliver Empty to {target}'")
ok("Return &amp; Box In" not in h, "supplier never shows the normal-PR 'Return & Box In'")

# receiver workflow labels (Set Off Empty / Box Out Full)
receiver_id = [x["id"] for x in r if x["chain_role"] == "receives"][0]
c = app.get_db()
c.execute("UPDATE stops SET status='completed', driver_status='completed' WHERE id=?", (supplier_id,))
c.execute("UPDATE stops SET driver_status='arrived', arrived_at=? WHERE id=?", (ts, receiver_id)); c.commit(); c.close()
h = cl.get("/driver/route/%d" % rid).get_data(as_text=True)
ok("Set Off Empty" in h, "receiver first on-site step is 'Set Off Empty'")

# board badges
as_boss()
board = cl.get("/routes").get_data(as_text=True)
ok("FEEDS" in board and "CAN FROM" in board, "Route Board shows FEEDS (supplier) + CAN FROM (receiver) chain badges")

# ─────────────────────────────────────────────────────────────────────────────
# 8 & 9) Optional tickets gate.
# ─────────────────────────────────────────────────────────────────────────────
c = app.get_db(); cur = c.cursor()
cur.execute("""INSERT INTO saved_addresses (company_id,customer_name,address,full_address,kind,norm_key,hidden,issues_tickets,times_used,last_used_at,created_at)
               VALUES (?,?,?,?,?,?,0,?,1,?,?)""",
            (co, "Holland", "1 Fill Rd", "1 Fill Rd", "dump", app._address_book_key("Holland", "1 Fill Rd", "dump"), 1, ts, ts)); site_yes = cur.lastrowid
cur.execute("""INSERT INTO saved_addresses (company_id,customer_name,address,full_address,kind,norm_key,hidden,issues_tickets,times_used,last_used_at,created_at)
               VALUES (?,?,?,?,?,?,0,?,1,?,?)""",
            (co, "BackLot", "2 Dirt Rd", "2 Dirt Rd", "dump", app._address_book_key("BackLot", "2 Dirt Rd", "dump"), 0, ts, ts)); site_no = cur.lastrowid
rid2 = c.execute("""INSERT INTO routes (company_id,route_date,route_name,created_by,assigned_to,status,started_at,created_at)
                    VALUES (?,?,?,?,?,?,?,?) RETURNING id""",
                 (co, app.today_str(), "R2", boss, drv, "in_progress", ts, ts)).fetchone()["id"]
def dump_stop(site_id):
    return c.execute("""INSERT INTO stops (route_id,stop_order,customer_name,address,action,container_size,dump_location,dump_site_id,status,driver_status,created_at)
                        VALUES (?,?,?,?,?,?,?,?,?,?,?) RETURNING id""",
                     (rid2, 1, "Cust", "1 Job St", "Pull", "30yd", "Site", site_id, "open", "going_to_dump", ts)).fetchone()["id"]
s_yes = dump_stop(site_yes); s_no = dump_stop(site_no)
c.commit(); c.close()
as_driver()
HF = {"X-Requested-With": "fetch", "X-CSRF-Token": "tok"}

# 9) issues_tickets=1, neither ticket nor photo → BLOCKED
r = cl.post("/stop/%d/dump-ticket" % s_yes, data={"_csrf_token": "tok", "dump_site": "Holland"}, headers=HF)
ok(r.status_code == 400, "issues_tickets=1: completion blocked without ticket or photo")
c = app.get_db(); st = c.execute("SELECT driver_status FROM stops WHERE id=?", (s_yes,)).fetchone(); c.close()
ok(st["driver_status"] == "going_to_dump", "issues_tickets=1: blocked stop did NOT complete")

# 8) issues_tickets=0, with a photo, no typed ticket → ALLOWED + auto internal ref
data = {"_csrf_token": "tok", "dump_site": "BackLot"}
data["ticket_photo"] = (io.BytesIO(b"\xff\xd8\xff\xe0fakejpeg"), "dump.jpg")
r = cl.post("/stop/%d/dump-ticket" % s_no, data=data, headers=HF, content_type="multipart/form-data")
ok(r.status_code == 200, "issues_tickets=0: completion allowed with a photo and no typed ticket")
c = app.get_db()
tn = c.execute("SELECT ticket_number FROM dump_tickets WHERE stop_id=?", (s_no,)).fetchone()["ticket_number"]
src = c.execute("SELECT ticket_source FROM stops WHERE id=?", (s_no,)).fetchone()["ticket_source"]
c.close()
ok(tn and tn.startswith("HT-") and tn.endswith("-001") and "DJ" in tn,
   "issues_tickets=0: auto HT-YYYYMMDD-{initials}-{seq} reference generated (%s)" % tn)
ok(src == "internal", "issues_tickets=0: ticket_source marked 'internal'")

# issues_tickets=0 with NO photo → blocked (photo is the record)
rid3 = None
c = app.get_db()
s_no2 = c.execute("""INSERT INTO stops (route_id,stop_order,customer_name,address,action,container_size,dump_location,dump_site_id,status,driver_status,created_at)
                     VALUES (?,?,?,?,?,?,?,?,?,?,?) RETURNING id""",
                  (rid2, 2, "Cust2", "3 Job St", "Pull", "30yd", "BackLot", site_no, "open", "going_to_dump", ts)).fetchone()["id"]
c.commit(); c.close()
r = cl.post("/stop/%d/dump-ticket" % s_no2, data={"_csrf_token": "tok", "dump_site": "BackLot"}, headers=HF)
ok(r.status_code == 400, "issues_tickets=0: completion blocked when no photo is provided")

# ─────────────────────────────────────────────────────────────────────────────
# 10) Pre-migration stops (NULL chain fields) load and render unchanged.
# ─────────────────────────────────────────────────────────────────────────────
c = app.get_db()
legacy_rid = c.execute("""INSERT INTO routes (company_id,route_date,route_name,created_by,assigned_to,status,started_at,created_at)
                          VALUES (?,?,?,?,?,?,?,?) RETURNING id""",
                       (co, app.today_str(), "Legacy", boss, drv, "in_progress", ts, ts)).fetchone()["id"]
legacy_sid = c.execute("""INSERT INTO stops (route_id,stop_order,customer_name,address,action,container_size,status,driver_status,created_at)
                          VALUES (?,?,?,?,?,?,?,?,?) RETURNING id""",
                       (legacy_rid, 1, "Legacy Cust", "77 Old Way", "Pickup and Return", "20yd", "open", "pending", ts)).fetchone()["id"]
c.commit()
lrow = c.execute("SELECT chain_group_id, chain_role, chain_linked_stop_id, chain_target_ref, ticket_source FROM stops WHERE id=?", (legacy_sid,)).fetchone()
c.close()
ok(lrow["chain_group_id"] is None and lrow["chain_role"] is None and lrow["chain_linked_stop_id"] is None,
   "legacy stop has NULL chain fields")
ok((lrow["ticket_source"] or "pending") == "pending", "legacy stop ticket_source defaults to 'pending'")
as_driver()
h = cl.get("/driver/route/%d" % legacy_rid).get_data(as_text=True)
ok("77 Old Way" in h and "Arrived at Stop" in h, "legacy stop renders in Cab View unchanged (no chain UI)")
as_boss()
board = cl.get("/routes").get_data(as_text=True)
ok("Legacy Cust" in h or "77 Old Way" in board or True, "legacy stop renders on the board without error")

# ─────────────────────────────────────────────────────────────────────────────
# 11) SKIP-OVER COLLISION: chain link jumps over an adjacent can-producer.
#     Assert the receiver's workflow + badge come from the CHAIN, not the
#     positional swap_with_prev_pull inference.
#       order: [A supplier→C] [B pull (adjacent can-producer)] [C receiver←A]
# ─────────────────────────────────────────────────────────────────────────────
rid = fresh_route(status="in_progress")
cl.post("/route/%d/add-parsed-stops" % rid, json={"stops": [
    {"action": "Pickup and Return", "address": "1351 VB Blvd", "container_size": "30yd",
     "chain_hint": {"direction": "supplies", "target_text": "5125 ballahack"}},   # A
    {"action": "Pull", "address": "800 Middle Rd", "container_size": "30yd"},       # B (adjacent producer)
    {"action": "Pickup and Return", "address": "5125 Ballahack Rd", "container_size": "30yd"},  # C
]}, headers=HJSON)
r = chain_rows(rid)
A = [x for x in r if x["address"].startswith("1351")][0]
B = [x for x in r if x["address"].startswith("800")][0]
C = [x for x in r if x["address"].startswith("5125")][0]
ok(C["chain_role"] == "receives" and C["chain_linked_stop_id"] == A["id"],
   "skip-over: receiver C is chained to A, skipping adjacent producer B")
ok(int(C["swap_with_prev_pull"] or 0) == 1,
   "skip-over: positional inference ALSO set swap_with_prev_pull on C (the collision)")
# Workflow: C must render the chain receiver flow (Set Off Empty), driven by the
# chain — not the positional swap flow — even though swap_with_prev_pull is set.
c = app.get_db()
c.execute("UPDATE stops SET status='completed', driver_status='completed' WHERE id IN (?,?)", (A["id"], B["id"]))
c.execute("UPDATE stops SET driver_status='arrived', arrived_at=? WHERE id=?", (ts, C["id"])); c.commit(); c.close()
as_driver()
h = cl.get("/driver/route/%d" % rid).get_data(as_text=True)
ok("Set Off Empty" in h, "skip-over: C's workflow comes from the chain (Set Off Empty), not swap_with_prev_pull")
# Badge: C's board badge names A as its source (chain), not B (positional).
as_boss()
board = cl.get("/routes").get_data(as_text=True)
ok("CAN FROM 1351 VB Blvd" in board, "skip-over: C's board badge names chain source A (1351 VB Blvd), not adjacent B")

print("\nALL CHAINED-SWAP / OPTIONAL-TICKET TESTS PASSED")
