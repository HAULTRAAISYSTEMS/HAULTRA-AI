"""Fixes 2/3/4 for the can-swap chain incident:

  Fix 2  the AI parser emits a STRUCTURED chain_hint (never prose); the swap
         phrase is derived in Python and never rendered raw as a note.
  Fix 3  ONE note-driven resolver runs on every write path; the same dispatch
         entered four different ways yields byte-identical chain state, and a
         new notes-bearing stop insert that skips the resolver fails this test.
  Fix 4  a resolved link renders on BOTH stops from FK state; a half-written
         link surfaces as a data-integrity notice, never a one-sided render;
         no link renders nothing.
"""
import os, sys, tempfile, importlib, re
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "cn.db")
os.environ["SECRET_KEY"] = "cn"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")
import chain_resolver as cr

def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c:
        raise SystemExit("FAILED: " + m)

# ── Fix 2: resolver helpers (structured hint in, derived phrase out) ─────────
ok(cr.hint_to_note({"kind": "run"}) == "swap till end", "hint run -> canonical phrase")
ok(cr.hint_to_note({"kind": "next"}) == "use to swap", "hint next -> canonical phrase")
ok(cr.hint_to_note({"kind": "explicit", "target_text": "5125 Ballahack Rd"}) == "use to swap 5125 Ballahack Rd",
   "hint explicit keeps the target verbatim")
ok(cr.hint_to_note({"kind": "terminal", "terminal": "yard"}) == "back to yard", "hint terminal:yard")
ok(cr.hint_to_note({"kind": "start", "start": "yard"}) == "start from yard", "hint start:yard")
ok(cr.hint_to_note(None) == "" and cr.hint_to_note({"kind": "bogus"}) == "", "unknown/None hint -> empty")

# stripping removes ONLY the trigger phrase; real note text survives
ok(cr.strip_chain_phrases("gate code 1234 use to swap 5125 ballahack") == "gate code 1234",
   "strip removes the explicit phrase + target, keeps the real note")
ok(cr.strip_chain_phrases("swap till end") == "", "strip a bare run phrase -> empty")
ok(cr.strip_chain_phrases("leave the bin by the fence") == "leave the bin by the fence",
   "strip leaves a normal note untouched")
ok(cr.detect_start("grab one from the yard first") == "yard" and cr.detect_start("nope") is None,
   "detect_start recognizes the yard-start phrase")

# the parser prompt no longer tells the model to keep a swap phrase in notes,
# and DOES define the structured chain_hint contract
ok("chain_hint" in app._PARSE_SYSTEM_PROMPT_BASE, "prompt defines chain_hint")
ok("VERBATIM in the\n  stop's `notes`" not in app._PARSE_SYSTEM_PROMPT_BASE
   and "keep that phrase VERBATIM in the" not in app._PARSE_SYSTEM_PROMPT_BASE,
   "prompt no longer parks the swap phrase in notes")
ok('{"kind":"start","start":"yard"}' in app._PARSE_SYSTEM_PROMPT_BASE, "prompt documents the start hint")

# ── Fix 4: both-sides render from FK state ──────────────────────────────────
# a clean 2-stop chain: stop 1 gives to stop 2, stop 2 (tail) returns to head
stops = [
    {"id": 10, "address": "1351 Virginia Beach Blvd", "chain_group_id": "g",
     "chain_seq": 0, "chain_gives_to_stop_id": 20, "chain_takes_from_stop_id": None,
     "chain_terminal": None, "chain_start": None},
    {"id": 20, "address": "5125 Ballahack Rd", "chain_group_id": "g",
     "chain_seq": 1, "chain_gives_to_stop_id": 10, "chain_takes_from_stop_id": 10,
     "chain_terminal": "head", "chain_start": None},
]
flows = cr.render_flows(stops)
ok(flows[10]["gives"] == "→ Empty goes to 5125 Ballahack Rd", "giver renders where the empty GOES")
ok(flows[20]["takes"] == "← Empty arrives from 1351 Virginia Beach Blvd", "receiver renders where the empty ARRIVES from")
ok(flows[10]["integrity"] is None and flows[20]["integrity"] is None, "a reciprocal link has no integrity notice")

# a stop with NO chain link renders nothing
solo = cr.render_flows([{"id": 5, "address": "9 Nowhere", "chain_group_id": None,
                         "chain_gives_to_stop_id": None, "chain_takes_from_stop_id": None,
                         "chain_terminal": None, "chain_start": None}])
ok(all(v is None for v in solo[5].values()), "an unchained stop renders no flow lines at all")

# a HALF-written link (giver points out, receiver doesn't point back) is a
# data-integrity notice, NOT a silent one-sided render
half = cr.render_flows([
    {"id": 1, "address": "A", "chain_group_id": "g", "chain_seq": 0,
     "chain_gives_to_stop_id": 2, "chain_takes_from_stop_id": None, "chain_terminal": None, "chain_start": None},
    {"id": 2, "address": "B", "chain_group_id": "g", "chain_seq": 1,
     "chain_gives_to_stop_id": None, "chain_takes_from_stop_id": None, "chain_terminal": None, "chain_start": None},
])
ok(half[1]["gives"] is None and half[1]["integrity"], "half-link giver -> integrity notice, not a fake arrow")

# terminal + start both derive lines with no neighbor
term = cr.render_flows([{"id": 1, "address": "A", "chain_group_id": "g", "chain_seq": 0,
                         "chain_gives_to_stop_id": None, "chain_takes_from_stop_id": None,
                         "chain_terminal": "yard", "chain_start": "yard"}])
ok("yard" in (term[1]["gives"] or "") and "yard" in (term[1]["start"] or ""),
   "terminal:yard and start:yard both render from FK state")

# ── DB fixture ──────────────────────────────────────────────────────────────
app.init_db()
conn = app.get_db(); cur = conn.cursor(); ts = app.now_ts()
cur.execute("""INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,created_at)
               VALUES (?,?,?,?,?,?)""", ("CN", "cnco", "pro", "active", 10, ts)); co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("cn_boss", "x", "boss", "Boss", co, ts)); boss = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("cn_drv", "x", "driver", "Dan Ray", co, ts)); drv = cur.lastrowid
conn.commit(); conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()
def as_boss():
    with cl.session_transaction() as s:
        s.update(user_id=boss, company_id=co, role="boss", roles=["owner", "dispatcher"], _csrf_token="tok")
HJ = {"X-CSRF-Token": "tok"}
HF = {"X-CSRF-Token": "tok"}

def new_route(date):
    c = app.get_db()
    rid = c.execute("""INSERT INTO routes (company_id,route_date,route_name,created_by,assigned_to,status,started_at,created_at)
                       VALUES (?,?,?,?,?,?,?,?) RETURNING id""",
                    (co, date, "R", boss, drv, "in_progress", app.now_ts(), app.now_ts())).fetchone()["id"]
    c.commit(); c.close(); return rid

def chain_signature(rid):
    """Normalized chain state independent of absolute stop ids: for each stop in
    saved order, (seq, terminal, start, gives->index, takes->index)."""
    c = app.get_db()
    rows = [dict(r) for r in c.execute(
        "SELECT id, chain_seq, chain_terminal, chain_start, chain_gives_to_stop_id, chain_takes_from_stop_id "
        "FROM stops WHERE route_id=? ORDER BY stop_order, id", (rid,)).fetchall()]
    c.close()
    idx = {r["id"]: i for i, r in enumerate(rows)}
    return tuple((r["chain_seq"], r["chain_terminal"], r["chain_start"],
                 idx.get(r["chain_gives_to_stop_id"]), idx.get(r["chain_takes_from_stop_id"])) for r in rows)

# ── Fix 3: the SAME dispatch, four entry paths, byte-identical chain state ───
as_boss()

# Path A — Confirm Stop save (parser confirm sheet -> /api/dispatch)
rA = cl.post("/api/dispatch", json={"driver_id": drv, "route_date": "2026-10-01", "stops": [
    {"action": "PR", "address": "1351 Virginia Beach Blvd", "container_size": "30yd", "notes": "use to swap"},
    {"action": "PR", "address": "5125 Ballahack Rd", "container_size": "30yd", "notes": ""}]}, headers=HJ)
ok(rA.status_code == 200, "path A (dispatch) inserts")
c = app.get_db(); ridA = c.execute("SELECT id FROM routes WHERE company_id=? ORDER BY id DESC LIMIT 1", (co,)).fetchone()["id"]; c.close()
sigA = chain_signature(ridA)

# Path B — AI parse add (/route/<id>/add-parsed-stops), structured chain_hint
ridB = new_route("2026-10-02")
rB = cl.post("/route/%d/add-parsed-stops" % ridB, json={"stops": [
    {"action": "Pickup and Return", "address": "1351 Virginia Beach Blvd", "container_size": "30yd",
     "notes": "", "chain_hint": {"kind": "next"}},
    {"action": "Pickup and Return", "address": "5125 Ballahack Rd", "container_size": "30yd",
     "notes": "", "chain_hint": None}]}, headers=HJ)
ok(rB.status_code == 200, "path B (add-parsed-stops) inserts")
sigB = chain_signature(ridB)

# Path C — Quick Add manual single-stop insert (/route/<id>/add_stop), typed note
ridC = new_route("2026-10-03")
cl.post("/route/%d/add_stop" % ridC, data={"_csrf_token": "tok", "customer_name": "REAP",
        "address": "1351 Virginia Beach Blvd", "action": "Pickup and Return", "container_size": "30yd",
        "notes": "use to swap"}, headers=HF)
cl.post("/route/%d/add_stop" % ridC, data={"_csrf_token": "tok", "customer_name": "RES",
        "address": "5125 Ballahack Rd", "action": "Pickup and Return", "container_size": "30yd",
        "notes": ""}, headers=HF)
sigC = chain_signature(ridC)

# Path D — Edit Stop save (/stop/<id>/edit): two plain stops, then edit adds the note
rD = cl.post("/api/dispatch", json={"driver_id": drv, "route_date": "2026-10-04", "stops": [
    {"action": "PR", "address": "1351 Virginia Beach Blvd", "container_size": "30yd", "notes": ""},
    {"action": "PR", "address": "5125 Ballahack Rd", "container_size": "30yd", "notes": ""}]}, headers=HJ)
c = app.get_db(); ridD = c.execute("SELECT id FROM routes WHERE company_id=? ORDER BY id DESC LIMIT 1", (co,)).fetchone()["id"]
d_first = c.execute("SELECT id FROM stops WHERE route_id=? ORDER BY stop_order LIMIT 1", (ridD,)).fetchone()["id"]; c.close()
cl.post("/stop/%d/edit" % d_first, data={"_csrf_token": "tok", "customer_name": "REAP",
        "address": "1351 Virginia Beach Blvd", "action": "Pickup and Return", "container_size": "30yd",
        "notes": "use to swap"})
sigD = chain_signature(ridD)

ok(sigA and sigA[0][0] == 0 and sigA[1][1] == "head", "path A formed the 2-stop chain (tail returns to head)")
ok(sigA == sigB, "AI-parse path is byte-identical to the confirm path")
ok(sigA == sigC, "Quick-Add path is byte-identical to the confirm path")
ok(sigA == sigD, "Edit-Stop path is byte-identical to the confirm path")

# the raw "use to swap" never survives into the user-facing note render
c = app.get_db()
noteC = c.execute("SELECT notes FROM stops WHERE route_id=? ORDER BY stop_order LIMIT 1", (ridC,)).fetchone()["notes"]
c.close()
ok("use to swap" not in app._display_note(noteC), "the swap phrase is stripped from the rendered note")

# ── Fix 3 guard: every notes-bearing stop insert must call the resolver ──────
# Split app.py into function bodies; any function that INSERTs into stops with a
# `notes` column (i.e. can carry a swap phrase) must also call _apply_route_chains.
# A new write path that forgets the resolver fails HERE.
src = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "app.py")).read()
funcs = re.split(r"\ndef ", src)
ALLOW = {
    # Single-stop inserts that can never form a ≥2-stop can-swap chain:
    "convert_order_to_route",  # one customer order -> one stop
    "_perform_assignment",     # one customer request -> one stop
    "_insert_vendor_stop",     # one breakdown/vendor shop stop
}
missing = []
for f in funcs:
    name = (f[:f.find("(")] or "").strip()
    body = f
    inserts_notes = re.search(r"INSERT INTO stops\b[^;]*\bnotes\b", body, re.S | re.I)
    if inserts_notes and "_apply_route_chains" not in body and name not in ALLOW:
        missing.append(name)
ok(not missing, "every notes-bearing stop insert resolves chains (offenders: %s)" % missing)

print("\nALL CHAIN-NARRATION (Fix 2/3/4) TESTS PASSED")
