"""Corrections A & B to the can-swap chain model.

  A  size-mismatch behavior depends on chain_source: an INFERRED (positional/run)
     mismatch breaks SILENTLY (no error) — the app guessed; only a BOSS-SPECIFIED
     (explicit/manual) mismatch is a BLOCKING error.
  B  new 'delivery' terminal: the final empty is dropped at a size-matching D stop.
     Auto-inferred after a yard-started run, or from a phrase; conservation INFO on
     a cold-started delivery; the D card shows the incoming reference; a manual
     [change]->delivery picker lists only size-matching D stops.
"""
import os, sys, tempfile, importlib
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "cc.db")
os.environ["SECRET_KEY"] = "cc"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")
import chain_resolver as cr

def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c:
        raise SystemExit("FAILED: " + m)

def mk(i, action, addr, size, note="", hint=None, manual=None, mdlv=None):
    return {"id": i, "action": action, "address": addr, "container_size": size,
            "note": note, "chain_hint": hint, "manual_gives_to": manual, "manual_delivery": mdlv}

# ── Correction A ────────────────────────────────────────────────────────────
# The live screenshot case: 1351(30) + 5125(30) chain; 3533(20) is an independent
# PR that follows in sequence — run detection must NOT drag it in or flag it.
s = [mk(1, "Pull", "1351 Virginia Beach Blvd", "30yd", note="use to swap"),
     mk(2, "Pull", "5125 Ballahack Rd", "30yd"),
     mk(3, "Pull", "3533 Sleepy Hole Rd", "20yd")]
res = cr.resolve_chain(s)
ok(res["errors"] == [], "screenshot case: ZERO errors (inferred mismatch is silent)")
ok(s[0]["_chain_group_id"] and s[0]["_chain_group_id"] == s[1]["_chain_group_id"], "screenshot case: 1351+5125 chain together")
ok(s[2]["_chain_group_id"] is None and s[2]["_chain_gives_to"] is None, "screenshot case: 3533 (20yd) stands alone, untouched")

# EXPLICIT link into a size mismatch -> BLOCKING error naming both stops
s = [mk(1, "Pull", "1 A St", "30yd", note="use to swap 2 B St"),
     mk(2, "Pull", "2 B St", "20yd")]
res = cr.resolve_chain(s)
ok([e["kind"] for e in res["errors"]].count("size") == 2, "explicit 30->20: BLOCKING size error on both stops")
ok(s[0]["_chain_gives_to"] != 2, "explicit 30->20: the bad link is not created")

# MANUAL link into a size mismatch -> BLOCKING error too
s = [mk(1, "Pull", "1 A St", "30yd", manual=2), mk(2, "Pull", "2 B St", "20yd")]
res = cr.resolve_chain(s)
ok(any(e["kind"] == "size" for e in res["errors"]), "manual 30->20: BLOCKING size error")

# INFERRED run into a size mismatch -> silent, no user-visible message
s = [mk(1, "Pull", "1 A St", "30yd", note="swap till end"),
     mk(2, "Pull", "2 B St", "30yd"),
     mk(3, "Pull", "3 C St", "20yd")]
res = cr.resolve_chain(s)
ok(res["errors"] == [], "inferred run into mismatch: silent break, no message")
ok(s[0]["_chain_group_id"] == s[1]["_chain_group_id"] and s[2]["_chain_group_id"] is None,
   "inferred run into mismatch: first two chain, odd-size third alone")

# ── Correction B ────────────────────────────────────────────────────────────
# Yard start + 3 PR + size-matching D -> terminal='delivery', delivery FK set
s = [mk(1, "Pull", "1 A St", "30yd", note="start from yard swap till end"),
     mk(2, "Pull", "2 B St", "30yd"),
     mk(3, "Pull", "3 C St", "30yd"),
     mk(4, "Delivery", "4512 Elm St", "30yd")]
res = cr.resolve_chain(s)
tail = s[2]
ok(tail["_chain_terminal"] == "delivery" and tail["_chain_delivery"] == 4, "yard+run+matching D: terminal delivery, FK to the D stop")
ok(tail["_chain_gives_to"] is None and s[0]["_chain_start"] == "yard", "yard+run+matching D: tail gives none, head starts from yard")
ok(not res["errors"] and not res["infos"], "yard+run+matching D: balanced — no error, no INFO")
flows = cr.render_flows([dict(id=x["id"], address=x["address"],
                              chain_group_id=x["_chain_group_id"], chain_seq=x["_chain_seq"],
                              chain_gives_to_stop_id=x["_chain_gives_to"], chain_takes_from_stop_id=x["_chain_takes_from"],
                              chain_terminal=x["_chain_terminal"], chain_start=x["_chain_start"],
                              chain_delivery_stop_id=x["_chain_delivery"]) for x in s])
ok("DELIVERED to 4512 Elm St" in (flows[3]["gives"] or ""), "delivery: tail renders 'DELIVERED to {addr}'")
ok("arrives from swap chain" in (flows[4]["takes"] or ""), "delivery: the D card shows the incoming reference")

# Yard start + 3 PR + NON-matching D (20yd) -> run ends silently, terminal 'yard'
s = [mk(1, "Pull", "1 A St", "30yd", note="start from yard swap till end"),
     mk(2, "Pull", "2 B St", "30yd"),
     mk(3, "Pull", "3 C St", "30yd"),
     mk(4, "Delivery", "4 D St", "20yd")]
res = cr.resolve_chain(s)
ok(s[2]["_chain_terminal"] == "yard" and s[2]["_chain_delivery"] is None, "yard+run+NON-matching D: falls back to yard terminal")
ok(res["errors"] == [], "yard+run+NON-matching D: no error")

# Cold start + delivery terminal -> INFO on head, insert allowed (never blocks)
s = [mk(1, "Pull", "1 A St", "30yd", note="swap till end until the delivery"),
     mk(2, "Pull", "2 B St", "30yd"),
     mk(3, "Delivery", "3 C St", "30yd")]
res = cr.resolve_chain(s)
ok(s[1]["_chain_terminal"] == "delivery" and s[1]["_chain_delivery"] == 3, "cold+delivery: terminal delivery bound to the D")
ok(any("no can" in i["msg"] for i in res["infos"]) and res["errors"] == [], "cold+delivery: INFO on head, no block")

# Manual [change]->delivery: only size-matching D stops are valid candidates.
# (The picker is populated from these.) A 30yd chain + a 30yd D + a 20yd D:
s = [mk(1, "Pull", "1 A St", "30yd", note="swap till end"),
     mk(2, "Pull", "2 B St", "30yd"),
     mk(3, "Delivery", "3 Good St", "30yd"),
     mk(4, "Delivery", "4 Bad St", "20yd")]
cr.resolve_chain(s)
cands = [x["id"] for x in s if cr._is_delivery(x["action"]) and cr.normalize_size(x["container_size"]) == "30"]
ok(cands == [3], "delivery picker candidates: only the size-matching D stop")
# picking the size-matching D via manual_delivery binds it
s2 = [mk(1, "Pull", "1 A St", "30yd", note="swap till end", mdlv=3), mk(2, "Pull", "2 B St", "30yd"),
      mk(3, "Delivery", "3 Good St", "30yd")]
cr.resolve_chain(s2)
ok(s2[1]["_chain_terminal"] == "delivery" and s2[1]["_chain_delivery"] == 3 and s2[1]["_chain_source"] == "manual",
   "manual delivery pick binds the D and stays 'manual' (sticky)")

# ── End-to-end: the screenshot dispatch inserts clean (no 400), preview clean ─
app.init_db()
conn = app.get_db(); cur = conn.cursor(); ts = app.now_ts()
cur.execute("""INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,created_at)
               VALUES (?,?,?,?,?,?)""", ("CC", "ccco", "pro", "active", 10, ts)); co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("cc_boss", "x", "boss", "Boss", co, ts)); boss = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("cc_drv", "x", "driver", "Dan Ray", co, ts)); drv = cur.lastrowid
conn.commit(); conn.close()
app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=boss, company_id=co, role="boss", roles=["owner", "dispatcher"], _csrf_token="tok")
HJ = {"X-CSRF-Token": "tok"}

r = cl.post("/api/dispatch", json={"driver_id": drv, "route_date": "2026-11-01", "stops": [
    {"action": "PR", "address": "1351 Virginia Beach Blvd", "container_size": "30yd", "notes": "use to swap"},
    {"action": "PR", "address": "5125 Ballahack Rd", "container_size": "30yd", "notes": ""},
    {"action": "PR", "address": "3533 Sleepy Hole Rd", "container_size": "20yd", "notes": ""}]}, headers=HJ)
ok(r.status_code == 200, "screenshot dispatch: all 3 stops go in clean, ZERO red errors")
c = app.get_db()
rid = c.execute("SELECT id FROM routes WHERE company_id=? ORDER BY id DESC LIMIT 1", (co,)).fetchone()["id"]
rows = [dict(x) for x in c.execute("SELECT address, chain_group_id FROM stops WHERE route_id=? ORDER BY stop_order", (rid,)).fetchall()]
c.close()
_by = {r["address"][:4]: r["chain_group_id"] for r in rows}
ok(_by["1351"] and _by["1351"] == _by["5125"] and _by["3533"] is None,
   "screenshot dispatch: 1351+5125 chained, 3533 independent")

# preview: delivery candidates list only size-matching D stops
pv = cl.post("/api/chain-preview", json={"stops": [
    {"action": "PR", "address": "1 A St", "container_size": "30yd", "notes": "swap till end"},
    {"action": "PR", "address": "2 B St", "container_size": "30yd", "notes": ""},
    {"action": "D", "address": "3 Good St", "container_size": "30yd", "notes": ""},
    {"action": "D", "address": "4 Bad St", "container_size": "20yd", "notes": ""}]}, headers=HJ).get_json()
ok(pv["chains"] and [c["index"] for c in pv["chains"][0]["delivery_candidates"]] == [2],
   "chain-preview: delivery_candidates lists only the size-matching D stop")

# manual delivery round-trips through dispatch and sticks
r = cl.post("/api/dispatch", json={"driver_id": drv, "route_date": "2026-11-02", "stops": [
    {"action": "PR", "address": "1 A St", "container_size": "30yd", "notes": "swap till end", "manual_delivery": 2},
    {"action": "PR", "address": "2 B St", "container_size": "30yd", "notes": ""},
    {"action": "D", "address": "3 Drop St", "container_size": "30yd", "notes": ""}]}, headers=HJ)
ok(r.status_code == 200, "manual-delivery dispatch: inserts clean")
c = app.get_db()
rid2 = c.execute("SELECT id FROM routes WHERE company_id=? ORDER BY id DESC LIMIT 1", (co,)).fetchone()["id"]
trows = [dict(x) for x in c.execute("SELECT address, chain_terminal, chain_delivery_stop_id, id FROM stops WHERE route_id=? ORDER BY stop_order", (rid2,)).fetchall()]
c.close()
_tail = [x for x in trows if x["address"].startswith("2 B")][0]
_dstop = [x for x in trows if x["address"].startswith("3 Drop")][0]
ok(_tail["chain_terminal"] == "delivery" and _tail["chain_delivery_stop_id"] == _dstop["id"],
   "manual-delivery dispatch: the pick persisted as a delivery terminal to the chosen D")

print("\nALL CHAIN-CORRECTION (A/B) TESTS PASSED")
