import os, sys, tempfile, importlib, json
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "aa.db")
os.environ["SECRET_KEY"] = "aa"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")

def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c:
        raise SystemExit("FAILED: " + m)

app.init_db()
conn = app.get_db(); cur = conn.cursor(); ts = app.now_ts(); today = app.today_str()
cur.execute("INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,created_at) VALUES (?,?,?,?,?,?)",
            ("AA", "aaco", "pro", "active", 10, ts)); co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,company_id,created_at) VALUES (?,?,?,?,?)",
            ("aa_boss", "x", "boss", co, ts)); boss = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("aa_drv", "x", "driver", "Dave", co, ts)); drv = cur.lastrowid

def mkroute(name):
    cur.execute("INSERT INTO routes (company_id,route_date,route_name,created_by,assigned_to,status,started_at,created_at) VALUES (?,?,?,?,?,'in_progress',?,?)",
                (co, today, name, boss, drv, ts, ts))
    return cur.lastrowid

def mkstop(rid, order, name, addr, action="Pickup and Return", dstatus="pending",
           status="open", plan=None, chain=None, swap=0):
    # chain = dict(group=, takes=, gives=, term=)
    cur.execute("""INSERT INTO stops (route_id,stop_order,customer_name,address,city,state,action,
                   container_size,status,driver_status,empty_can_plan,swap_with_prev_pull,
                   chain_group_id,chain_takes_from_stop_id,chain_gives_to_stop_id,chain_terminal,created_at)
                   VALUES (?,?,?,?,'Virginia Beach','VA',?,'30yd',?,?,?, ?, ?,?,?,?,?)""",
                (rid, order, name, addr, action, status, dstatus, plan, swap,
                 chain["group"] if chain else None,
                 chain.get("takes") if chain else None,
                 chain.get("gives") if chain else None,
                 chain.get("term") if chain else None, ts))
    return cur.lastrowid

def row(sid):
    return app.get_db().execute("SELECT * FROM stops WHERE id=?", (sid,)).fetchone()

def set_stop(sid, **kw):
    c = app.get_db()
    c.execute("UPDATE stops SET %s WHERE id=?" % ", ".join("%s=?" % k for k in kw), (*kw.values(), sid))
    c.commit(); c.close()

# ── Unit: _chain_head_id ───────────────────────────────────────────────────
r1 = mkroute("U1")
u1 = mkstop(r1, 1, "H", "543 Central Dr", chain={"group": "g1"})
u2 = mkstop(r1, 2, "M", "100 Main St", chain={"group": "g1", "takes": u1})
u3 = mkstop(r1, 3, "T", "114 Sawyers Creek", chain={"group": "g1", "takes": u2})
conn.commit()
c = app.get_db()
ok(app._chain_head_id(c, r1, "g1") == u1, "chain head resolves to the member that takes from nobody")
ok(app._chain_head_id(c, r1, "nope") is None, "unknown chain group -> None")
c.close()

# ── Unit: _deliver_handoff_dest_id ─────────────────────────────────────────
set_stop(u2, chain_gives_to_stop_id=u3)
c = app.get_db()
ok(app._deliver_handoff_dest_id(c, row(u2), r1) == u3, "chain middle -> gives_to stop")
ok(app._deliver_handoff_dest_id(c, row(u3), r1) == u1, "blank-terminal tail -> head")
set_stop(u3, chain_terminal="yard")
ok(app._deliver_handoff_dest_id(c, row(u3), r1) is None, "yard terminal -> None")
set_stop(u3, chain_terminal="head", chain_gives_to_stop_id=u1)
ok(app._deliver_handoff_dest_id(c, row(u3), r1) == u1, "explicit head terminal -> head")
set_stop(u3, chain_terminal=None, chain_gives_to_stop_id=None)
c.close()

r2 = mkroute("U2")
p1 = mkstop(r2, 1, "P1", "1 A St", plan="carry_next")
p2 = mkstop(r2, 2, "P2", "2 B St", plan="carry_next")
p3 = mkstop(r2, 3, "P3", "3 C St")
p4 = mkstop(r2, 4, "P4", "4 D St", plan="leave_site")
p5 = mkstop(r2, 5, "P5", "5 E St", action="Pull")
conn.commit()
# cancelled stops keep status='open' + cancelled_at (CHECK constraint)
set_stop(p2, cancelled_at=ts)
c = app.get_db()
ok(app._deliver_handoff_dest_id(c, row(p1), r2) == p3, "PR carry_next skips cancelled stop -> next live stop")
ok(app._deliver_handoff_dest_id(c, row(p4), r2) is None, "PR leave_site -> None")
ok(app._deliver_handoff_dest_id(c, row(p5), r2) is None, "pull stop -> None")
c.close()

# ── HTTP harness ───────────────────────────────────────────────────────────
app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=drv, company_id=co, role="driver", _csrf_token="tok")

def post_action(sid, action="box_in", replay=False):
    hdrs = {"X-Sync-Replay": "1"} if replay else {}
    data = {"_csrf_token": "tok", "action": action}
    if replay:
        data["expected_driver_status"] = "need_box_in"
    return cl.post("/stop/%d/driver-action" % sid, data=data, headers=hdrs)

# ── HTTP 1: PR carry_next tap completes the stop and advances the card ──────
r3 = mkroute("R3")
a1 = mkstop(r3, 1, "Priority Pest", "2289 Military Hwy", dstatus="need_box_in", plan="carry_next")
a2 = mkstop(r3, 2, "HEARTLAND", "999 Heartland Rd")
conn.commit()
r = post_action(a1)
ok(r.status_code == 302, "deliver tap redirects (302)")
ok(("handoff=%d" % a2) in r.location, "redirect carries handoff=<next stop>")
st = row(a1)
ok(st["status"] == "completed" and st["driver_status"] == "completed",
   "PR carry_next tap completes the stop")
h = cl.get(r.location).get_data(as_text=True)
ok(">HEARTLAND</div>" in h, "card now shows the next stop (HEARTLAND)")
ok('<div class="cab-next-handoff">' not in h, "no handoff banner when dest IS the current card")
ok("Priority Pest complete" in h and "HEARTLAND" in h, "flash confirms completion + destination")

# ── HTTP 2: chain tail (blank terminal) tap -> banner back to the head ──────
r4 = mkroute("R4")
b1 = mkstop(r4, 1, "Priority Pest", "543 Central Dr", dstatus="completed", status="completed",
            chain={"group": "g2"})
b2 = mkstop(r4, 2, "Camden Site", "114 Sawyers Creek", dstatus="need_box_in",
            chain={"group": "g2", "takes": b1})  # terminal NULL -> defaults to head
conn.commit()
r = post_action(b2)
ok(r.status_code == 302 and ("handoff=%d" % b1) in r.location,
   "tail tap redirects with handoff=<head>")
ok(row(b2)["status"] == "completed", "tail tap completes the tail stop")
h = cl.get(r.location).get_data(as_text=True)
ok("All Stops Done" in h, "route shows all-done when the tail was last")
ok("Empty can goes to" in h and "Priority Pest" in h,
   "one-time banner names the head stop")
ok("destination=543+Central+Dr" in h,
   "banner Navigate link carries the head address")
ok("google.com/maps/dir/?api=1&destination=" in h, "banner has a Navigate link")

# ── HTTP 3: chain middle tap advances to the next chain stop, no banner ─────
r5 = mkroute("R5")
m1 = mkstop(r5, 1, "S1", "1 One St", dstatus="completed", status="completed",
            chain={"group": "g3", "gives": None})
m2 = mkstop(r5, 2, "S2", "2 Two St", dstatus="need_box_in",
            chain={"group": "g3", "takes": m1})
m3 = mkstop(r5, 3, "S3", "3 Three St", chain={"group": "g3", "takes": m2})
conn.commit()
set_stop(m1, chain_gives_to_stop_id=m2)
set_stop(m2, chain_gives_to_stop_id=m3)
r = post_action(m2)
ok(r.status_code == 302 and ("handoff=%d" % m3) in r.location,
   "middle tap redirects with handoff=<next chain stop>")
ok(row(m2)["status"] == "completed", "middle tap completes the stop")
h = cl.get(r.location).get_data(as_text=True)
ok(">S3</div>" in h, "card advances to the next chain stop")
ok("Empty can goes to" not in h, "no banner when the destination is the current card")

# ── HTTP 4: swap-PR guard — box_in ("Confirm Box In") does NOT complete ─────
r6 = mkroute("R6")
w1 = mkstop(r6, 1, "Swap Stop", "7 Swap Ln", dstatus="need_box_in", swap=1)
conn.commit()
r = post_action(w1)
ok(r.status_code == 302 and "handoff" not in r.location, "swap-PR tap has no handoff param")
st = row(w1)
ok(st["status"] == "open" and st["driver_status"] == "box_in",
   "swap-PR Confirm Box In leaves the stop open (dump run still ahead)")
ok(">Swap Stop</div>" in cl.get("/driver/route/%d" % r6).get_data(as_text=True),
   "card stays on the swap stop")

# ── HTTP 5: photo-proof required with no photo — no auto-complete ────────────
cur.execute("UPDATE companies SET photo_proof_mode='required' WHERE id=?", (co,))
conn.commit()
r7 = mkroute("R7")
v1 = mkstop(r7, 1, "Photo Stop", "8 Photo Pl", dstatus="need_box_in", plan="carry_next")
v2 = mkstop(r7, 2, "Next Stop", "9 Next Pl")
conn.commit()
set_stop(v1, arrived_at=ts)  # phase-2 card, like the real driver flow
r = post_action(v1)
st = row(v1)
ok(st["status"] == "open" and st["driver_status"] == "box_in",
   "photo-required + no photo: stop stays open")
ok('<div class="cab-next-handoff">' in cl.get("/driver/route/%d" % r7).get_data(as_text=True),
   "fallback handoff strip still renders for the held-open stop")

# ── HTTP 6: photo-proof required WITH a photo — auto-completes ──────────────
cur.execute("INSERT INTO route_photos (stop_id,file_path,uploaded_at,uploaded_by) VALUES (?,?,?,?)",
            (v1, "static/uploads/p.jpg", ts, drv))
conn.commit()
set_stop(v1, status="open", driver_status="need_box_in")
r = post_action(v1)
ok(row(v1)["status"] == "completed", "photo-required + photo present: tap completes the stop")
cur.execute("UPDATE companies SET photo_proof_mode='encouraged' WHERE id=?", (co,))
conn.commit()

# ── HTTP 7: offline sync replay converges to completed ──────────────────────
r8 = mkroute("R8")
y1 = mkstop(r8, 1, "Replay Stop", "10 Replay Rd", dstatus="need_box_in", plan="carry_next")
y2 = mkstop(r8, 2, "After Stop", "11 After Rd")
conn.commit()
r = post_action(y1, replay=True)
ok(r.status_code == 200, "replay returns 200")
body = json.loads(r.get_data(as_text=True))
ok(body.get("new_status") == "completed" and body.get("auto_completed") is True,
   "replay JSON reports completed + auto_completed")
ok(row(y1)["status"] == "completed", "replay converges server state to completed")

# ── HTTP 8: leave-on-site tap completes with no handoff ─────────────────────
r9 = mkroute("R9")
z1 = mkstop(r9, 1, "Leave Stop", "12 Leave Ln", dstatus="need_box_in", plan="leave_site")
z2 = mkstop(r9, 2, "Later Stop", "13 Later Ln")
conn.commit()
r = post_action(z1)
ok(r.status_code == 302 and "handoff" not in r.location,
   "leave-on-site tap completes with no handoff param")
ok(row(z1)["status"] == "completed", "leave-on-site tap completes the stop")
h = cl.get(r.location).get_data(as_text=True)
ok("Leave Stop complete." in h, "flash confirms completion without a destination")

print("ALL PASS")
