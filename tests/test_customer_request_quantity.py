"""Customer text-link portal: ask for SEVERAL containers in one request.

The texted /c/<token> link let a customer pick a size but always meant one
container, and an open drop request blocked asking for more. Now:
  * a Drop / New-bin request carries quantity (1..10)
  * approving it creates one delivery stop per container
  * the request is done only when every stop is completed
  * another size at the same site is its own request (dupe guard per size)
  * PR / P / S stay one-bin, and old clients without quantity still work

Run:  python tests/test_customer_request_quantity.py
"""
import json
import os
import sys
import tempfile

TMPDIR = tempfile.mkdtemp(prefix="haultra-qty-")
os.environ["DATABASE_PATH"] = os.path.join(TMPDIR, "qty.db")
os.environ["SECRET_KEY"] = "testsecret123"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMPDIR, "uploads")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import app  # noqa: E402

FAILURES = []


def ok(cond, label):
    print(("PASS" if cond else "FAIL") + " - " + label, flush=True)
    if not cond:
        FAILURES.append(label)


app.init_db()
conn = app.get_db(); cur = conn.cursor(); ts = app.now_ts(); today = app.today_str()
cur.execute("INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,created_at)"
            " VALUES (?,?,?,?,?,?)", ("QtyCo", "qtyco", "pro", "active", 10, ts)); co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,company_id,created_at)"
            " VALUES (?,?,?,?,?)", ("q_boss", "x", "boss", co, ts)); boss = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at)"
            " VALUES (?,?,?,?,?,?)", ("q_drv", "x", "driver", "Dave", co, ts)); drv = cur.lastrowid
TOKEN = "qty-portal-token-abc123"
cur.execute("""INSERT INTO customers (company_id,business_name,contact_name,phone,portal_token,is_active,created_at)
               VALUES (?,?,?,?,?,1,?)""", (co, "Big Build LLC", "Sam", "555", TOKEN, ts)); cust = cur.lastrowid
cur.execute("INSERT INTO sites (customer_id,address,created_at) VALUES (?,?,?)",
            (cust, "100 Job Site Rd", ts)); site = cur.lastrowid
cur.execute("INSERT INTO bins (customer_id,site_id,size,dropped_at) VALUES (?,?,?,?)",
            (cust, site, "20yd", today)); bin1 = cur.lastrowid
conn.commit(); conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()


def post_req(body):
    r = cl.post(f"/api/c/{TOKEN}/requests", data=json.dumps(body), content_type="application/json")
    return r.status_code, json.loads(r.data)


def row(sql, *a):
    c = app.get_db()
    try:
        return c.execute(sql, a).fetchall()
    finally:
        c.close()


# ── schema + portal page ───────────────────────────────────────────────────
cols = {r[1] for r in row("PRAGMA table_info(requests)")}
ok("quantity" in cols, "requests has a quantity column")
page = cl.get(f"/c/{TOKEN}").data.decode()
ok("What do you need at" in page and '"max_qty": 10' in page and "submitOrder" in page,
   "portal page has the job-site order builder")
ok("NEED MORE BINS" in page, "drop button invites asking for more than one")

# ── customer asks for 3 × 30yd ─────────────────────────────────────────────
code, j = post_req({"type": "D", "site_id": site, "size_requested": "30yd",
                    "quantity": 3, "preferred_date": "asap"})
ok(code == 201 and j["quantity"] == 3, "drop request for 3 containers accepted")
req3 = j["id"]

# validation
for bad_q in (0, 11, -1, "3", 2.5, True):
    c2, _ = post_req({"type": "D", "site_id": site, "size_requested": "10yd",
                      "quantity": bad_q, "preferred_date": "asap"})
    ok(c2 == 400, f"quantity {bad_q!r} rejected")

# same size again → duplicate; different size → allowed
c2, _ = post_req({"type": "D", "site_id": site, "size_requested": "30yd", "quantity": 1,
                  "preferred_date": "asap"})
ok(c2 == 409, "second open 30yd request at the same site is a duplicate")
c2, j2 = post_req({"type": "D", "site_id": site, "size_requested": "20yd", "preferred_date": "asap"})
ok(c2 == 201 and j2["quantity"] == 1, "different size is its own request; quantity defaults to 1")
req20 = j2["id"]

# PR ignores quantity
c2, j3 = post_req({"type": "PR", "site_id": site, "bin_id": bin1, "quantity": 5, "preferred_date": "asap"})
ok(c2 == 201 and j3["quantity"] == 1, "empty-and-return stays one bin")

dash = json.loads(cl.get(f"/api/c/{TOKEN}/dashboard").data)
ok(any(r["id"] == req3 and r["quantity"] == 3 for r in dash["requests"]), "portal dashboard returns quantity")

# ── boss approves → 3 delivery stops ───────────────────────────────────────
with cl.session_transaction() as s:
    s.update(user_id=boss, company_id=co, role="boss", roles=["owner", "dispatcher", "customer_manager"],
             username="q_boss", _csrf_token="tok")
rp = cl.get("/requests").data.decode()
ok("3 × 30yd" in rp, "boss Requests page shows 3 × 30yd")

r = cl.patch(f"/api/requests/{req3}/approve", data=json.dumps({"driver_id": drv, "_csrf_token": "tok"}),
             content_type="application/json", headers={"X-CSRF-Token": "tok"})
pj = json.loads(r.data)
ok(r.status_code == 200 and len(pj.get("stop_ids", [])) == 3, "approve creates 3 stops")
stops = row("SELECT id, action, container_size, address, request_id, stop_order FROM stops WHERE request_id=? ORDER BY stop_order", req3)
ok(len(stops) == 3 and all(s["container_size"] == "30yd" and s["address"] == "100 Job Site Rd" for s in stops),
   "each stop is a 30yd delivery at the job site")
ok(len({s["stop_order"] for s in stops}) == 3, "stops get distinct route order")
ok(row("SELECT status FROM requests WHERE id=?", req3)[0]["status"] == "scheduled", "request scheduled")

# ── status follows ALL stops ───────────────────────────────────────────────
c = app.get_db()
c.execute("UPDATE stops SET status='completed' WHERE id=?", (stops[0]["id"],))
app.cascade_request_from_stop(c, stops[0]["id"]); c.commit()
ok(c.execute("SELECT status FROM requests WHERE id=?", (req3,)).fetchone()[0] == "in_progress",
   "one of three delivered -> in progress, not done")
c.execute("UPDATE stops SET status='completed' WHERE id IN (?,?)", (stops[1]["id"], stops[2]["id"]))
app.cascade_request_from_stop(c, stops[2]["id"]); c.commit()
ok(c.execute("SELECT status FROM requests WHERE id=?", (req3,)).fetchone()[0] == "done",
   "all three delivered -> done")
c.close()

# ── single-container request still makes exactly one stop ──────────────────
r = cl.patch(f"/api/requests/{req20}/approve", data=json.dumps({"driver_id": drv}),
             content_type="application/json", headers={"X-CSRF-Token": "tok"})
ok(r.status_code == 200 and len(row("SELECT id FROM stops WHERE request_id=?", req20)) == 1,
   "quantity 1 -> one stop (unchanged behavior)")

# ── re-assign after partial loss never over-delivers ───────────────────────
code, j = post_req({"type": "D", "site_id": site, "size_requested": "40yd", "quantity": 2,
                    "preferred_date": "asap"})
req40 = j["id"]
cl.patch(f"/api/requests/{req40}/approve", data=json.dumps({"driver_id": drv}),
         content_type="application/json", headers={"X-CSRF-Token": "tok"})
s40 = row("SELECT id FROM stops WHERE request_id=? ORDER BY id", req40)
c = app.get_db()
c.execute("DELETE FROM stops WHERE id=?", (s40[1]["id"],))
c.execute("UPDATE requests SET status='accepted', stop_id=NULL WHERE id=?", (req40,)); c.commit(); c.close()
cl.patch(f"/api/requests/{req40}/assign", data=json.dumps({"driver_id": drv}),
         content_type="application/json", headers={"X-CSRF-Token": "tok"})
ok(len(row("SELECT id FROM stops WHERE request_id=?", req40)) == 2,
   "re-assigning after one stop was removed tops up to 2, not 3")

print()
if FAILURES:
    print(f"{len(FAILURES)} FAILURE(S):")
    for f in FAILURES:
        print("  -", f)
    sys.exit(1)
print("ALL CUSTOMER REQUEST QUANTITY TESTS PASSED")
