"""All Stops Done screen: bin prompt and Fix Last Stop.

Two field bugs reported 2026-10-27 from a real route:

1. The last stop was a Delivery — the can went on the ground at the
   customer — and the end-of-day screen still asked "Bin NNNN — where'd it
   go?". A Delivery ALWAYS empties the truck; being a chain receiver (it
   takes the empty from the previous pull) does not change that. The chain
   replay lumped any chain leg in with swaps and carried the can forward.

2. "Fix Last Stop" pointed at stops[-1] — the last row by order, cancelled
   rows included. When the route's final row is cancelled the tap either
   does nothing visible or, worse, marks the cancelled stop completed. It
   must target the last COMPLETED stop, the same one "Previous Stop" uses.

Run:  python3 tests/test_cab_done_screen_fixes.py
"""
import os
import sys
import tempfile
import importlib

TMP = tempfile.mkdtemp(prefix="haultra-donescreen-")
os.environ["DATABASE_PATH"] = os.path.join(TMP, "done.db")
os.environ["SECRET_KEY"] = "done"
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
            ("Done Co", "doneco", "pro", "active", 10, ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id, created_at)"
            " VALUES (?,?,?,?,?,?)", ("done_drv", "x", "driver", "Done Driver", co, ts))
drv = cur.lastrowid
conn.commit()

app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=drv, company_id=co, role="driver", roles=["driver"],
             _csrf_token="tok")


_DAY = [0]


def mkroute(name):
    # One route per driver per date, so each fixture gets its own day.
    _DAY[0] += 1
    cur.execute("INSERT INTO routes (company_id, route_date, route_name, created_by,"
                " assigned_to, status, created_at)"
                " VALUES (?,?,?,?,?,'in_progress',?)",
                (co, "2026-10-%02d" % _DAY[0], name, drv, drv, ts))
    conn.commit()
    return cur.lastrowid


def mkstop(rid, order, action, status="completed", assigned_can="",
           cancelled=False, takes_from=None, gives_to=None):
    cur.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address, city,
                   state, action, container_size, assigned_can, driver_status, status,
                   completed_at, cancelled_at, created_at)
                   VALUES (?,?,?,?,'Norfolk','VA',?,'20yd',?,?,?,?,?,?)""",
                (rid, order, "cust%d" % order, "%d Test St" % order, action,
                 assigned_can, "completed" if status == "completed" else "pending",
                 status, ts if status == "completed" else None,
                 ts if cancelled else None, ts))
    conn.commit()
    sid = cur.lastrowid
    if takes_from is not None:
        cur.execute("UPDATE stops SET chain_takes_from_stop_id=? WHERE id=?", (takes_from, sid))
    if gives_to is not None:
        cur.execute("UPDATE stops SET chain_gives_to_stop_id=? WHERE id=?", (gives_to, sid))
    conn.commit()
    return sid


# ══════════════════════════════════════════════════════════════════
# BUG 1 — final Delivery must leave the truck empty
# ══════════════════════════════════════════════════════════════════
print("\n-- Bug 1: bin prompt after a final Delivery --")

# Plain route: pull, then deliver the empty to a customer. No chain links.
r1 = mkroute("Plain delivery last")
mkstop(r1, 1, "Pull", assigned_can="3080")
mkstop(r1, 2, "Delivery", assigned_can="3080")
bin1, _ = app._route_final_bin_detail(conn, r1)
ok(bin1 == "", "plain route ending in Delivery leaves truck empty (got %r)" % bin1)

# Chained route, the real 10/27 shape: a pull hands its empty to a delivery
# leg (chain_terminal='delivery'). The can ends up at the customer.
r2 = mkroute("Chained delivery last")
s_pull = mkstop(r2, 1, "Pull", assigned_can="3080")
s_del = mkstop(r2, 2, "Delivery", assigned_can="3080", takes_from=s_pull)
cur.execute("UPDATE stops SET chain_gives_to_stop_id=? WHERE id=?", (s_del, s_pull))
conn.commit()
bin2, _ = app._route_final_bin_detail(conn, r2)
ok(bin2 == "", "chained route ending in Delivery leaves truck empty (got %r)" % bin2)


def mkticket(rid, sid, can):
    """A dumped pull: the ticket bin is what the truck carries away."""
    cur.execute("INSERT INTO dump_tickets (stop_id, route_id, company_id, dump_site,"
                " can_number, created_at) VALUES (?,?,?,?,?,?)",
                (sid, rid, co, "Dominion", can, ts))
    conn.commit()


# Control: a route ending in a Pull really does still have a can aboard.
r3 = mkroute("Pull last")
mkstop(r3, 1, "Delivery", assigned_can="3001")
s_pull3 = mkstop(r3, 2, "Pull", assigned_can="3080")
mkticket(r3, s_pull3, "3080")
bin3, _ = app._route_final_bin_detail(conn, r3)
ok(bin3 == "3080", "route ending in Pull still reports the can (got %r)" % bin3)

# The screen itself must not render the prompt for the delivery route.
html = cl.get("/driver/route/%d" % r2).get_data(as_text=True)
ok("where&#39;d it go?" not in html and "where'd it go?" not in html,
   "All Stops Done screen shows no bin prompt after a final Delivery")

html3 = cl.get("/driver/route/%d" % r3).get_data(as_text=True)
ok("3080" in html3 and ("where&#39;d it go?" in html3 or "where'd it go?" in html3),
   "All Stops Done screen still prompts when a can really is aboard")


# ══════════════════════════════════════════════════════════════════
# BUG 2 — Fix Last Stop must target the last COMPLETED stop
# ══════════════════════════════════════════════════════════════════
print("\n-- Bug 2: Fix Last Stop target --")

# Route whose final row is cancelled. The reopen must target stop 2.
r4 = mkroute("Cancelled tail")
mkstop(r4, 1, "Pull", assigned_can="3001")
real_last = mkstop(r4, 2, "Delivery", assigned_can="3001")
dead_tail = mkstop(r4, 3, "Pull", status="open", cancelled=True)

html4 = cl.get("/driver/route/%d" % r4).get_data(as_text=True)
ok("All Stops Done" in html4, "route with a cancelled tail reaches the done screen")
ok("/stop/%d/toggle" % real_last in html4,
   "Fix Last Stop points at the last completed stop (%d)" % real_last)
ok("/stop/%d/toggle" % dead_tail not in html4,
   "Fix Last Stop does NOT point at the cancelled tail (%d)" % dead_tail)

# And the tap must actually land the driver back on that stop.
cl.post("/stop/%d/toggle" % real_last,
        data={"_csrf_token": "tok", "intent": "reopen"},
        follow_redirects=True)
row = dict(conn.execute("SELECT status FROM stops WHERE id=?", (real_last,)).fetchone())
ok(row["status"] == "open", "reopened stop is open again (got %r)" % row["status"])
dead = dict(conn.execute("SELECT status FROM stops WHERE id=?", (dead_tail,)).fetchone())
ok(dead["status"] != "completed",
   "cancelled tail was never completed by the reopen (got %r)" % dead["status"])

after = cl.get("/driver/route/%d" % r4).get_data(as_text=True)
ok("All Stops Done" not in after, "driver is back on a stop card, not the done screen")

print("\n%d failure(s)" % len(FAILURES))
for f in FAILURES:
    print("  FAILED: " + f)
sys.exit(1 if FAILURES else 0)
