"""Alert feed regression suite.

The problem this exists for: a driver could reach the boss eight different ways
and each one landed somewhere else, while the page actually called "Alerts"
showed exactly one event type (customer-portal deletions) and nothing a driver
had ever done. These tests assert that everything a driver sends lands in one
inbox, exactly once.
"""
import os, sys, tempfile, importlib, json

TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "alerts.db")
os.environ["SECRET_KEY"] = "alerts"
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
cur.execute("""INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,
               created_at,driver_day_start_rule,driver_day_end_rule)
               VALUES (?,?,?,?,?,?,?,?)""",
            ("Feed Co", "feedco", "pro", "active", 5, ts, "manual", "manual")); co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at)"
            " VALUES (?,?,?,?,?,?)", ("f_boss", "x", "boss", "Tim Brown", co, ts)); boss = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at)"
            " VALUES (?,?,?,?,?,?)", ("f_drv", "x", "driver", "Dave Miller", co, ts)); drv = cur.lastrowid
cur.execute("""INSERT INTO routes (company_id,route_date,route_name,created_by,assigned_to,status,started_at,created_at)
               VALUES (?,?,?,?,?,'in_progress',?,?)""", (co, today, "Route A", boss, drv, ts, ts))
rid = cur.lastrowid
cur.execute("""INSERT INTO stops (route_id,stop_order,customer_name,address,city,state,action,
               container_size,status,driver_status,created_at)
               VALUES (?,1,'Acme Roofing','1 Main','Norfolk','VA','Pull','30yd','open','pending',?)""", (rid, ts))
sid = cur.lastrowid
conn.commit(); conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()

def as_driver():
    with cl.session_transaction() as s:
        s.update(user_id=drv, company_id=co, role="driver", roles=["driver"],
                 username="f_drv", _csrf_token="t")

def as_boss():
    with cl.session_transaction() as s:
        s.update(user_id=boss, company_id=co, role="boss", roles=["owner", "dispatcher"],
                 username="f_boss", _csrf_token="t")

def alerts():
    c = app.get_db()
    rows = c.execute("SELECT * FROM alerts WHERE company_id=? ORDER BY id", (co,)).fetchall()
    c.close()
    return rows

def kinds():
    return [r["kind"] for r in alerts()]


# ── schema ────────────────────────────────────────────────────────────────
c = app.get_db()
cols = {r[1] for r in c.execute("PRAGMA table_info(alerts)").fetchall()}
ok({"kind", "severity", "title", "body", "link", "actor_user_id",
    "entity_type", "entity_id", "dedupe_key", "read_at", "resolved_at", "pushed_at"} <= cols,
   "alerts table has the full pointer + state shape")
ok(bool(c.execute("PRAGMA table_info(push_tokens)").fetchall()), "push_tokens table exists")
c.close()

# ── notify() is idempotent and never raises ───────────────────────────────
c = app.get_db()
app.notify(c, co, "DRIVER_LATE", "dupe test", dedupe_key="dk-1")
app.notify(c, co, "DRIVER_LATE", "dupe test", dedupe_key="dk-1")
c.commit()
n = c.execute("SELECT COUNT(*) n FROM alerts WHERE company_id=? AND dedupe_key='dk-1'", (co,)).fetchone()["n"]
ok(n == 1, "same dedupe_key twice writes one row (offline replay safe)")
app.notify(c, co, "NOT_A_REAL_KIND", "unknown kind")
c.commit()
ok(True, "notify() with an unknown kind does not raise")
c.execute("DELETE FROM alerts WHERE company_id=?", (co,)); c.commit(); c.close()

# ── running late ──────────────────────────────────────────────────────────
as_driver()
r = cl.post("/late/checkin", data={"_csrf_token": "t", "eta": "30 min", "reason": "traffic on 264"})
ok(r.status_code in (200, 302), "late check-in accepted")
a = alerts()
ok(len(a) == 1 and a[0]["kind"] == "DRIVER_LATE", "running late raises one alert")
ok("Dave Miller" in a[0]["title"], "alert names the driver, not their username")
ok("30 min" in a[0]["title"], "the ETA is on the alert")
ok(a[0]["body"] == "traffic on 264", "the reason the driver typed is carried through")
ok(a[0]["severity"] == "warning", "running late is a warning, not noise")

# the ETA field collision regression: a typed time must beat a chip
c = app.get_db(); c.execute("DELETE FROM late_checkins WHERE company_id=?", (co,)); c.commit(); c.close()
r = cl.post("/late/checkin", data={"_csrf_token": "t", "eta": ["30 min", "be in by 7:30"],
                                   "reason": "shop first"})
c = app.get_db()
row = c.execute("SELECT eta FROM late_checkins WHERE company_id=? ORDER BY id DESC LIMIT 1", (co,)).fetchone()
c.close()
ok(row["eta"] == "be in by 7:30", "a typed ETA wins over a chip (got %r)" % row["eta"])
ok(len([k for k in kinds() if k == "DRIVER_LATE"]) == 1,
   "a second late check-in the same day does not raise a SECOND alert row")

# ...but it must not vanish either. This shipped broken: dedupe_key was
# "late:<driver>:<day>", so once an alert existed the driver was muted for the
# rest of the day — every later check-in silently wrote nothing and the boss
# saw no update at all.
_late = [a for a in alerts() if a["kind"] == "DRIVER_LATE"][0]
ok("be in by 7:30" in _late["title"],
   "the repeat check-in UPDATED the alert with the new ETA (got %r)" % _late["title"])
ok(_late["body"] == "shop first", "and with the new reason")

# and a handled alert comes back when the driver sends again
c = app.get_db()
c.execute("UPDATE alerts SET resolved_at=?, read_at=? WHERE id=?",
          (app.now_ts(), app.now_ts(), _late["id"]))
c.commit(); c.close()
c = app.get_db(); c.execute("DELETE FROM late_checkins WHERE company_id=?", (co,)); c.commit(); c.close()
cl.post("/late/checkin", data={"_csrf_token": "t", "eta": "10 min", "reason": "almost there"})
_late2 = [a for a in alerts() if a["kind"] == "DRIVER_LATE"][0]
ok(_late2["resolved_at"] is None,
   "a new check-in re-opens an alert the boss had already marked handled")
ok(_late2["read_at"] is None, "and marks it unread again so the badge counts it")
ok(_late2["emailed_at"] is None and _late2["pushed_at"] is None,
   "and clears the delivery stamps so the update actually gets sent")
ok("10 min" in _late2["title"], "carrying the latest ETA")

# ── time off ──────────────────────────────────────────────────────────────
r = cl.post("/time-off/request", data={"_csrf_token": "t", "start_date": "2099-01-05", "reason": "family"})
ok("TIME_OFF_REQUEST" in kinds(), "time-off request raises an alert")
_to = [x for x in alerts() if x["kind"] == "TIME_OFF_REQUEST"][0]
ok(_to["severity"] == "info", "a time-off request is info, so it never holds the badge")

# ── driver message ────────────────────────────────────────────────────────
r = cl.post("/route/%d/messages" % rid,
            json={"_csrf_token": "t", "body": "gate is locked", "client_id": "c-1"})
ok(r.status_code == 200, "driver message accepted")
ok("DRIVER_MESSAGE" in kinds(), "a driver message raises an alert")
# replayed from the offline outbox
cl.post("/route/%d/messages" % rid, json={"_csrf_token": "t", "body": "gate is locked", "client_id": "c-1"})
ok(len([k for k in kinds() if k == "DRIVER_MESSAGE"]) == 1,
   "a replayed message raises no second alert")

# ── driver cancel ─────────────────────────────────────────────────────────
r = cl.post("/stop/%d/cancel" % sid,
            data={"_csrf_token": "t", "reason": "BOSS_SAID_CANCEL", "client_uuid": "u-9"})
ok("STOP_CANCELLED" in kinds(), "a driver cancelling a stop raises an alert")
_sc = [x for x in alerts() if x["kind"] == "STOP_CANCELLED"][0]
ok("Acme Roofing" in _sc["title"], "the cancel alert names the customer")
ok(_sc["entity_type"] == "stop" and _sc["entity_id"] == sid, "alert points back at the stop")

# ── the boss's own actions must NOT alert the boss ─────────────────────────
before = len(alerts())
as_boss()
cl.post("/route/%d/messages" % rid, json={"_csrf_token": "t", "body": "ok thanks", "client_id": "b-1"})
ok(len(alerts()) == before, "the boss's own message does not alert the boss")

# ── the feed ──────────────────────────────────────────────────────────────
html = cl.get("/boss/notifications").get_data(as_text=True)
ok(html.count("alert-card") >= 4, "feed renders every alert raised so far")
for needle in ["running late", "asked for time off", "sent a message", "cancelled a stop"]:
    ok(needle in html, "feed shows: %s" % needle)
ok("Mark handled" in html, "each open alert offers a way to close it")

# badge counts things needing a decision, and ignores info
c = app.get_db()
_open = app.alert_open_count(c, co)
_unread = app.alert_unread_count(c, co)
c.close()
ok(_open == 3, "badge counts the 3 warning/critical items, not the info one (got %d)" % _open)
ok(_unread == 0, "opening the feed marks everything read")

j = json.loads(cl.get("/api/alerts/count").data)
ok(j["count"] == _open, "the live badge endpoint agrees with the page")

# ── resolve ───────────────────────────────────────────────────────────────
target = [x for x in alerts() if x["severity"] != "info"][0]["id"]
r = cl.post("/alerts/%d/resolve" % target, data={"_csrf_token": "t"})
ok(r.status_code in (200, 302), "mark handled accepted")
ok(json.loads(cl.get("/api/alerts/count").data)["count"] == _open - 1,
   "handling one alert drops the badge by one")
open_html = cl.get("/boss/notifications").get_data(as_text=True)
all_html = cl.get("/boss/notifications?show=all").get_data(as_text=True)
ok(open_html.count("alert-card") < all_html.count("alert-card"),
   "handled alerts leave the 'needs you' view but stay in history")

# ── a driver can't read or resolve alerts ─────────────────────────────────
as_driver()
ok(cl.get("/boss/notifications").status_code in (302, 403), "driver cannot open the boss feed")
ok(cl.post("/alerts/%d/resolve" % target, data={"_csrf_token": "t"}).status_code in (302, 403),
   "driver cannot resolve alerts")

# ── push plumbing ─────────────────────────────────────────────────────────
as_boss()
cfg = json.loads(cl.get("/api/push/config").data)
ok("enabled" in cfg and "publicKey" in cfg, "push config endpoint answers")
ok(cfg["enabled"] is False, "push reports itself off with no VAPID keys set")
ok(app.push_configured() is False, "push_configured() false without keys")
ok(app.flush_alert_pushes(co) == 0, "the push sweep is a safe no-op when unconfigured")

SUB = {"endpoint": "https://fcm.googleapis.com/wp/abc123",
       "keys": {"p256dh": "BFake", "auth": "authfake"}}
r = cl.post("/api/push/register", json={"_csrf_token": "t", "subscription": SUB, "platform": "web"})
ok(r.status_code == 200, "a device can register a push subscription")
c = app.get_db()
row = c.execute("SELECT token FROM push_tokens WHERE company_id=?", (co,)).fetchone()
c.close()
ok(row is not None and "abc123" in row["token"], "the whole subscription is stored, endpoint and keys")

cl.post("/api/push/register", json={"_csrf_token": "t", "subscription": SUB, "platform": "web"})
c = app.get_db()
n = c.execute("SELECT COUNT(*) n FROM push_tokens WHERE company_id=?", (co,)).fetchone()["n"]
c.close()
ok(n == 1, "re-registering the same device updates rather than duplicates")

ok(cl.post("/api/push/register", json={"_csrf_token": "t"}).status_code == 400,
   "a missing subscription is rejected")
ok(cl.post("/api/push/register", json={"_csrf_token": "t", "subscription": {"keys": {}}}).status_code == 400,
   "a subscription with no endpoint is rejected")

html = cl.get("/boss/notifications").get_data(as_text=True)
ok("push-card" in html, "the phone-alerts row is on the page")
ok("firebasejs" not in html, "no Firebase scripts are loaded any more")
ok("applicationServerKey" in html, "the client subscribes through the standard PushManager")
ok("Add to Home Screen" in html,
   "iPhone users in a Safari tab are told why push can't work, instead of a button that fails")
ok("HaultraNativeApp" in html,
   "the store build is detected and told where push does work")

# ── email delivery ────────────────────────────────────────────────────────
# Email is the channel that reaches a phone TODAY: the Capacitor store builds
# have no Push API, so until native push exists this is what actually gets a
# breakdown in front of the boss.
_sent = []
_real_send = app.send_email
app.send_email = lambda to, subj, html: (_sent.append((to, subj, html)) or True)
try:
    c = app.get_db()
    c.execute("UPDATE users SET email='tim@haultraai.com' WHERE id=?", (boss,))
    c.execute("UPDATE users SET email='dave@example.com' WHERE id=?", (drv,))
    c.execute("UPDATE alerts SET emailed_at=? WHERE company_id=?", (app.now_ts(), co))
    c.commit()
    app.notify(c, co, "BREAKDOWN", "Dave Miller reported a breakdown",
               "Truck 12 hydraulics", severity="critical", link="/route/9")
    app.notify(c, co, "TIME_OFF_REQUEST", "Dave asked for a Friday", "2099-01-05")
    c.commit(); c.close()

    n = app.flush_alert_emails(co)
    ok(n == 1, "one email per critical alert, to the one boss with an address (got %d)" % n)
    to, subj, html = _sent[0]
    ok(to == "tim@haultraai.com", "sent to the boss")
    ok(not any(t == "dave@example.com" for t, _, _ in _sent), "drivers are never emailed alerts")
    ok(subj == "Dave Miller reported a breakdown",
       "the subject IS the alert, so a lock screen shows what happened")
    ok("/route/9" in html, "the email links straight to what the alert is about")
    ok(not any("Friday" in s2 for _, s2, _ in _sent), "info alerts are never emailed")
    ok(app.flush_alert_emails(co) == 0, "a second sweep re-sends nothing")

    # email and push claim independently
    c = app.get_db()
    row = c.execute("""SELECT emailed_at, pushed_at FROM alerts
                        WHERE company_id=? AND kind='BREAKDOWN' ORDER BY id DESC LIMIT 1""",
                    (co,)).fetchone()
    c.close()
    ok(row["emailed_at"] and not row["pushed_at"],
       "email and push stamp separately, so a dead push never costs you the email")

    os.environ["ALERT_EMAIL_TO"] = "dispatch@haultraai.com"
    c = app.get_db()
    app.notify(c, co, "ROUTE_CANCELLED", "Dave cancelled a route", "weather", severity="critical")
    c.commit(); c.close()
    _sent.clear()
    app.flush_alert_emails(co)
    ok(_sent and _sent[0][0] == "dispatch@haultraai.com",
       "ALERT_EMAIL_TO overrides the per-user addresses")
    os.environ.pop("ALERT_EMAIL_TO")
finally:
    app.send_email = _real_send

# ── relative time uses the same clock the rows were written with ──────────
ok(app._ago(app.now_ts()) == "just now",
   "a brand-new alert reads 'just now', not a timezone-skewed hours-ago (got %r)"
   % app._ago(app.now_ts()))

print("\nALL ALERT FEED TESTS PASSED")
