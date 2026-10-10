"""Sheet scan: boss photographs the paper Daily Route Log -> stops JSON (2026-10-10).

The Claude Vision call is mocked (no API key / photo needed); the endpoint's
validation, auth, JSON salvage, and stop-cleaning are exercised for real.

Run:  ~/workspace/.haultra-venv/bin/python tests/test_garbage_scan.py
"""
import io
import os
import sys
import json
import tempfile
import importlib
import types

TMP = tempfile.mkdtemp(prefix="haultra-scan-")
os.environ["DATABASE_PATH"] = os.path.join(TMP, "s.db")
os.environ["SECRET_KEY"] = "s"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
os.environ["ANTHROPIC_API_KEY"] = "test-key"
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# Mock anthropic BEFORE app import (the endpoint imports it lazily, so a
# sys.modules entry is enough).
VISION_REPLY = json.dumps({
    "stops": [
        {"service_type": "toter", "address": "2545 Squadron Ct", "city": "VB",
         "notes": "", "not_before": ""},
        {"service_type": "hpu", "address": "800 Gas Light Ln", "city": "VB",
         "notes": "all cans and bags", "not_before": "7am"},
        {"service_type": "landfill", "address": "GFL", "city": "",
         "notes": "dump here every Friday", "not_before": ""},
        {"service_type": "bogus", "address": "Nowhere", "city": ""},
        {"service_type": "toter", "address": "", "city": "VB"},
    ]
})


class _FakeBlock:
    type = "text"

    def __init__(self, text):
        self.text = text


class _FakeResp:
    content = [_FakeBlock(VISION_REPLY)]


class _FakeMessages:
    def create(self, **kwargs):
        # The photo must actually ride along.
        content = kwargs["messages"][0]["content"]
        assert any(b.get("type") == "image" for b in content), "no image sent"
        assert "Daily Route Log" in kwargs["system"], "wrong system prompt"
        return _FakeResp()


class _FakeClient:
    def __init__(self, api_key=None, timeout=None):
        assert api_key == "test-key"
        self.messages = _FakeMessages()


fake_anthropic = types.ModuleType("anthropic")
fake_anthropic.Anthropic = _FakeClient
sys.modules["anthropic"] = fake_anthropic

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
cur.execute("INSERT INTO companies (name, slug, subscription_plan, subscription_status, max_drivers, created_at)"
            " VALUES (?,?,?,?,?,?)", ("S Co", "sco", "pro", "active", 10, ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id, created_at)"
            " VALUES (?,?,?,?,?,?)", ("s_boss", "x", "boss", "S Boss", co, ts))
boss = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id, created_at)"
            " VALUES (?,?,?,?,?,?)", ("s_drv", "x", "driver", "S Driver", co, ts))
drv = cur.lastrowid
conn.commit()

app.app.config["TESTING"] = True
cl = app.app.test_client()


def login_as(uid, role):
    roles = [role] + (["owner", "dispatcher", "customer_manager"] if role == "boss" else [])
    with cl.session_transaction() as s:
        s.update(user_id=uid, company_id=co, role=role, roles=roles, _csrf_token="tok")


def scan(data=None, file_bytes=None, filename="sheet.jpg"):
    if file_bytes is None:
        file_bytes = b"\xff\xd8" + b"x" * 5000  # fake jpeg-ish payload
    return cl.post("/api/garbage/scan-sheet",
                   data={"photo": (io.BytesIO(file_bytes), filename),
                         "_csrf_token": "tok"},
                   content_type="multipart/form-data")


# Happy path: photo -> cleaned stops.
login_as(boss, "boss")
r = scan()
j = r.get_json()
ok(r.status_code == 200 and j.get("success"), "scan succeeds")
ok(j.get("count") == 3, "bad rows filtered (bogus type, empty address)")
got = [(s["service_type"], s["address"], s["city"], s["not_before"]) for s in j["stops"]]
ok(got[0] == ("toter", "2545 Squadron Ct", "VB", ""), "toter row extracted")
ok(got[1] == ("hpu", "800 Gas Light Ln", "VB", "7am"), "hpu row + not_before extracted")
ok(got[2][0] == "landfill" and got[2][1] == "GFL", "landfill row extracted")
ok(j["stops"][1]["notes"] == "all cans and bags", "notes preserved")

# No photo -> 400.
r = cl.post("/api/garbage/scan-sheet", data={"_csrf_token": "tok"})
ok(r.status_code == 400, "missing photo rejected")

# Tiny file -> 400.
r = scan(file_bytes=b"xx")
ok(r.status_code == 400, "empty photo rejected")

# Oversized -> 400.
r = scan(file_bytes=b"x" * (10 * 1024 * 1024 + 1))
ok(r.status_code == 400, "oversized photo rejected")

# Driver cannot scan.
login_as(drv, "driver")
r = scan()
ok(r.status_code == 403, "driver blocked from scanning")

# Dispatch page carries the scan button.
login_as(boss, "boss")
html = cl.get("/garbage-dispatch").get_data(as_text=True)
ok("gd-scan-btn" in html and "scan-sheet" in html, "dispatch page has scan button")

conn.close()
print()
if FAILURES:
    print("FAILURES (%d):" % len(FAILURES))
    for f in FAILURES:
        print("  - " + f)
    sys.exit(1)
print("ALL CHECKS PASSED")
