"""If the LLM parser returns a wayward reply (prose, bare array, odd envelope),
/api/parse must salvage the stops — and when nothing is salvageable it must
fall back to the local rule-based parser instead of 502ing with
"Parser returned invalid format — try re-parsing".

Regression for the 2026-10-08 field report: the boss's dispatch text
    Pr 1013 paragon way,suff, napo 3075 at array 1004 serene rd dump holland
    Pr 1013 paragon way,suff, napo 3053 at 1001 serene rd dump holland
    Pr 1110 n main st,suff, sifen 30yd dump holland
kept failing with "Parser returned invalid format". The deterministic local
parser handles that text fine, so it is the correct degraded path.

Run:  ~/workspace/.haultra-venv/bin/python tests/test_parse_llm_fallback.py
"""
import json
import os
import sys
import tempfile
import types

TMPDIR = tempfile.mkdtemp(prefix="haultra-llmfb-")
os.environ["DATABASE_PATH"] = os.path.join(TMPDIR, "llmfb.db")
os.environ["SECRET_KEY"] = "testsecret123"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMPDIR, "uploads")
os.environ["ANTHROPIC_API_KEY"] = "test-key-not-real"
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import app  # noqa: E402

FAILURES = []


def ok(cond, label):
    print(("PASS" if cond else "FAIL") + " - " + label, flush=True)
    if not cond:
        FAILURES.append(label)


# ── Seed ───────────────────────────────────────────────────────────────
app.init_db()
conn = app.get_db()
cur = conn.cursor()
ts = app.now_ts()
cur.execute(
    "INSERT INTO companies (name, slug, subscription_plan, subscription_status,"
    " max_drivers, created_at) VALUES (?,?,?,?,?,?)",
    ("Fallback Co", "fallbackco", "pro", "active", 10, ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
            " created_at) VALUES (?,?,?,?,?,?)",
            ("fb_boss", "x", "boss", "Boss", co, ts))
boss = cur.lastrowid
for nm, ad, ct in [("Napo", "1013 Paragon Way", "Suffolk"),
                   ("Sifen", "6417 Providence Rd", "Virginia Beach")]:
    cur.execute(
        "INSERT INTO saved_addresses (company_id, customer_name, address, city,"
        " state, kind, times_used, created_at, last_used_at)"
        " VALUES (?,?,?,?,'VA','customer',5,?,?)",
        (co, nm, ad, ct, ts, ts))
cur.execute("INSERT INTO dump_locations (company_id, name, city, active, created_at)"
            " VALUES (?,?,?,1,?)", (co, "Holland", "Suffolk", ts))
conn.commit()
conn.close()

BOSS_TEXT = """Pr 1013 paragon way,suff, napo 3075 at array 1004 serene rd dump holland
Pr 1013 paragon way,suff, napo 3053 at 1001 serene rd dump holland
Pr 1110 n main st,suff, sifen 30yd dump holland"""


# ── 1. Salvage unit tests ──────────────────────────────────────────────
GOOD = {"stops": [{"action": "PR", "address": "1 Main St"}]}
ok(app._salvage_parse_response(json.dumps(GOOD)) == GOOD["stops"],
   "salvage: clean envelope passes through")
ok(app._salvage_parse_response("```json\n" + json.dumps(GOOD) + "\n```") == GOOD["stops"],
   "salvage: fenced JSON passes through")
ok(app._salvage_parse_response(json.dumps(GOOD["stops"])) == GOOD["stops"],
   "salvage: bare top-level array is wrapped")
ok(app._salvage_parse_response(
    "Here is your parse:\n" + json.dumps(GOOD) + "\nHope this helps!") == GOOD["stops"],
   "salvage: prose-wrapped JSON is extracted")
ok(app._salvage_parse_response(
    json.dumps({"route": GOOD})) == GOOD["stops"],
   "salvage: alternate envelope {'route': {...}} is unwrapped")
ok(app._salvage_parse_response("sorry, I cannot parse this dispatch") is None,
   "salvage: pure prose returns None")
ok(app._salvage_parse_response(json.dumps({"stops": "oops-not-a-list"})) is None,
   "salvage: non-list stops returns None")
ok(app._salvage_parse_response("") is None,
   "salvage: empty reply returns None")
ok(app._salvage_parse_response(json.dumps({"stops": [{"a": 1}, "junk", 42]})) == [{"a": 1}],
   "salvage: non-dict entries are dropped, dicts kept")


# ── 2. Rule-based fallback mapping on the boss's exact text ────────────
conn = app.get_db()
rule_stops = app.parse_route_text(BOSS_TEXT, conn, co)
conn.close()
mapped = [m for m in (app._rule_stop_to_llm_shape(s) for s in rule_stops) if m]
ok(len(mapped) == 3, "fallback maps the boss text to exactly 3 stops (got %d)" % len(mapped))
if len(mapped) == 3:
    m1, m2, m3 = mapped
    ok(all(m["action"] == "PR" for m in mapped), "all three fallback stops are PR")
    ok(m1["address"] == "1013 paragon way, Suffolk", "stop 1 address + suff->Suffolk")
    ok(m1["customer"] == "napo", "stop 1 customer cleaned to 'napo'")
    ok("can 3075" in m1["notes"] and "1004 serene rd" in m1["notes"],
       "stop 1 keeps can number + can location in notes")
    ok(m2["customer"] == "napo" and "can 3053" in m2["notes"],
       "stop 2 customer cleaned, can 3053 in notes")
    ok(m3["customer"] == "sifen" and m3["container_size"] == "30yd",
       "stop 3 customer 'sifen', 30yd kept")
    ok(m3["address"] == "1110 n main st, Suffolk", "stop 3 address + city")
    ok(all(m["dump_leg"] == "Holland" for m in mapped), "dump leg Holland on all three")
    ok(all(m["confidence"] in ("high", "low") for m in mapped),
       "confidence stays in the low/high vocabulary the sheet expects")
    ok(all(m["source"] == "rule" for m in mapped), "fallback stops tagged source='rule'")


# ── 3. Endpoint: garbage LLM reply → 200 + rule-based stops + warning ───
class _FakeMsg:
    def __init__(self, text):
        self.content = [types.SimpleNamespace(type="text", text=text)]


class _FakeAnthropic:
    reply = ""

    def __init__(self, api_key=None, timeout=None):
        pass

    @property
    def messages(self):
        outer = self

        class _M:
            def create(self, **kw):
                return _FakeMsg(outer.reply)

        return _M()


_fake_mod = types.ModuleType("anthropic")
_fake_mod.Anthropic = _FakeAnthropic
for _en in ("APITimeoutError", "APIConnectionError", "RateLimitError", "APIStatusError"):
    setattr(_fake_mod, _en, type(_en, (Exception,), {}))
_real_anthropic = sys.modules.get("anthropic")
sys.modules["anthropic"] = _fake_mod

app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=boss, company_id=co, roles=["dispatcher"], _csrf_token="tok")


def post_parse(text):
    return cl.post("/api/parse", json={"text": text, "manual_stops": []},
                   headers={"X-CSRF-Token": "tok"})


_FakeAnthropic.reply = "Sure! Here are the stops as a list:\n- PR 1013 paragon way\nHave a great day!"
r = post_parse(BOSS_TEXT)
ok(r.status_code == 200, "garbage LLM reply -> HTTP 200 via fallback (got %d)" % r.status_code)
j = r.get_json() or {}
ok(isinstance(j.get("stops"), list) and len(j["stops"]) == 3,
   "fallback returns the 3 parsed stops (got %s)" % (len(j.get("stops", [])) if isinstance(j.get("stops"), list) else type(j.get("stops"))))
ok(j.get("fallback") == "rule-based", "response flags fallback='rule-based'")
ok(bool(j.get("warning")), "response carries a human-readable warning")
ok("invalid format" not in json.dumps(j).lower(), "no 'invalid format' error in fallback response")
if isinstance(j.get("stops"), list) and len(j["stops"]) == 3:
    ok(j["stops"][0]["action"] == "PR" and "Suffolk" in j["stops"][0]["address"],
       "fallback stop 1 is a usable PR stop")

# Garbage LLM reply AND nothing parseable locally -> the old 502, not a crash.
_orig_parse = app.parse_route_text
app.parse_route_text = lambda text, c, cid_: []
try:
    r = post_parse("Pr 1013 paragon way,suff, napo dump holland")
    ok(r.status_code == 502, "unsalvageable + empty local parse -> 502 (got %d)" % r.status_code)
    ok("invalid format" in (r.get_json() or {}).get("error", ""),
       "502 body keeps the original 'invalid format' message")
finally:
    app.parse_route_text = _orig_parse

# Valid LLM reply still takes the normal path (no fallback flag).
_FakeAnthropic.reply = json.dumps(
    {"stops": [{"action": "PR", "address": "1013 Paragon Way, Suffolk",
                "customer": "Napo", "container_size": None, "dump_leg": "Holland",
                "return_leg": None, "empty_can_plan": None, "raw": "x",
                "confidence": "high", "notes": "", "chain_hint": None}]})
r = post_parse(BOSS_TEXT)
j = r.get_json() or {}
ok(r.status_code == 200 and len(j.get("stops", [])) == 1,
   "valid LLM reply still returns its stops untouched")
ok("fallback" not in j and not j.get("partial_failure"),
   "valid LLM reply sets no fallback/partial_failure flags")
if j.get("stops"):
    ok(j["stops"][0].get("source") == "ai", "normal-path stops still tagged source='ai'")

if _real_anthropic is not None:
    sys.modules["anthropic"] = _real_anthropic
else:
    del sys.modules["anthropic"]

print()
if FAILURES:
    print("FAILURES (%d):" % len(FAILURES))
    for f in FAILURES:
        print("  - " + f)
    sys.exit(1)
print("ALL CHECKS PASSED")
