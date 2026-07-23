#!/usr/bin/env python3
"""Permanent parser regression suite — runs REAL dispatch texts through the
live /api/parse LLM parser and asserts the structured output, so we never
regress on the boss's actual language.

Fixtures live in tests/parser_fixtures.json (append new real texts there).

Running:
  ANTHROPIC_API_KEY=sk-... python tests/test_parser_real_texts.py     # strict, live
  python tests/test_parser_real_texts.py                              # skips live asserts

Behavior:
  - With a key: each fixture is parsed for real; every hard matcher must pass or
    the suite exits non-zero. A per-field expected-vs-actual diff is printed.
  - Without a key: /api/parse returns "not configured"; the suite SKIPS the live
    assertions (exit 0) but still self-tests its own matcher engine so the
    harness itself stays trustworthy in keyless CI.

Also importable as pytest (test_parser_real_texts()).
"""
import os
import re
import sys
import json
import tempfile
import importlib

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
FIXTURES_PATH = os.path.join(HERE, "parser_fixtures.json")

# ── ANSI (falls back to plain if not a TTY) ──────────────────────────────────
_C = sys.stdout.isatty()
def _g(s): return f"\033[32m{s}\033[0m" if _C else s
def _r(s): return f"\033[31m{s}\033[0m" if _C else s
def _y(s): return f"\033[33m{s}\033[0m" if _C else s


# ── Matcher engine ───────────────────────────────────────────────────────────
def _match_field(matchers, value):
    """Apply a dict of matchers to a single field value. Returns (ok, reason)."""
    v = "" if value is None else str(value)
    vl = v.strip().lower()
    for kind, arg in matchers.items():
        if kind == "equals_ci":
            if vl != str(arg).strip().lower():
                return False, f"equals_ci {arg!r} (got {v!r})"
        elif kind == "contains_ci":
            for sub in arg:
                if str(sub).lower() not in vl:
                    return False, f"contains {sub!r} (got {v!r})"
        elif kind == "oneof_ci":
            if vl not in [str(a).strip().lower() for a in arg]:
                return False, f"oneof {arg!r} (got {v!r})"
        elif kind == "regex":
            if not re.search(arg, v, re.I):
                return False, f"regex /{arg}/ (got {v!r})"
        elif kind == "empty":
            if arg and vl != "":
                return False, f"expected empty (got {v!r})"
        elif kind == "nonempty":
            if arg and vl == "":
                return False, "expected non-empty (got empty)"
        else:
            return False, f"unknown matcher {kind!r}"
    return True, f"ok ({v!r})" if v else "ok (empty)"


def _stop_blob(stop):
    """All string-ish field values of a stop, lowercased, for any-field checks."""
    parts = []
    for k, val in stop.items():
        if isinstance(val, (str, int, float)) and not isinstance(val, bool):
            parts.append(str(val))
    return " ⁣ ".join(parts).lower()


def _check_group(fields, stop, advisory=False):
    """Check a group of field matchers against a stop. Returns (all_ok, lines)."""
    ok_all = True
    lines = []
    mark = _y("⚠") if advisory else None
    for field, matchers in (fields or {}).items():
        ok, reason = _match_field(matchers, stop.get(field))
        if ok:
            lines.append(f"      {_g('✓')} {field}: {reason}")
        else:
            ok_all = False
            sym = mark if advisory else _r("✗")
            lines.append(f"      {sym} {field}: expected {reason}")
    return ok_all, lines


def _check_fixture(fx, stops):
    """Run one fixture's expectations against the parsed stops. Returns
    (hard_ok, advisory_ok, report_lines)."""
    exp = fx["expect"]
    lines = []
    hard_ok = True

    # stop_count
    want_n = exp.get("stop_count")
    if want_n is not None:
        if len(stops) == want_n:
            lines.append(f"      {_g('✓')} stop_count: {len(stops)}")
        else:
            hard_ok = False
            lines.append(f"      {_r('✗')} stop_count: expected {want_n}, got {len(stops)}")

    idx = exp.get("stop_index", 0)
    stop = stops[idx] if len(stops) > idx else {}
    blob = _stop_blob(stop)

    # hard field matchers
    ok, flines = _check_group(exp.get("fields"), stop)
    hard_ok = hard_ok and ok
    lines += flines

    # hard any_field_contains_ci
    for sub in exp.get("any_field_contains_ci", []):
        if str(sub).lower() in blob:
            lines.append(f"      {_g('✓')} any-field contains {sub!r}")
        else:
            hard_ok = False
            lines.append(f"      {_r('✗')} any-field contains {sub!r} (not found)")

    # advisory (reported, never fails the suite)
    adv = exp.get("advisory") or {}
    advisory_ok = True
    aok, alines = _check_group(adv.get("fields"), stop, advisory=True)
    advisory_ok = advisory_ok and aok
    lines += alines
    for sub in adv.get("any_field_contains_ci", []):
        if str(sub).lower() in blob:
            lines.append(f"      {_g('✓')} (advisory) any-field contains {sub!r}")
        else:
            advisory_ok = False
            lines.append(f"      {_y('⚠')} (advisory) any-field contains {sub!r} (not found)")

    return hard_ok, advisory_ok, lines


# ── Matcher engine self-test (runs even without a key) ───────────────────────
def _self_test_matchers():
    sample = {"action": "PR", "address": "7021 Harbour View Blvd, Suffolk",
              "customer": "Ew", "container_size": "40yd", "dump_leg": "Holland",
              "return_leg": "", "confidence": "high", "notes": "at vista 23"}
    checks = [
        ({"equals_ci": "pr"}, "action", True),
        ({"regex": "7021.*harbou?r\\s+view", "contains_ci": ["suffolk"]}, "address", True),
        ({"equals_ci": "EW"}, "customer", True),
        ({"empty": True}, "return_leg", True),
        ({"equals_ci": "30yd"}, "container_size", False),   # wrong on purpose
        ({"contains_ci": ["vista 23"]}, "notes", True),
    ]
    for matchers, field, want in checks:
        ok, _ = _match_field(matchers, sample.get(field))
        assert ok is want, f"self-test failed: {field} {matchers} expected {want}"
    assert "7021 harbour view blvd, suffolk" in _stop_blob(sample)
    return True


# ── Live parse via the real /api/parse endpoint ──────────────────────────────
def _make_client():
    """Boot the app on a fresh temp DB and return a test client logged in as the
    bootstrap company's boss. The bootstrap company already carries the seeded
    dump sites + shorthand, mirroring company 1's real parser environment, so the
    company-1 fixtures parse against the same vocabulary the boss actually has."""
    tmp = tempfile.mkdtemp()
    os.environ.setdefault("DATABASE_PATH", os.path.join(tmp, "parsertest.db"))
    os.environ.setdefault("SECRET_KEY", "parser-test")
    os.environ.setdefault("UPLOAD_FOLDER", os.path.join(tmp, "uploads"))
    os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
    sys.path.insert(0, REPO)
    app = importlib.import_module("app")

    conn = app.get_db()
    co = conn.execute("SELECT id FROM companies ORDER BY id LIMIT 1").fetchone()
    company_id = co["id"]
    boss = conn.execute(
        "SELECT id FROM users WHERE company_id=? AND role='boss' ORDER BY id LIMIT 1",
        (company_id,)
    ).fetchone()
    conn.close()
    boss_id = boss["id"] if boss else 1

    app.app.config["TESTING"] = True
    client = app.app.test_client()
    with client.session_transaction() as s:
        s["user_id"] = boss_id
        s["role"] = "boss"
        s["roles"] = ["owner", "dispatcher"]
        s["company_id"] = company_id
        s["_csrf_token"] = "tok"
    return client


def _parse(client, text):
    """POST to the real /api/parse. Returns (stops, skip_reason)."""
    resp = client.post("/api/parse", json={"_csrf_token": "tok", "text": text})
    if resp.status_code != 200:
        data = resp.get_json(silent=True) or {}
        err = (data.get("error") or "")
        if "ANTHROPIC_API_KEY not configured" in err or "AI package not installed" in err:
            return None, err or f"HTTP {resp.status_code}"
        # A real failure (bad request, parser error) — surface it as a failure.
        return None, None if resp.status_code >= 500 and not err else err
    return (resp.get_json() or {}).get("stops"), None


# ── Runner ───────────────────────────────────────────────────────────────────
def _load_companies(doc):
    """Support both the company-keyed schema (preferred) and a legacy flat
    'fixtures' list, so old fixture files keep working."""
    if "companies" in doc:
        return doc["companies"]
    return [{"company_key": "default", "label": "default", "fixtures": doc.get("fixtures", [])}]


def run():
    with open(FIXTURES_PATH, encoding="utf-8") as f:
        doc = json.load(f)
    companies = _load_companies(doc)
    total = sum(len(c.get("fixtures", [])) for c in companies)

    print("Parser real-text regression suite")
    print(f"  companies: {len(companies)}   fixtures: {total}   ({FIXTURES_PATH})")

    # 1) Always self-test the matcher engine so the harness is trustworthy.
    _self_test_matchers()
    print(f"  {_g('✓')} matcher engine self-test passed")

    client = _make_client()
    # Probe once to detect a missing key up front.
    first_text = next((fx["text"] for c in companies for fx in c.get("fixtures", [])), None)
    if first_text is None:
        print("  no fixtures — nothing to run")
        return 0
    _, skip = _parse(client, first_text)
    if skip:
        print(f"\n  {_y('SKIP')} live parse unavailable: {skip}")
        print("  Set ANTHROPIC_API_KEY to run the live assertions. Harness OK.")
        return 0

    hard_fail = 0
    adv_warn = 0
    for comp in companies:
        fixtures = comp.get("fixtures", [])
        print(f"\n  ── {comp.get('label', comp.get('company_key', '?'))} "
              f"({len(fixtures)} fixture(s)) ──")
        for fx in fixtures:
            stops, s = _parse(client, fx["text"])
            print(f"\n  • {fx['id']}")
            print(f"    text: {fx['text']!r}")
            if s is not None or stops is None:
                hard_fail += 1
                print(f"    {_r('FAIL')} parser error: {s or 'no stops returned'}")
                continue
            hard_ok, adv_ok, lines = _check_fixture(fx, stops)
            print("    actual: " + json.dumps(stops, ensure_ascii=False))
            for ln in lines:
                print(ln)
            if not hard_ok:
                hard_fail += 1
                print(f"    {_r('FAIL')}")
            else:
                print(f"    {_g('PASS')}")
                if not adv_ok:
                    adv_warn += 1
                    print(f"    {_y('(advisory expectations not met — watch, not failing)')}")

    print("\n" + "=" * 60)
    print(f"  {total - hard_fail}/{total} fixtures passed"
          + (f", {adv_warn} with advisory warnings" if adv_warn else ""))
    if hard_fail:
        print(f"  {_r('SUITE FAILED')} — {hard_fail} fixture(s) regressed")
        return 1
    print(f"  {_g('SUITE PASSED')}")
    return 0


def test_parser_real_texts():
    """pytest entry point — never fails for a missing key (skips live)."""
    assert run() == 0


if __name__ == "__main__":
    sys.exit(run())
