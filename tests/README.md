# Parser regression tests

Real dispatch texts, frozen as permanent regression fixtures, so the parser
never regresses on the boss's actual language.

## Run

```bash
# Strict, live — parses each text through the real /api/parse LLM parser:
ANTHROPIC_API_KEY=sk-... python tests/test_parser_real_texts.py

# Keyless (CI without a key) — self-tests the matcher engine and SKIPS the
# live assertions (exit 0). Never red-fails just for a missing key:
python tests/test_parser_real_texts.py
```

Exit code is non-zero if any **hard** expectation regresses. Advisory
expectations (LLM nuances we watch but don't gate on yet) print a `⚠` and
never fail the suite.

## Add a real text

Append an object to `fixtures` in [`parser_fixtures.json`](./parser_fixtures.json).
Never delete an existing fixture — that's the regression guard.

```json
{
  "id": "short-slug",
  "text": "the exact dispatch text, \\n for newlines",
  "expect": {
    "stop_count": 1,
    "fields": {
      "action":         {"equals_ci": "PR"},
      "address":        {"regex": "1234.*main\\s+st", "contains_ci": ["norfolk"]},
      "customer":       {"equals_ci": "Acme"},
      "container_size": {"equals_ci": "30yd"},
      "dump_leg":       {"equals_ci": "holland"},
      "return_leg":     {"empty": true},
      "confidence":     {"equals_ci": "high"}
    },
    "any_field_contains_ci": ["someToken"],
    "advisory": { "fields": { "empty_can_plan": {"nonempty": true} } }
  }
}
```

Matchers (all listed for a field must pass): `equals_ci`, `contains_ci` (list),
`oneof_ci` (list), `regex` (case-insensitive `re.search`), `empty`, `nonempty`.
Stop-level: `stop_count`, `stop_index`, `any_field_contains_ci`. Put anything
uncertain under `advisory` so it's reported without failing the suite; promote
it into `fields` once confirmed against a live run.
