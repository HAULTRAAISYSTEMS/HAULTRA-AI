"""Regression guard: no tappable sticky header may sit under the iOS status bar.

Every page that declares `apple-mobile-web-app-status-bar-style=black-translucent`
tells iOS to draw web content from y=0, underneath the system status bar. iOS
swallows touches inside that strip, so a sticky header pinned to `top: 0` with a
plain pixel padding renders fine but is DEAD ON TAP in portrait. It appears to
"work" only in landscape, where the strip shrinks out of the way.

That shipped in static/parser.html and made its back link untappable in the
1.0.0(1) App Store submission build. Two things are required together:

  1. `viewport-fit=cover` in the viewport meta — without it every
     `env(safe-area-inset-*)` resolves to 0 and the padding silently does nothing.
  2. `env(safe-area-inset-top)` folded into the sticky header's top padding.

Checking (1) without (2) is the trap this test exists to catch: the CSS looks
correct in review and computes to zero on device.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# (file, CSS selector of the sticky header that owns the status-bar strip)
TRANSLUCENT_PAGES = [
    ("static/parser.html", ".topbar"),
    ("static/route.html", ".status-bar"),
]

failures = []


def ok(condition, message):
    print(("PASS" if condition else "FAIL") + " - " + message)
    if not condition:
        failures.append(message)


def rule_body(css, selector):
    """The declaration block for `selector`, or None. Good enough for these
    hand-written single-file pages; no CSS parser dependency."""
    match = re.search(
        r"(?:^|[},;>])\s*" + re.escape(selector) + r"\s*\{(.*?)\}", css, re.S
    )
    return match.group(1) if match else None


for rel, selector in TRANSLUCENT_PAGES:
    path = ROOT / rel
    ok(path.exists(), f"{rel} exists")
    if not path.exists():
        continue
    html = path.read_text(encoding="utf-8")

    translucent = "black-translucent" in html
    ok(translucent, f"{rel} still declares a translucent status bar (test premise)")
    if not translucent:
        continue

    viewport = re.search(r'<meta\s+name="viewport"[^>]*content="([^"]*)"', html)
    ok(viewport is not None, f"{rel} has a viewport meta")
    ok(
        viewport is not None and "viewport-fit=cover" in viewport.group(1),
        f"{rel} viewport sets viewport-fit=cover, so env(safe-area-inset-*) is non-zero",
    )

    body = rule_body(html, selector)
    ok(body is not None, f"{rel} defines {selector}")
    if body is None:
        continue

    sticky = "sticky" in body or "fixed" in body
    ok(sticky, f"{rel} {selector} is pinned to the top (test premise)")

    padding = [
        line for line in body.splitlines()
        if re.search(r"\bpadding(-top)?\s*:", line)
    ]
    ok(
        any("safe-area-inset-top" in line for line in padding),
        f"{rel} {selector} pads its top by env(safe-area-inset-top) "
        f"— otherwise its tap targets sit under the iOS status bar",
    )

# Bottom edge: the home-indicator band. capacitor.config.json sets
# ios.contentInset="never", so a bar pinned to bottom:0 really does reach the
# physical edge. iOS paints the indicator pill over it and takes drags that
# start there, so a control without the inset is degraded or dead. Checking the
# top inset alone missed this: .bottom-bar sat one selector away from .topbar
# in a file this test already covered.
BOTTOM_BARS = [
    ("static/parser.html", ".bottom-bar"),   # driver select + Confirm & Dispatch
    ("static/route.html", ".bottom-bar"),    # driver name + Logout
]

for rel, selector in BOTTOM_BARS:
    path = ROOT / rel
    body = rule_body(path.read_text(encoding="utf-8"), selector) if path.exists() else None
    ok(body is not None, f"{rel} defines {selector}")
    if body is None:
        continue
    ok(
        "bottom: 0" in body or "bottom:0" in body,
        f"{rel} {selector} is pinned to the bottom (test premise)",
    )
    ok(
        "safe-area-inset-bottom" in body,
        f"{rel} {selector} pads its bottom by env(safe-area-inset-bottom) "
        f"— otherwise its controls sit in the home-indicator band",
    )

# Sweep both files for any OTHER rule that pins to the bottom without the inset.
# Exempt: containers whose own inner footer carries the inset, so no control of
# theirs ever lands in the band. Each exemption names the rule that covers it —
# if that rule loses its inset, its own check above fails.
BOTTOM_PINNED_EXEMPT = {
    ("static/parser.html", ".sheet"): ".sheet-foot",
}

for rel, _ in BOTTOM_BARS:
    css = (ROOT / rel).read_text(encoding="utf-8")
    for match in re.finditer(r"([.#][\w-]+)\s*\{([^}]*)\}", css):
        sel, decls = match.group(1), match.group(2)
        pinned = re.search(r"position\s*:\s*fixed", decls) and re.search(
            r"bottom\s*:\s*0", decls
        )
        if not pinned or "safe-area-inset-bottom" in decls:
            continue
        covered_by = BOTTOM_PINNED_EXEMPT.get((rel, sel))
        if covered_by:
            inner = rule_body(css, covered_by)
            ok(
                inner is not None and "safe-area-inset-bottom" in inner,
                f"{rel} {sel} is exempt because {covered_by} carries the inset",
            )
            continue
        ok(False, f"{rel} {sel} pins to bottom:0 with no safe-area-inset-bottom")

# The main app shell in app.py is the reference implementation the pages above
# mirror. Its CSS lives inside an f-string with doubled braces, so scan a window
# after the selector rather than trying to brace-match it.
app_py = (ROOT / "app.py").read_text(encoding="utf-8")
topnav_at = app_py.find(".topnav {{")
ok(topnav_at != -1, "app.py still defines the app shell .topnav")
ok(
    topnav_at != -1
    and "safe-area-inset-top" in app_py[topnav_at:topnav_at + 900],
    "app.py .topnav still owns the status-bar strip",
)
ok(
    "viewport-fit=cover" in app_py,
    "app.py app shell viewport sets viewport-fit=cover",
)

# The phone-only parser bar carries Parse Route / Build Route and is the only
# place those buttons exist at phone width, so a reviewer's device is the only
# device that ever renders it.
bar_at = app_py.find("#pr-mobile-bar{")
ok(bar_at != -1, "app.py still defines #pr-mobile-bar")
ok(
    bar_at != -1 and "safe-area-inset-bottom" in app_py[bar_at:bar_at + 400],
    "app.py #pr-mobile-bar clears the home-indicator band",
)

# The offline banner outranks .topnav (z-index 10000 vs 200) and reassigns
# cssText wholesale on every state change, so no stylesheet can patch it from
# outside — the inset has to be in _BASE_CSS itself.
base_at = app_py.find("var _BASE_CSS = (")
ok(base_at != -1, "app.py still defines the offline banner _BASE_CSS")
ok(
    base_at != -1
    and "safe-area-inset-top" in app_py[base_at:base_at + 600],
    "app.py offline banner reserves the status-bar strip",
)

# The cab view's STOP n OF m / END ROUTE bar is sticky inside the same scroll
# context as the sticky .topnav; pinned at top:0 it slides underneath and
# becomes unreachable.
cab_at = app_py.find(".cab-sticky-bar {{")
ok(cab_at != -1, "app.py still defines .cab-sticky-bar")
ok(
    cab_at != -1 and "--haul-topnav-h" in app_py[cab_at:cab_at + 400],
    "app.py .cab-sticky-bar pins below the topnav, not underneath it",
)
ok(
    "--haul-topnav-h'," in app_py or '--haul-topnav-h"' in app_py
    or "setProperty(\n      '--haul-topnav-h'" in app_py,
    "app.py publishes --haul-topnav-h from the shell",
)

if failures:
    raise SystemExit("FAILED: " + "; ".join(failures))

print("\nALL SAFE-AREA INSET TESTS PASSED")
