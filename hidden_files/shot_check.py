#!/usr/bin/env python3
"""HAULTRA viewport check — screenshot key pages at phone/tablet/desktop widths.

Usage:  python3 hidden_files/shot_check.py
Output: hidden_files/shots/<timestamp>/*.png

The three device classes:
  phone    390px  — iPhone / Samsung, bottom tabs, single column
  tablet   820px  — iPad, top nav, roomier layout
  desktop 1440px  — MacBook / PC, top nav, widest layout

Run this before every push that touches layout/CSS. Look at each shot and
confirm: nav is present (bottom tabs on phone, top nav on tablet/desktop),
no horizontal overflow, no overlapping elements, action bars reachable.
"""
import os, re, sys, subprocess
from datetime import datetime

WIDTHS = {"phone": 390, "tablet": 820, "desktop": 1440}
HEIGHT = 900
CHROME = os.path.expanduser(
    "~/.cache/ms-playwright/chromium_headless_shell-1243/"
    "chrome-headless-shell-linux64/chrome-headless-shell")

PAGES = [
    ("/routes", "board"),
    ("/requests", "requests"),
    ("/customers", "customers"),
    ("/invoices", "invoices"),
    ("/bin-tracker", "bins"),
    ("/messages", "messages"),
    ("/garbage-dispatch", "garbage"),
]


def main():
    here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    sys.path.insert(0, here)
    os.chdir(here)
    os.environ.setdefault("SECRET_KEY", "test123")
    os.environ.setdefault("DATABASE_PATH", "/tmp/test_haultra.db")

    import app  # noqa: E402
    stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
    outdir = os.path.join(here, "hidden_files", "shots", stamp)
    os.makedirs(outdir, exist_ok=True)

    c = app.app.test_client()
    with c.session_transaction() as s:
        s["user_id"] = 1
        s["username"] = "boss"
        s["role"] = "boss"
        s["roles"] = ["boss", "owner", "dispatcher", "customer_manager"]
        s["company_id"] = 1

    html_files = {}
    for url, name in PAGES:
        r = c.get(url)
        html = r.get_data(as_text=True)
        # Strip <style> so the check below inspects real markup, not CSS text
        body = re.sub(r"<style.*?</style>", "", html, flags=re.S)
        nav_ok = ("haul-tabbar" in body) or ("topnav" in body)
        print(f"{name:10} status={r.status_code} nav_present={nav_ok}")
        path = os.path.join(outdir, f"{name}.html")
        with open(path, "w") as f:
            f.write(html)
        html_files[name] = path

    # parser.html is a static file — screenshot it directly
    parser_src = os.path.join(here, "static", "parser.html")
    parser_dst = os.path.join(outdir, "parser.html")
    with open(parser_src) as f, open(parser_dst, "w") as g:
        g.write(f.read())
    html_files["parser"] = parser_dst
    print(f"{'parser':10} static file copied")

    for name, html_path in html_files.items():
        for label, w in WIDTHS.items():
            png = os.path.join(outdir, f"{name}_{label}_{w}.png")
            subprocess.run(
                [CHROME, "--headless", "--disable-gpu", "--no-sandbox",
                 "--virtual-time-budget=4000",
                 f"--window-size={w},{HEIGHT}",
                 f"--screenshot={png}", f"file://{html_path}"],
                capture_output=True, timeout=60)
    print(f"\nShots saved to {outdir}")
    print("Review each PNG: nav present, no h-overflow, no overlaps, actions reachable.")


if __name__ == "__main__":
    main()
