#!/usr/bin/env python3
"""Idempotently provision or repair HAULTRA's isolated App Review tenant.

Required Render environment variables:
  APP_REVIEW_BOSS_USERNAME / APP_REVIEW_BOSS_PASSWORD
  APP_REVIEW_DRIVER_USERNAME / APP_REVIEW_DRIVER_PASSWORD
  APP_REVIEW_DELETE_USERNAME / APP_REVIEW_DELETE_PASSWORD

Credentials are never printed. The same repair also runs at app startup and
during scheduled maintenance, so the disposable deletion-test user returns
after a reviewer genuinely deletes it.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import app as haultra


def main():
    result = haultra.verify_app_review_demo(repair=True)
    if not result["ready"]:
        categories = ", ".join(result["missing"]) or "unknown"
        raise SystemExit(f"App Review demo is not ready: {categories}")
    print("App Review demo tenant is ready.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
