#!/usr/bin/env python3
"""Run HAULTRA's due account/company deletion maintenance immediately."""

import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from app import init_db, purge_due_deletions


if __name__ == "__main__":
    if not os.environ.get("DATABASE_PATH", "").strip():
        raise SystemExit("DATABASE_PATH must be set")
    init_db()
    result = purge_due_deletions()
    print(
        "Deletion maintenance complete: "
        f"{result['purged_companies']} companies purged, "
        f"{result['anonymized_users']} users anonymized."
    )
