"""Cab View photo capture must actually upload, and must not fail silently.

The native Add Photo path used resultType 'uri' and then fetch(photo.webPath).
capacitor.config.json points the shell at https://haultra-systems.com, so the
page origin is the remote site while webPath is a capacitor://localhost/... URL
— that fetch is cross-scheme, always rejects, and landed in a catch that only
restored the button. No error, no upload: the driver tapped Add Photo and the
photo simply never saved.

It now takes base64 straight from the plugin and builds the Blob in JS, so no
cross-origin read is involved. The POST result is also checked: reloading on a
failed upload wiped the pending photo and looked exactly like success.

Covered here:
  * every inline script on the Cab View page parses (the upload path is built
    inside an f-string, where one stray brace breaks the whole page)
  * the native path reads base64 and never fetches webPath
  * a failed POST does not reload
  * the upload endpoint really persists a JPEG posted as a Blob would be, and
    the file lands on disk
"""

import os
import re
import subprocess
import sys
import tempfile
from io import BytesIO
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TMP = tempfile.TemporaryDirectory()
os.environ["DATABASE_PATH"] = str(Path(TMP.name) / "photo.db")
os.environ["UPLOAD_FOLDER"] = str(Path(TMP.name) / "uploads")
os.environ["SECRET_KEY"] = "cab-photo-upload-test"
os.environ["FLASK_ENV"] = "testing"
os.environ["APP_REVIEW_BOSS_USERNAME"] = "review-boss"
os.environ["APP_REVIEW_BOSS_PASSWORD"] = "ReviewBossPassword!1"
os.environ["APP_REVIEW_DRIVER_USERNAME"] = "review-driver"
os.environ["APP_REVIEW_DRIVER_PASSWORD"] = "ReviewDriverPassword!1"
os.environ["APP_REVIEW_DELETE_USERNAME"] = "review-delete"
os.environ["APP_REVIEW_DELETE_PASSWORD"] = "ReviewDeletePassword!1"
sys.path.insert(0, str(ROOT))

import app as haultra  # noqa: E402

haultra.app.config["TESTING"] = True

failures = []


def ok(condition, message):
    print(("PASS" if condition else "FAIL") + " - " + message)
    if not condition:
        failures.append(message)


def csrf_from(response):
    match = re.search(rb'<meta name="csrf-token" content="([^"]+)"', response.data)
    if not match:
        raise AssertionError("CSRF token missing")
    return match.group(1).decode()


with haultra.app.app_context():
    status = haultra.verify_app_review_demo(repair=True)
ok(status["ready"], "App Review demo tenant seeded")

with haultra.app.app_context():
    conn = haultra.get_db()
    company_id = conn.execute(
        "SELECT id FROM companies WHERE slug=?", (haultra.APP_REVIEW_DEMO_SLUG,)
    ).fetchone()["id"]
    route = conn.execute(
        "SELECT id FROM routes WHERE company_id=? AND status='open' ORDER BY id LIMIT 1",
        (company_id,),
    ).fetchone()
    stop = conn.execute(
        "SELECT id FROM stops WHERE route_id=? ORDER BY stop_order LIMIT 1",
        (route["id"],),
    ).fetchone()
route_id, stop_id = route["id"], stop["id"]

client = haultra.app.test_client()
page = client.get("/login")
client.post(
    "/login",
    data={
        "_csrf_token": csrf_from(page),
        "username": os.environ["APP_REVIEW_DRIVER_USERNAME"],
        "password": os.environ["APP_REVIEW_DRIVER_PASSWORD"],
    },
    follow_redirects=True,
)

cab = client.get(f"/cab/{route_id}", follow_redirects=True)
if cab.status_code != 200:
    cab = client.get(f"/driver/route/{route_id}", follow_redirects=True)
ok(cab.status_code == 200, f"Cab View loads for the driver ({cab.status_code})")

# An 'open' route renders the pre-flight card, which has no photo widget.
# Start it so the running Cab View — the screen with Add Photo — is what we
# assert against.
started = client.post(
    f"/route/{route_id}/start",
    data={"_csrf_token": csrf_from(cab)},
    follow_redirects=True,
)
if started.status_code != 200 or "triggerAddPhoto" not in started.data.decode("utf-8", "replace"):
    with haultra.app.app_context():
        conn = haultra.get_db()
        conn.execute("UPDATE routes SET status='in_progress' WHERE id=?", (route_id,))
        conn.commit()
    started = client.get(f"/cab/{route_id}", follow_redirects=True)
cab = started
ok(cab.status_code == 200, f"running Cab View loads ({cab.status_code})")
html = cab.data.decode("utf-8", "replace")

# ── The page's inline scripts must parse ──────────────────────────────────
scripts = re.findall(r"<script(?![^>]*\bsrc=)[^>]*>(.*?)</script>", html, re.S)
ok(bool(scripts), f"Cab View carries inline scripts ({len(scripts)})")
bad = []
for index, source in enumerate(scripts):
    if not source.strip():
        continue
    with tempfile.NamedTemporaryFile("w", suffix=".js", delete=False, encoding="utf-8") as handle:
        handle.write(source)
        temp = handle.name
    result = subprocess.run(["node", "--check", temp], capture_output=True, text=True)
    os.unlink(temp)
    if result.returncode != 0:
        bad.append((index, result.stderr.strip().splitlines()[:2]))
ok(not bad, f"every inline script parses{'' if not bad else f' — broken: {bad}'}")
ok("{{" not in html and "}}" not in html, "no unconsumed f-string braces rendered")

# ── The native path must not round-trip through webPath ───────────────────
ok("triggerAddPhoto" in html, "the native Add Photo entry point is present")
ok("resultType: 'base64'" in html, "camera returns base64, not a capacitor:// uri")
ok(
    "fetch(photo.webPath)" not in html,
    "no cross-origin fetch of photo.webPath (the bug: it always rejected)",
)
ok("atob(photo.base64String)" in html, "the blob is built from base64 in the page")
ok(
    "width: 1600" in html,
    "capture is downscaled before encoding — a full-resolution photo took "
    "~45s to upload from a truck",
)
upload_call = html[html.find("triggerAddPhoto"):]
upload_call = upload_call[:upload_call.find("</script>")]
ok("if (!r.ok) throw" in upload_call, "a failed POST raises instead of reloading")
ok(
    upload_call.find("if (!r.ok) throw") < upload_call.find("window.location.reload"),
    "the ok-check runs before the reload, not after",
)

# ── The endpoint must really persist the photo ────────────────────────────
from PIL import Image  # noqa: E402

buffer = BytesIO()
Image.new("RGB", (48, 32), (255, 107, 26)).save(buffer, format="JPEG")
buffer.seek(0)

with haultra.app.app_context():
    before = haultra.get_db().execute(
        "SELECT COUNT(*) n FROM route_photos WHERE stop_id=?", (stop_id,)
    ).fetchone()["n"]

posted = client.post(
    f"/stop/{stop_id}/upload",
    data={
        "_csrf_token": csrf_from(cab),
        # Exactly what the page sends: a Blob named photo.jpeg.
        "photos": (buffer, "photo.jpeg", "image/jpeg"),
    },
    content_type="multipart/form-data",
    follow_redirects=True,
)
ok(posted.status_code == 200, f"uploading photo.jpeg returns 200 ({posted.status_code})")

with haultra.app.app_context():
    rows = haultra.get_db().execute(
        "SELECT file_path FROM route_photos WHERE stop_id=? ORDER BY id", (stop_id,)
    ).fetchall()
ok(len(rows) == before + 1, f"a route_photos row was written ({before} -> {len(rows)})")

if rows:
    stored = rows[-1]["file_path"]
    ok(stored.startswith(os.path.join("static", "uploads")),
       f"the stored path is web-relative ({stored})")
    on_disk = Path(os.environ["UPLOAD_FOLDER"]) / Path(stored).name
    ok(on_disk.exists(), "the file actually landed on disk")
    ok(on_disk.exists() and on_disk.stat().st_size > 0, "and it is not empty")

# jpeg must be an accepted extension — the native path names every file
# photo.<format>, and Capacitor reports jpeg.
ok("jpeg" in haultra.ALLOWED_EXTENSIONS, "jpeg is an allowed upload extension")

if failures:
    raise SystemExit("FAILED: " + "; ".join(failures))

print("\nALL CAB PHOTO UPLOAD TESTS PASSED")
