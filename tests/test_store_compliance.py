"""Fast release-gate checks for the iOS and Android store wrappers."""

import importlib
import json
import os
import plistlib
import sys
import tempfile
from pathlib import Path
from xml.etree import ElementTree


ROOT = Path(__file__).resolve().parents[1]
TMP = tempfile.mkdtemp(prefix="haultra-store-test-")
os.environ["DATABASE_PATH"] = str(Path(TMP) / "store.db")
os.environ["SECRET_KEY"] = "store-compliance-test-only"
os.environ["UPLOAD_FOLDER"] = str(Path(TMP) / "uploads")
os.environ.pop("APPLE_TEAM_ID", None)
ANDROID_APP_SIGNING_SHA256 = (
    "6F:8A:46:AD:1B:0D:D8:E0:98:97:CE:82:47:81:E1:A9:"
    "C2:4C:D7:AF:65:37:35:C2:B9:59:33:D3:42:1F:10:D7"
)
os.environ["ANDROID_SHA256_FINGERPRINT"] = ANDROID_APP_SIGNING_SHA256
sys.path.insert(0, str(ROOT))

haultra = importlib.import_module("app")


def ok(condition, message):
    print(("PASS" if condition else "FAIL") + " - " + message)
    if not condition:
        raise SystemExit("FAILED: " + message)


config = json.loads((ROOT / "capacitor.config.json").read_text())
ok(config["appId"] == "com.rockkstaar.haultra", "Capacitor app ID is final")
ok(config["server"]["url"] == "https://haultra-systems.com", "native shell uses HTTPS production URL")
ok(config["server"]["cleartext"] is False, "Capacitor cleartext traffic is disabled")
ok(config["ios"]["appendUserAgent"] == "HaultraNativeApp", "iOS native marker configured")
ok(config["android"]["appendUserAgent"] == "HaultraNativeApp", "Android native marker configured")

with (ROOT / "ios/App/App/Info.plist").open("rb") as source:
    info = plistlib.load(source)
for key in (
    "NSCameraUsageDescription",
    "NSPhotoLibraryUsageDescription",
    "NSPhotoLibraryAddUsageDescription",
    "NSLocationWhenInUseUsageDescription",
):
    ok(bool(info.get(key)), f"iOS usage description present: {key}")
ok(info.get("ITSAppUsesNonExemptEncryption") is False, "iOS export-compliance flag present")
with (ROOT / "ios/App/App/App.entitlements").open("rb") as source:
    entitlements = plistlib.load(source)
ok("applinks:haultra-systems.com" in entitlements["com.apple.developer.associated-domains"],
   "iOS universal-link entitlement configured")

android_namespace = "{http://schemas.android.com/apk/res/android}"
manifest = ElementTree.parse(ROOT / "android/app/src/main/AndroidManifest.xml").getroot()
permissions = {
    node.attrib[f"{android_namespace}name"]
    for node in manifest.findall("uses-permission")
}
for permission in (
    "android.permission.INTERNET",
    "android.permission.CAMERA",
    "android.permission.ACCESS_COARSE_LOCATION",
    "android.permission.ACCESS_FINE_LOCATION",
):
    ok(permission in permissions, f"Android permission present: {permission}")
application = manifest.find("application")
ok(application.attrib[f"{android_namespace}allowBackup"] == "false", "Android app backup disabled")
ok(application.attrib[f"{android_namespace}usesCleartextTraffic"] == "false", "Android cleartext disabled")
app_links = [
    data
    for activity in application.findall("activity")
    for intent in activity.findall("intent-filter")
    if intent.attrib.get(f"{android_namespace}autoVerify") == "true"
    for data in intent.findall("data")
]
ok(any(
    data.attrib.get(f"{android_namespace}scheme") == "https"
    and data.attrib.get(f"{android_namespace}host") == "haultra-systems.com"
    for data in app_links
), "Android verified app link configured")

variables = (ROOT / "android/variables.gradle").read_text()
ok("minSdkVersion = 24" in variables, "Android minimum SDK is 24")
ok("compileSdkVersion = 36" in variables, "Android compile SDK is 36")
ok("targetSdkVersion = 36" in variables, "Android target SDK is 36")

app_source = (ROOT / "app.py").read_text()
ok("REPLACE_WITH_APPLE_TEAM_ID" not in app_source, "no Apple signing placeholder is published")
ok("REPLACE_WITH_ANDROID_SHA256_FINGERPRINT" not in app_source, "no Android signing placeholder is published")

haultra.app.config["TESTING"] = True
client = haultra.app.test_client()
native_headers = {"User-Agent": "HAULTRA Test HaultraNativeApp"}

login = client.get("/login", headers=native_headers)
ok(login.status_code == 200, "native login renders")
ok(b"/signup" not in login.data, "native login does not steer to registration")

registration = client.get("/register-company", headers=native_headers)
ok(registration.status_code == 302 and registration.headers["Location"].endswith("/login"),
   "native company registration is blocked")

ok(client.get("/.well-known/apple-app-site-association").status_code == 404,
   "unsigned Apple association data fails closed")
android_links = client.get("/.well-known/assetlinks.json")
ok(android_links.status_code == 200, "signed Android association data is published")
android_target = android_links.get_json()[0]["target"]
ok(android_target["package_name"] == "com.rockkstaar.haultra",
   "Android association uses the release package name")
ok(android_target["sha256_cert_fingerprints"] == [ANDROID_APP_SIGNING_SHA256],
   "Android association uses the Play app-signing SHA-256 fingerprint")

# ---- Guideline 3.1.1: no unauthenticated route reaches a purchase surface ----
# The purchase surfaces are "/" (marketing, carries pricing) and
# /register-company ("Start Free Trial"). Both are hidden from the native
# shells by is_native_app(), but that is User-Agent sniffing and fails open,
# so the checks below assert the session-keyed behaviour that does not.
web_headers = {"User-Agent": "Mozilla/5.0 (Macintosh) Chrome/120"}

for label, headers in (("native", native_headers), ("web", web_headers)):
    blocked = client.get("/subscription/blocked", headers=headers)
    ok(blocked.status_code == 302 and blocked.headers["Location"].endswith("/login"),
       f"{label}: /subscription/blocked requires a session")

    missing = client.get("/no-such-page-exists", headers=headers)
    ok(missing.status_code == 404, f"{label}: unknown path still 404s")
    ok(b'href="/login"' in missing.data,
       f"{label}: signed-out 404 sends you to login")
    ok(b'href="/">' not in missing.data,
       f"{label}: signed-out 404 does not link to the marketing site")

for path in ("/login", "/forgot-password", "/privacy", "/terms", "/support",
             "/offline", "/order", "/delete-account", "/no-such-page-exists"):
    page = client.get(path, headers=native_headers)
    if page.status_code != 200:
        continue
    ok(b'href="/"' not in page.data and b'href="/register-company"' not in page.data,
       f"native signed-out {path} links to no purchase surface")

print("\nALL STORE COMPLIANCE TESTS PASSED")
