# HAULTRA — iOS & Android Store Launch

This wraps the live web app at **https://haultra-systems.com** in
[Capacitor](https://capacitorjs.com) as a **remote-URL wrapper**: the native
shell always loads the live site. There is no bundled web build to keep in
sync — ship a change to the Flask app on Render and every installed copy of
the app picks it up on next launch, with no store resubmission.

> **Important — read before you start:** none of the commands in this
> document have been run. The environment that authored this file has no
> Node.js/npm, no full Xcode.app (only Command Line Tools), and no Android
> SDK, so the Capacitor CLI could not be executed and neither platform could
> be built or verified here. Everything below is precise, standard Capacitor
> tooling, but you are the first one actually running it. Go step by step
> and don't skip the verification points.

---

## 0. What's already in the repo

| File | Purpose |
|---|---|
| `package.json` | Capacitor core + plugins (`@capacitor/camera`, `@capacitor/geolocation`, `@capacitor/app`) |
| `capacitor.config.ts` | `appId`, `appName`, `server.url`, status bar / splash screen config |
| `www/index.html` | Placeholder only — never shown; `server.url` overrides it. Required by the CLI's copy step. |
| `static/icon-source-1024.png` | 1024×1024 square icon source, generated from `static/logo.png` |
| `static/splash-source-2732.png` | 2732×2732 splash source (wordmark on `#121212`), generated from `static/logo.png` |
| `app.py` — Add Photo flow | Detects the native Camera plugin at runtime; falls back to the existing HTML file input on web (unchanged) |
| `app.py` — `/.well-known/apple-app-site-association`, `/.well-known/assetlinks.json` | Deep-link verification files, **placeholder values** — see §6 |

### ⚠️ Two things to decide before you go further

1. **`appId`**: set to `com.rockkstaar.haultra` in `capacitor.config.ts`,
   reverse-DNS style from the "Rockkstaar" name already used elsewhere in
   your projects (e.g. `rockkstaar-trade-assistant`). I don't have your
   actual registered Apple Developer / Google Play account or LLC filing on
   hand to confirm this is the exact legal/brand name you want permanently
   locked into both app stores — **confirm it before your first real build**,
   since changing `appId` after either store listing exists effectively
   means creating a new app.
2. **Icon/splash color**: `static/logo.png` — the only image asset in this
   repo — is cyan/blue ("HAULTRA AI SYSTEMS," teal ring). The in-app product
   itself is themed orange (`#FF6B1A`) with teal reserved strictly for
   AI-touched UI elements. I generated `icon-source-1024.png` and
   `splash-source-2732.png` directly from this existing asset because that's
   what was asked for and it's the only asset that exists, but it does not
   match the app's current brand color. Get a proper on-brand icon from a
   designer before you actually submit to either store — swapping the source
   file and re-running the asset generator in §2 takes two minutes once you
   have it.

---

## 1. Install

```bash
# from the repo root
npm install
```

Requires Node.js 18+ and npm. If you don't have Node installed:
`brew install node` (macOS) or download from nodejs.org.

## 2. Generate icons and splash screens

```bash
npx capacitor-assets generate \
  --iconBackgroundColor '#121212' \
  --iconBackgroundColorDark '#121212' \
  --splashBackgroundColor '#121212' \
  --splashBackgroundColorDark '#121212'
```

`@capacitor/assets` (already in `devDependencies`) reads
`static/icon-source-1024.png` and `static/splash-source-2732.png` **only if
you point it at them** — by default it looks for `assets/icon.png` and
`assets/splash.png` in the repo root. Either:

- move/copy the two files: `mkdir assets && cp static/icon-source-1024.png assets/icon.png && cp static/splash-source-2732.png assets/splash.png`, then run the command above with no extra flags, **or**
- pass `--iconSource static/icon-source-1024.png --splashSource static/splash-source-2732.png` explicitly.

This produces every required iOS (20pt–1024pt @1x/2x/3x, all idioms) and
Android (mdpi–xxxhdpi, adaptive icon layers) size automatically — you do not
need to hand-export a size table.

## 3. Generate the native projects

```bash
npx cap add ios
npx cap add android
npx cap sync
```

`cap add` creates `ios/` and `android/` from Capacitor's official templates
and copies in the config from `capacitor.config.ts` (appId, appName, status
bar, splash). `cap sync` copies `www/`, installs/links the plugins declared
in `package.json` (Camera, Geolocation, App), and re-copies config on every
future run — **re-run `npx cap sync` any time you edit `capacitor.config.ts`
or change plugins.**

Commit `ios/` and `android/` to git once generated — unlike `node_modules/`,
Capacitor's native projects are meant to be version-controlled (they can
carry manual native config/entitlements you don't want to regenerate from
scratch).

## 4. iOS — Xcode

```bash
npx cap open ios
```

In Xcode, with the top-level `App` target selected → **Signing & Capabilities**:

1. Check **Automatically manage signing**.
2. **Team**: select your Apple Developer team (requires an active
   [Apple Developer Program](https://developer.apple.com/programs/)
   membership, $99/yr — this is on you to enroll, I can't do it for you).
3. Confirm **Bundle Identifier** reads `com.rockkstaar.haultra` (matches
   `capacitor.config.ts`; if you change one, change both and re-run `cap sync`).
4. Status bar and splash are already wired via `capacitor.config.ts` —
   confirm the splash preview in Xcode's `App/App/Assets.xcassets` shows the
   dark wordmark, not a blank/white screen.
5. **Deep linking** (optional, see §6): add the **Associated Domains**
   capability, entry `applinks:haultra-systems.com`.

**Build → Run** on a simulator first (Product → Run, or ⌘R) to confirm it
launches and loads `haultra-systems.com`. For a real device you need it
registered to your provisioning profile (Xcode does this automatically with
a connected device and automatic signing).

**Release build / App Store submission:**
- Product → Archive (only enabled on a real "Any iOS Device" or connected
  device destination, not a simulator).
- Once archived, **Distribute App → App Store Connect → Upload**.
- You'll need an [App Store Connect](https://appstoreconnect.apple.com)
  listing created first (App Store Connect → My Apps → +) with the same
  bundle ID, screenshots, description, privacy policy URL (you already have
  one at `/privacy`), and a completed **App Privacy** questionnaire —
  this app requests Camera and Location, both must be declared there, and
  the `NSCameraUsageDescription` / `NSLocationWhenInUseUsageDescription`
  strings Capacitor's Camera/Geolocation plugins add to `Info.plist` should
  match what you declare.

## 5. Android — Android Studio

```bash
npx cap open android
```

1. Let Gradle sync finish (first run downloads dependencies — can take a
   few minutes).
2. Build → **Generate Signed Bundle / APK** → Android App Bundle (`.aab`,
   what Play Store wants).
3. If you don't have a release keystore yet, Android Studio's wizard has a
   **Create new...** option — do this once, then **keep that `.jks` file and
   its passwords somewhere safe outside this repo**. Losing it means you can
   never update the app under the same listing again.
4. Status bar/splash: same as iOS, already wired via `capacitor.config.ts` —
   run on an emulator first to confirm the launch screen looks right.

**Play Store submission:**
- Create the app in [Play Console](https://play.google.com/console)
  (package name must match `com.rockkstaar.haultra`).
- Complete the **Data safety** section — same Camera/Location declaration
  as iOS. Capacitor's Android manifest additions for these plugins are
  handled automatically by `cap sync`; you don't need to hand-edit
  `AndroidManifest.xml` for the permissions themselves.
- Upload the signed `.aab` under Production (or an internal testing track
  first, which is worth doing before a public release).

## 6. Deep linking (haultra-systems.com links open the app)

`@capacitor/app` is installed, and the two verification files it needs are
already served by the backend with placeholder values:

- `https://haultra-systems.com/.well-known/apple-app-site-association`
- `https://haultra-systems.com/.well-known/assetlinks.json`

To make them real:

**iOS** — open `app.py`, find `apple_app_site_association()`, replace
`REPLACE_WITH_APPLE_TEAM_ID` with your 10-character Team ID (Apple Developer
account → Membership details, or top-right of the Xcode signing pane). Then
in Xcode add the **Associated Domains** capability (§4.5) with
`applinks:haultra-systems.com`.

**Android** — open `app.py`, find `android_asset_links()`, replace
`REPLACE_WITH_ANDROID_SHA256_FINGERPRINT` with your release keystore's
SHA-256 fingerprint:

```bash
keytool -list -v -keystore your-release-key.jks -alias your-key-alias
```

(the `SHA256:` line in that output — colons and all). Then add an intent
filter for `haultra-systems.com` with `android:autoVerify="true"` in
`android/app/src/main/AndroidManifest.xml`'s main activity — Capacitor's
Android template has a commented example of this block already.

Deploy the `app.py` change, then re-run each platform's association-file
checker (Xcode re-validates on next Associated Domains build; Android:
`adb shell pm get-app-links com.rockkstaar.haultra`) to confirm.

## 7. Verify — checklist

Run through this on both platforms before considering either "done":

- [ ] `npm install` completes with no errors
- [ ] `npx cap add ios` / `npx cap add android` complete, `ios/` and `android/` exist
- [ ] `npx capacitor-assets generate` produces icon sets in `ios/App/App/Assets.xcassets` and `android/app/src/main/res`
- [ ] App launches in the iOS simulator and Android emulator, loads haultra-systems.com, status bar and splash match the dark theme
- [ ] Log in as a driver, open Cab View, tap **Add Photo** — native camera sheet opens (not a file picker), photo uploads and appears in the gallery
- [ ] Complete a stop with location permission granted — confirm in Bin Tracker that the pin shows "✓ GPS" (see `feat/gps-stamp`)
- [ ] iOS: Xcode archive succeeds; Android: signed `.aab` builds successfully
- [ ] Deep link test (after §6): tapping a `haultra-systems.com` link from Messages/Mail opens the app, not a browser tab

## 8. What I could not do here

- Run any command above — no Node/npm in this environment.
- Generate the actual `ios/`/`android/` project directories — same reason,
  plus no Xcode.app or Android SDK to have opened/built them even with Node.
- Confirm the icons/splash render correctly inside a real Xcode/Android
  Studio preview.
- Enroll you in the Apple Developer Program or create your Android
  keystore — both require your own accounts/credentials.
