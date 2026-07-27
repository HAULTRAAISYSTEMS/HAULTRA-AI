# HAULTRA App Store and Google Play Release

HAULTRA has native Capacitor 8 projects for iOS and Android. Both use the
production service at `https://haultra-systems.com` and identify native
requests with the `HaultraNativeApp` user-agent suffix.

## Release identifiers and requirements

| Setting | Value |
|---|---|
| App name | HAULTRA |
| Bundle/package ID | `com.rockkstaar.haultra` |
| iOS deployment target | 15.0 |
| Android minimum SDK | 24 |
| Android compile/target SDK | 36 |
| Privacy policy | `https://haultra-systems.com/privacy` |
| Terms | `https://haultra-systems.com/terms` |
| Account deletion | Available in Settings and at `https://haultra-systems.com/delete-account` |

Use Node 22 or newer. Capacitor 8 also requires Xcode 26+ for iOS and an
Android SDK containing API 36 for Android.

## Before every release

```bash
npm ci
npx cap sync
python tests/test_store_compliance.py
```

Then test login, camera/photo upload, location capture, route dispatch,
notifications if enabled, logout, and account deletion on real iOS and
Android devices. Confirm that the native app never shows registration,
pricing, checkout, or a link telling users to purchase on the website.

## App Review account

Set production-only credentials and run the idempotent seed command:

```bash
export APP_REVIEW_USERNAME='apple-review'
export APP_REVIEW_PASSWORD='use-a-unique-strong-password'
python scripts/create_app_review_account.py
```

Add the username and password to App Store Connect under **App Review
Information → Sign-in required**. The account includes an active Pro sample
company, a dispatcher/owner view, a driver account, and sample route data.
Never commit the password.

## iOS

Open `ios/App/App.xcworkspace` in Xcode:

1. Select the App target and your Apple Developer Team.
2. Keep automatic signing enabled and confirm bundle ID
   `com.rockkstaar.haultra`.
3. Add the Associated Domains capability with
   `applinks:haultra-systems.com` if deep links are enabled.
4. Set `APPLE_TEAM_ID` in the production service. Until it is present, the
   association endpoint deliberately returns 404 instead of publishing an
   invalid identity.
5. Set the marketing version/build number, select **Any iOS Device**, then
   **Product → Archive** and upload through Organizer.

The required Camera, Photo Library, and Location usage descriptions are in
`ios/App/App/Info.plist`. Export-compliance metadata declares that the app
does not use non-exempt encryption.

## Android / Google Play

The Android project already targets API 36. Build versions are supplied as
Gradle properties:

```bash
./android/gradlew -p android bundleRelease \
  -PHAULTRA_VERSION_CODE=1 \
  -PHAULTRA_VERSION_NAME=1.0.0
```

For a signed upload bundle, keep the keystore outside this repository and
provide these environment variables:

```bash
export HAULTRA_UPLOAD_STORE_FILE='/absolute/path/haultra-upload.jks'
export HAULTRA_UPLOAD_STORE_PASSWORD='...'
export HAULTRA_UPLOAD_KEY_ALIAS='haultra-upload'
export HAULTRA_UPLOAD_KEY_PASSWORD='...'
```

Run the same `bundleRelease` command. The `.aab` is written below
`android/app/build/outputs/bundle/release/`. Enroll the app in Play App
Signing and retain a secure backup of the upload key.

Set `ANDROID_SHA256_FINGERPRINT` in the production service to the SHA-256
certificate fingerprint used by installed Play builds. Use the **app
signing certificate** fingerprint from Play Console, not merely the local
upload-key fingerprint. The app-link endpoint returns 404 until configured.

## Production service gates

Before submitting either binary:

- merge the release pull request and require all GitHub production-readiness
  checks to pass
- configure `APPLE_TEAM_ID` and `ANDROID_SHA256_FINGERPRINT`, then verify both
  `/.well-known/` association endpoints return HTTP 200
- configure `BACKUP_S3_BUCKET` and AWS-compatible credentials, run a manual
  backup, and complete a restore drill
- confirm `/health` returns HTTP 200 and reports both database and storage as
  healthy
- run `scripts/purge_deleted_accounts.py` once and confirm no overdue deletion
  jobs remain

## Store listing checklist

- 1024×1024 iOS icon and Google Play 512×512 icon
- iPhone/iPad screenshots for every supported App Store device class
- Phone/tablet screenshots and 1024×500 feature graphic for Google Play
- Category, description, support contact, privacy-policy URL, and copyright
- App Store App Privacy answers and Google Play Data Safety answers
- Content rating, target audience, ads declaration, and access instructions
- App Review / Play review credentials tested immediately before submission
- Account-deletion URL entered in Play Console
- Camera and precise/approximate location use explained in review notes
- No checkout or purchase steering visible in native sessions

## Data-disclosure working inventory

Verify this against actual production configuration before submission:

- Account identifiers and contact data: account operation and support
- Company, driver, customer, route, stop, and service data: core app function
- Camera/photos: user-initiated documentation and proof of service
- Precise or approximate location: user-initiated service/GPS stamps
- Device/network diagnostics and server logs: security and reliability
- Payment data: processed by Stripe on the web; not collected in the native app

Declare whether each category is collected, linked to identity, retained,
shared with service providers, and deletable. Store forms must describe the
production behavior, including backend and third-party processing—not only
what the native binary contains.

## Known submission risk

Both binaries present a hosted web product inside a native shell. The native
camera, location, deep-link, secure-session, and mobile workflow integration
help, but Apple can still reject a wrapper under guideline 4.2 if reviewers
do not see enough app-like value. In review notes, direct the reviewer to the
driver photo/GPS workflow and the dispatcher-to-driver operational flow.
