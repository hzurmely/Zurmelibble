# Zurmelibble

A simple Jibble style time tracking app. Runs on the web (GitHub Pages) and on Android (APK).

## Features

* Accounts with email and password (with a show password button)
* Organisations: anyone can create one; people join with an invite code or link
* Optional "require approval" so admins approve new people first
* Teams inside each organisation
* Roles: Owner, Admin, Manager (sees their own team), Member (sees only themselves)
* Switch between several organisations from the header
* Clock in, clock out and breaks, with a live timer
* GPS location saved on every clock in and clock out, shown on a map
* Timesheets filtered by team, person and date, plus CSV export
* Organisation branding: the CEFAST Aerospace organisation uses its own design system (`brands/cefast/`), switched on by setting `brand: "cefast"` on the organisation in Firestore

## Links

* Web app: https://hzurmely.github.io/Zurmelibble/
* Android APK: see the latest release on the [Releases page](../../releases/latest). A new APK is built automatically on every push to `main`.

## Firebase setup (one time)

1. Go to https://console.firebase.google.com and create a project.
2. **Build → Authentication → Get started → Email/Password → Enable.**
3. **Build → Firestore Database → Create database** (production mode, any region).
4. In Firestore, open the **Rules** tab, paste the contents of `firestore.rules`, and publish.
5. **Project settings → Your apps → Web (</>)**, register an app, and copy the config into `firebase-config.js`.
6. **Authentication → Settings → Authorized domains**: add `hzurmely.github.io` (`localhost` is already there, which the APK uses).
7. Open the app, create your account, then create your organisation. You become its Owner.

## How people join

In **Settings**, copy the invite message and send it. People install the APK (or open the link), create an account and enter the code. Put them in a team and pick their role in the **People** tab.
