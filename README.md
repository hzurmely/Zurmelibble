# Zurmelibble

A simple Jibble style time tracking app. Runs on the web (GitHub Pages) and on Android (APK).

## Features

* Accounts with email and password
* Clock in, clock out and breaks, with a live timer
* GPS location saved on every clock in and clock out
* Admins see the whole team live, everyone's timesheets, and a map of clock in/out locations
* Admins can promote other people to admin
* Timesheet filters by person and date, plus CSV export

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
7. Open the app and create your account. Then, in Firestore, open `users → (your user)` and change `role` from `member` to `admin`. From then on you can make other admins from the Team tab.

## How people join

Each person installs the APK (or opens the web link) and creates an account. They show up in the Team tab for admins.
