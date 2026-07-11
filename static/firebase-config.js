// firebase-config.js
// TODO: Replace these placeholder values with your actual Firebase project config.
// Get them from: Firebase Console → Project Settings → Your Apps → Web App → Config

export const firebaseConfig = {
  apiKey: "YOUR_API_KEY",
  authDomain: "YOUR_PROJECT_ID.firebaseapp.com",
  projectId: "YOUR_PROJECT_ID",
  storageBucket: "YOUR_PROJECT_ID.appspot.com",
  messagingSenderId: "YOUR_SENDER_ID",
  appId: "YOUR_APP_ID",
  measurementId: "YOUR_MEASUREMENT_ID"
};

// Your VAPID key for FCM Web Push
// Get from: Firebase Console → Project Settings → Cloud Messaging → Web Push Certificates
export const VAPID_KEY = "YOUR_VAPID_KEY";

// Your company ID in Firestore (set after creating the company document)
// This is a fixed value per deployment — one company per hosted instance
export const COMPANY_ID = "YOUR_COMPANY_ID";
