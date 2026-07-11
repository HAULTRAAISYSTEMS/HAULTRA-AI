// service-worker.js — FCM push notification handler
// This file MUST be served from the root of the domain for FCM to work.
// In Flask, add a route: @app.route('/service-worker.js') -> send_from_directory('static', 'service-worker.js')

importScripts('https://www.gstatic.com/firebasejs/10.12.0/firebase-app-compat.js');
importScripts('https://www.gstatic.com/firebasejs/10.12.0/firebase-messaging-compat.js');

// Firebase config must be duplicated here (service workers can't use ES modules)
firebase.initializeApp({
  apiKey: self.FIREBASE_API_KEY || "YOUR_API_KEY",
  authDomain: "YOUR_PROJECT_ID.firebaseapp.com",
  projectId: "YOUR_PROJECT_ID",
  storageBucket: "YOUR_PROJECT_ID.appspot.com",
  messagingSenderId: "YOUR_SENDER_ID",
  appId: "YOUR_APP_ID"
});

const messaging = firebase.messaging();

// Handle background push notifications
messaging.onBackgroundMessage((payload) => {
  console.log('[SW] Background message received:', payload);
  const { title, body, icon } = payload.notification || {};
  self.registration.showNotification(title || 'New Stop', {
    body: body || 'You have a new dispatch stop.',
    icon: icon || '/static/icon-192.png',
    badge: '/static/icon-192.png',
    tag: payload.data?.stopId || 'dispatch',
    data: payload.data,
    actions: [
      { action: 'view', title: 'View Stop' }
    ]
  });
});

// Handle notification click — open route.html
self.addEventListener('notificationclick', (event) => {
  event.notification.close();
  const url = '/static/route.html';
  event.waitUntil(
    clients.matchAll({ type: 'window', includeUncontrolled: true }).then((clientList) => {
      for (const client of clientList) {
        if (client.url.includes('route.html') && 'focus' in client) {
          return client.focus();
        }
      }
      return clients.openWindow(url);
    })
  );
});

// Offline cache for route.html and its assets
const CACHE_NAME = 'haultra-dispatch-v1';
const OFFLINE_ASSETS = ['/static/route.html', '/static/firebase-config.js'];

self.addEventListener('install', (event) => {
  event.waitUntil(
    caches.open(CACHE_NAME).then((cache) => cache.addAll(OFFLINE_ASSETS))
  );
  self.skipWaiting();
});

self.addEventListener('activate', (event) => {
  event.waitUntil(
    caches.keys().then((keys) =>
      Promise.all(keys.filter((k) => k !== CACHE_NAME).map((k) => caches.delete(k)))
    )
  );
  self.clients.claim();
});

self.addEventListener('fetch', (event) => {
  // Cache-first for offline assets
  if (OFFLINE_ASSETS.some((url) => event.request.url.includes(url))) {
    event.respondWith(
      caches.match(event.request).then((cached) => cached || fetch(event.request))
    );
  }
});
