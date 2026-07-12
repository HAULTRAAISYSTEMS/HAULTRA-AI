// service-worker.js — FCM push notification handler
// This file MUST be served from the root of the domain for FCM to work.
// In Flask, add a route: @app.route('/service-worker.js') -> send_from_directory('static', 'service-worker.js')

importScripts('https://www.gstatic.com/firebasejs/10.12.0/firebase-app-compat.js');
importScripts('https://www.gstatic.com/firebasejs/10.12.0/firebase-messaging-compat.js');

// Firebase config must be duplicated here (service workers can't use ES modules)
firebase.initializeApp({
  apiKey: "AIzaSyBAWm08bVHH5uia21H5VPd1mAW0Ei0MnV4",
  authDomain: "haultra-dispatch.firebaseapp.com",
  projectId: "haultra-dispatch",
  storageBucket: "haultra-dispatch.firebasestorage.app",
  messagingSenderId: "66096047367",
  appId: "1:66096047367:web:a7a3da473ba9d0bf5b51a2"
});

const messaging = firebase.messaging();

// Handle background FCM messages (when app is not in foreground)
messaging.onBackgroundMessage((payload) => {
  console.log('[SW] Background message received:', payload);

  const { title, body, stopId } = payload.data || {};
  const notifTitle = title || 'New Stop Assigned';
  const notifBody = body || 'You have a new stop. Tap to view.';

  self.registration.showNotification(notifTitle, {
    body: notifBody,
    icon: '/static/icons/icon-192.png',
    badge: '/static/icons/badge-72.png',
    tag: stopId || 'haultra-stop',
    data: { stopId }
  });
});

// Handle notification click — open/focus route.html
self.addEventListener('notificationclick', (event) => {
  event.notification.close();
  const stopId = event.notification.data?.stopId;
  const url = '/route' + (stopId ? '?stop=' + stopId : '');

  event.waitUntil(
    clients.matchAll({ type: 'window', includeUncontrolled: true }).then((clientList) => {
      for (const client of clientList) {
        if (client.url.includes('/route') && 'focus' in client) {
          return client.focus();
        }
      }
      if (clients.openWindow) return clients.openWindow(url);
    })
  );
});

// Offline cache — cache-first for critical assets
const CACHE_NAME = 'haultra-v1';
const PRECACHE = [
  '/route',
  '/static/firebase-config.js'
];

self.addEventListener('install', (event) => {
  event.waitUntil(
    caches.open(CACHE_NAME).then((cache) => cache.addAll(PRECACHE))
  );
  self.skipWaiting();
});

self.addEventListener('activate', (event) => {
  event.waitUntil(
    caches.keys().then((keys) =>
      Promise.all(keys.filter(k => k !== CACHE_NAME).map(k => caches.delete(k)))
    )
  );
  self.clients.claim();
});

self.addEventListener('fetch', (event) => {
  if (event.request.method !== 'GET') return;
  const url = new URL(event.request.url);
  if (PRECACHE.some(p => url.pathname === p || url.pathname.startsWith(p))) {
    event.respondWith(
      caches.match(event.request).then((cached) => cached || fetch(event.request))
    );
  }
});
