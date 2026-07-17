import type { CapacitorConfig } from '@capacitor/cli';

// Remote-URL wrapper: the app always loads the live site. There is no bundled
// web build to keep in sync — `webDir` below just needs to exist for the
// Capacitor CLI's copy step; its contents are never shown to users because
// `server.url` takes over immediately on launch. See STORE_LAUNCH.md.
const config: CapacitorConfig = {
  appId: 'com.rockkstaar.haultra',
  appName: 'HAULTRA',
  webDir: 'www',
  server: {
    url: 'https://haultra-systems.com',
    cleartext: false,
  },
  plugins: {
    SplashScreen: {
      launchShowDuration: 1200,
      launchAutoHide: true,
      backgroundColor: '#121212',
      androidScaleType: 'CENTER_CROP',
      showSpinner: false,
      splashFullScreen: true,
      splashImmersive: true,
    },
    StatusBar: {
      // Dark charcoal app background -> light (white) status bar icons/text.
      style: 'LIGHT',
      backgroundColor: '#121212',
      overlaysWebView: false,
    },
  },
  ios: {
    contentInset: 'automatic',
    backgroundColor: '#121212',
  },
  android: {
    backgroundColor: '#121212',
  },
};

export default config;
