import UIKit
import Capacitor

// NOTE (2026-10-22): This MUST extend CAPBridgeAppDelegate -- not the plain
// Xcode UIResponder/UIApplicationDelegate template that was here before.
// The bridge is what forwards Apple's push callbacks
// (didRegisterForRemoteNotificationsWithDeviceToken /
// didFailToRegisterForRemoteNotificationsWithError) to the PushNotifications
// plugin. With the plain template, Apple's reply had nowhere to go: the
// device token never reached the webview, the JS 'registration' event never
// fired, and push registration silently never completed on any build.
@UIApplicationMain
class AppDelegate: CAPBridgeAppDelegate {

}
