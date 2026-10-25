"""Optional tray capabilities and Unix desktop host detection.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import importlib
import os
import sys
import time


def gtk_platform(platform=None):
	platform = sys.platform if platform is None else platform
	return platform.startswith(("linux", "freebsd"))


def tray_platform(platform=None):
	platform = sys.platform if platform is None else platform
	return platform in {"darwin", "win32"} or gtk_platform(platform)


def status_notifier_host():
	"""Require a registered visualization host, not just a watcher service."""
	try:
		from gi.repository import Gio, GLib
		bus = Gio.bus_get_sync(Gio.BusType.SESSION, None)
		reply = bus.call_sync("org.kde.StatusNotifierWatcher", "/StatusNotifierWatcher", "org.freedesktop.DBus.Properties", "Get",
			GLib.Variant("(ss)", ("org.kde.StatusNotifierWatcher", "IsStatusNotifierHostRegistered")), None, Gio.DBusCallFlags.NO_AUTO_START, 1000, None)
		value = reply.unpack()[0]
		return (value.unpack() if hasattr(value, "unpack") else value) is True
	except Exception:
		return False


def load_pystray():
	"""Choose menu-capable GTK backends; respect explicit user backend policy."""
	if not gtk_platform() or os.environ.get("PYSTRAY_BACKEND"):
		return importlib.import_module("pystray")
	# pystray 0.19.5 can raise ValueError when an AppIndicator typelib is absent,
	# rather than trying GTK. Select and retry explicitly in this private child.
	candidates = ("appindicator", "gtk") if status_notifier_host() else ("gtk",)
	original = os.environ.get("PYSTRAY_BACKEND")
	try:
		for backend in candidates:
			os.environ["PYSTRAY_BACKEND"] = backend
			try:
				return importlib.import_module("pystray")
			except Exception:
				continue
	finally:
		if original is None:
			os.environ.pop("PYSTRAY_BACKEND", None)
		else:
			os.environ["PYSTRAY_BACKEND"] = original
	raise ImportError("No menu-capable GTK tray backend is available.")


def tray_host_available(icon):
	if not icon.HAS_MENU:
		return False
	if not gtk_platform():
		return True
	# These backend handles are from the pinned pystray 0.19.5 implementation.
	status = getattr(icon, "_status_icon", None)
	if status is not None:
		return bool(status.is_embedded())
	if getattr(icon, "_appindicator", None) is not None:
		return status_notifier_host()
	return False


class HostWatch:
	"""Never signal readiness before a usable host; stop on later host loss."""
	def __init__(self, probe, emit, stop, clock=time.monotonic, timeout=5):
		self.probe, self.emit, self.stop, self.clock = probe, emit, stop, clock
		self.deadline = clock() + timeout
		self.ready = False
		self.ended = False

	def tick(self):
		if self.ended:
			return False
		try:
			available = self.probe()
		except Exception:
			available = False
		if available:
			if not self.ready:
				self.ready = True
				self.emit("ready")
			return True
		if self.ready or self.clock() >= self.deadline:
			self.ended = True
			try:
				self.emit("unavailable")
			finally:
				self.stop()
			return False
		return True
