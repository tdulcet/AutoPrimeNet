#!/usr/bin/env python3
"""Private native tray helper; communicate menu events over stdout.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import importlib
import json
import os
import sys
import threading
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


def emit(event):
	print(json.dumps({"event": event}), flush=True)


def main():
	if not tray_platform():
		emit("unavailable")
		return 1
	try:
		pystray = load_pystray()
		if not pystray.Icon.HAS_MENU:
			emit("unavailable")
			return 1
		from PIL import Image, ImageDraw

		image = Image.new("RGBA", (64, 64), (0, 0, 0, 0))
		draw = ImageDraw.Draw(image)
		draw.ellipse((6, 6, 58, 58), fill=(35, 97, 155, 255))
		draw.line((20, 44, 32, 19, 44, 44), fill="white", width=5)
		draw.line((25, 35, 39, 35), fill="white", width=4)
		state = ["Stopped"]
		icon = pystray.Icon(
			"autoprimenet-gui", image, "AutoPrimeNet GUI",
			menu=pystray.Menu(
				pystray.MenuItem("Open AutoPrimeNet GUI", lambda *_: emit("open"), default=True),
				pystray.MenuItem(lambda _item: "Scheduled monitoring: " + state[0], None, enabled=False),
				pystray.MenuItem("Start monitoring…", lambda *_: emit("start"), enabled=lambda _item: state[0] in {"Stopped", "Failed"}),
				pystray.MenuItem("Stop monitoring", lambda *_: emit("stop"), enabled=lambda _item: state[0] in {"Starting", "Running cycle", "Waiting", "Watching files"}),
				pystray.Menu.SEPARATOR,
				pystray.MenuItem("Quit AutoPrimeNet GUI", lambda *_: emit("quit")),
			),
		)
		stopping = threading.Event()
		control = os.fdopen(sys.stdin.fileno(), "rb", buffering=0, closefd=False)

		def on_native_thread(function):
			if sys.platform == "darwin":
				from PyObjCTools import AppHelper
				AppHelper.callAfter(function)
			elif gtk_platform():
				from gi.repository import GLib
				def call():
					function()
					return False
				GLib.idle_add(call)
			else:
				function()

		def wait_for_parent():
			# EOF is the shutdown signal. A crashed GUI also closes this pipe, so
			# an orphan menu-bar helper does not remain indefinitely.
			while line := control.readline(8193):
				if len(line) > 8192:
					continue
				try:
					message = json.loads(line)
					if isinstance(message.get("state"), str) and message["state"] in {"Stopped", "Starting", "Running cycle", "Waiting", "Watching files", "Stopping", "Failed"}:
						state[0] = message["state"]
						on_native_thread(icon.update_menu)
				except (ValueError, AttributeError):
					continue
			stopping.set()
			on_native_thread(icon.stop)

		def setup(tray):
			def activate():
				if stopping.is_set():
					tray.stop()
					return
				try:
					tray.visible = True
					if gtk_platform():
						from gi.repository import GLib
						watch = HostWatch(lambda: tray_host_available(tray), emit, tray.stop)
						def tick():
							was_ready = watch.ready
							keep = watch.tick()
							if keep and watch.ready and not was_ready:
								GLib.timeout_add_seconds(2, tick)
								return False
							return keep
						GLib.timeout_add(250, tick)
					else:
						emit("ready")
				except Exception:
					try:
						emit("unavailable")
					finally:
						tray.stop()
			on_native_thread(activate)

		threading.Thread(target=wait_for_parent, daemon=True).start()
		icon.run(setup=setup)
		return 0
	except Exception:
		emit("unavailable")
		return 1


if __name__ == "__main__":
	sys.exit(main())
