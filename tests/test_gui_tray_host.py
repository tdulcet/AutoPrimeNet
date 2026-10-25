"""Tray host policy tests with simulated GTK/D-Bus and local IPC helpers.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import io
import json
import os
import subprocess
import sys
import time
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

from gui_controller import TrayController
from gui_tray_host import HostWatch, gtk_platform, load_pystray, status_notifier_host, tray_host_available, tray_platform


class TrayHostTests(unittest.TestCase):
	def test_supported_platforms_and_menu_requirement(self):
		for platform in ("darwin", "win32", "linux", "linux2", "freebsd14"):
			self.assertTrue(tray_platform(platform))
		self.assertFalse(tray_platform("sunos5"))
		self.assertFalse(gtk_platform("darwin"))
		with patch("gui_tray_host.sys.platform", "linux"):
			self.assertFalse(tray_host_available(SimpleNamespace(HAS_MENU=False)))
			self.assertFalse(tray_host_available(SimpleNamespace(HAS_MENU=True)))
			status = Mock()
			status.is_embedded.return_value = True
			self.assertTrue(tray_host_available(SimpleNamespace(HAS_MENU=True, _status_icon=status)))
			status.is_embedded.return_value = False
			self.assertFalse(tray_host_available(SimpleNamespace(HAS_MENU=True, _status_icon=status)))

	def test_status_notifier_probe_requires_host_property_and_is_bounded(self):
		bus = Mock()
		reply = Mock()
		bus.call_sync.return_value = reply
		gio = SimpleNamespace(bus_get_sync=Mock(return_value=bus), BusType=SimpleNamespace(SESSION=0), DBusCallFlags=SimpleNamespace(NO_AUTO_START=1))
		glib = SimpleNamespace(Variant=lambda signature, value: (signature, value))
		with patch.dict(sys.modules, {"gi": SimpleNamespace(repository=SimpleNamespace(Gio=gio, GLib=glib)), "gi.repository": SimpleNamespace(Gio=gio, GLib=glib)}):
			for value in (True, False, "false"):
				reply.unpack.return_value = (value,)
				self.assertEqual(status_notifier_host(), value is True)
			self.assertIn("IsStatusNotifierHostRegistered", str(bus.call_sync.call_args))
			self.assertEqual(bus.call_sync.call_args.args[-2], 1000)
			self.assertEqual(bus.call_sync.call_args.args[-3], 1)
			bus.call_sync.side_effect = OSError("local bus unavailable")
			self.assertFalse(status_notifier_host())

	def test_backend_selection_falls_back_from_missing_typelib_and_preserves_environment(self):
		with patch("gui_tray_host.sys.platform", "linux"), patch.dict(os.environ, {}, clear=True), patch("gui_tray_host.status_notifier_host", return_value=True):
			attempts = []
			def load(name):
				attempts.append(os.environ["PYSTRAY_BACKEND"])
				if attempts[-1] == "appindicator":
					raise ValueError("missing typelib")
				return "gtk-module"
			with patch("gui_tray_host.importlib.import_module", side_effect=load):
				self.assertEqual(load_pystray(), "gtk-module")
			self.assertEqual(attempts, ["appindicator", "gtk"])
			self.assertNotIn("PYSTRAY_BACKEND", os.environ)
		with patch("gui_tray_host.sys.platform", "freebsd14"), patch.dict(os.environ, {"PYSTRAY_BACKEND": "gtk"}), patch("gui_tray_host.importlib.import_module", return_value="explicit") as load:
			self.assertEqual(load_pystray(), "explicit")
			load.assert_called_once_with("pystray")
			self.assertEqual(os.environ["PYSTRAY_BACKEND"], "gtk")

	def test_host_watch_does_not_hide_without_host_and_stops_on_loss(self):
		now, events, stops = [0], [], []
		available = [False]
		watch = HostWatch(lambda: available[0], events.append, lambda: stops.append(True), clock=lambda: now[0])
		self.assertTrue(watch.tick())
		self.assertEqual(events, [])
		available[0] = True
		self.assertTrue(watch.tick())
		self.assertTrue(watch.tick())
		self.assertEqual(events, ["ready"])
		available[0] = False
		self.assertFalse(watch.tick())
		self.assertFalse(watch.tick())
		self.assertEqual(events, ["ready", "unavailable"])
		self.assertEqual(stops, [True])
		events.clear()
		watch = HostWatch(lambda: False, events.append, lambda: None, clock=lambda: now[0])
		now[0] = 6
		self.assertFalse(watch.tick())
		self.assertEqual(events, ["unavailable"])

	def test_controller_linux_launches_and_shutdown_invalidates_late_events(self):
		code = "import json,sys; print(json.dumps({'event':'ready'}),flush=True); sys.stdin.read()"
		def factory(_command, **kwargs):
			return subprocess.Popen([sys.executable, "-B", "-c", code], **kwargs)
		controller = TrayController(process_factory=factory)
		with patch("gui_tray_host.sys.platform", "linux"):
			controller.start()
		try:
			event = controller.events.get(timeout=5)
			self.assertEqual(event, {"event": "ready", "generation": controller.generation})
			generation = controller.generation
			process = controller.process
			controller.stop()
			self.assertGreater(controller.generation, generation)
			self.assertEqual(process.wait(timeout=5), 0)
			controller.stop()  # Idempotent; never reap a future replacement helper.
		finally:
			controller.stop()

	def test_old_reaper_and_reader_capture_old_process(self):
		controller = TrayController()
		old = Mock(stdout=io.StringIO('{"event":"ready"}\n'))
		new = Mock(stdout=io.StringIO())
		controller.process = new
		controller.generation = 5
		controller._read(old, 2)
		self.assertEqual(controller.events.get_nowait(), {"event": "ready", "generation": 2})
		controller._reap(old)
		old.wait.assert_called_once_with(timeout=3)
		new.wait.assert_not_called()

	def test_linux_helper_mainloop_host_loss_and_no_menu_fallback_without_display(self):
		code = r'''
import queue, sys, threading
from types import SimpleNamespace
import gui_tray
sys.platform = 'linux'
callbacks = queue.Queue()
class Loop:
    @staticmethod
    def idle_add(callback): callbacks.put(callback)
    @staticmethod
    def timeout_add(delay, callback): callbacks.put(callback)
    @staticmethod
    def timeout_add_seconds(delay, callback): callbacks.put(callback)
class Icon:
    HAS_MENU = sys.argv[1] != 'nomenu'
    def __init__(self, *args, **kwargs):
        self.ended = False
        self.probes = 0
        self.visible = False
        self._status_icon = SimpleNamespace(is_embedded=self.embedded)
    def embedded(self):
        self.probes += 1
        return self.probes < 3
    def update_menu(self): pass
    def stop(self): self.ended = True
    def run(self, setup):
        setup(self)
        while not self.ended:
            callback = callbacks.get(timeout=3)
            if callback(): callbacks.put(callback)
class Menu:
    SEPARATOR = object()
    def __init__(self, *args): pass
fake = SimpleNamespace(Icon=Icon, Menu=Menu, MenuItem=lambda *args, **kwargs: None)
repo = SimpleNamespace(GLib=Loop)
sys.modules['gi'] = SimpleNamespace(repository=repo)
sys.modules['gi.repository'] = repo
draw = SimpleNamespace(ellipse=lambda *a, **kw: None, line=lambda *a, **kw: None)
sys.modules['PIL'] = SimpleNamespace(Image=SimpleNamespace(new=lambda *a: object()), ImageDraw=SimpleNamespace(Draw=lambda *a: draw))
gui_tray.load_pystray = lambda: fake
sys.exit(gui_tray.main())
'''
		for mode in ("hostloss", "nomenu"):
			with self.subTest(mode=mode):
				process = subprocess.Popen([sys.executable, "-B", "-c", code, mode], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
				try:
					self.assertEqual(process.wait(timeout=5), 0 if mode == "hostloss" else 1)
					events = [json.loads(line)["event"] for line in process.stdout]
					self.assertEqual(events, ["ready", "unavailable"] if mode == "hostloss" else ["unavailable"])
					self.assertEqual(process.stderr.read(), "")
				finally:
					if process.poll() is None:
						process.kill()
					process.wait()
					for stream in (process.stdin, process.stdout, process.stderr):
						stream.close()
