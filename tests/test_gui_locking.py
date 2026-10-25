"""Native lock policy and mandatory atomic GUI ownership tests.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import errno
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from gui_config import ConfigDocument, GUI_GUARD, WorkspaceError, instance_lease, lock_policy_notice, save_configuration
from gui_controller import backend_request


class LockPolicyTests(unittest.TestCase):
	def document(self, directory, policy=""):
		path = Path(directory) / "prime.ini"
		path.write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n" + ("require_lock=" + policy + "\n" if policy else ""))
		return ConfigDocument(directory)

	def test_default_is_strict_and_false_only_relaxes_native_lock_errors(self):
		with tempfile.TemporaryDirectory() as directory:
			for code in (errno.EAGAIN, errno.EACCES, errno.ENOSYS, errno.ENOLCK):
				for required in (True, False):
					with self.subTest(code=code, required=required), patch("gui_config._lock_stream", side_effect=OSError(code, "fixture")):
						if required or code in (errno.EAGAIN, errno.EACCES):
							with self.assertRaises(WorkspaceError):
								with instance_lease(directory, require_lock=required):
									self.fail("Lock policy bypassed")
						else:
							with instance_lease(directory, require_lock=False) as verified:
								self.assertFalse(verified)

	def test_guard_remains_exclusive_without_native_locking_and_is_private(self):
		with tempfile.TemporaryDirectory() as directory, patch("gui_config._lock_stream", side_effect=OSError(errno.ENOSYS, "fixture")):
			path = Path(directory) / GUI_GUARD
			with instance_lease(directory, "~gui-monitor.lock", require_lock=False) as verified:
				self.assertFalse(verified)
				owner = json.loads(path.read_text())
				self.assertEqual(owner["pid"], os.getpid())
				self.assertTrue(owner["host"])
				self.assertEqual(len(owner["token"]), 32)
				if os.name != "nt":
					self.assertEqual(path.stat().st_mode & 0o777, 0o600)
				with self.assertRaisesRegex(WorkspaceError, "guard already exists"):
					with instance_lease(directory, "~gui-monitor.lock", require_lock=False):
						pass
			self.assertFalse(path.exists())

	def test_stale_and_symlink_guards_are_never_removed_or_followed(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / GUI_GUARD
			path.write_text("stale owner")
			with self.assertRaises(WorkspaceError):
				with instance_lease(directory, "~gui-monitor.lock", require_lock=False):
					pass
			self.assertEqual(path.read_text(), "stale owner")
			path.unlink()
			target = Path(directory) / "target"
			target.write_text("unchanged")
			try:
				path.symlink_to(target)
			except OSError:
				return
			with self.assertRaises(WorkspaceError):
				with instance_lease(directory, "~gui-monitor.lock", require_lock=False):
					pass
			self.assertTrue(path.is_symlink())
			self.assertEqual(target.read_text(), "unchanged")

	def test_guard_cleanup_uses_token_not_timestamp_and_rejects_native_fifo(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / GUI_GUARD
			with instance_lease(directory, "~gui-monitor.lock"):
				os.utime(path, ns=(1, 1))
			self.assertFalse(path.exists())
			if hasattr(os, "mkfifo"):
				os.mkfifo(Path(directory) / "~lock")
				with self.assertRaisesRegex(WorkspaceError, "regular files"):
					with instance_lease(directory, require_lock=False):
						pass

	def test_guard_cleanup_does_not_remove_replacement_and_handles_write_failure(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / GUI_GUARD
			with instance_lease(directory, "~gui-monitor.lock"):
				# Replace contents (also supported when Windows holds the inode).
				path.write_text("replacement owner")
			self.assertEqual(path.read_text(), "replacement owner")
			path.unlink()
			with patch("gui_config.os.fsync", side_effect=OSError("fixture disk error")):
				with self.assertRaises(OSError):
					with instance_lease(directory, "~gui-monitor.lock"):
						pass
			self.assertFalse(path.exists())

	def test_false_policy_saves_offline_when_native_locking_is_unavailable(self):
		with tempfile.TemporaryDirectory() as directory:
			document = self.document(directory)
			values = document.values()
			values["require_lock"] = "False"
			with patch("gui_config._lock_stream", side_effect=OSError(errno.ENOSYS, "fixture")):
				with self.assertRaises(WorkspaceError):
					save_configuration(document, document.values(), "mlucas", [{"directory": "", "preference": ""}])
				result = save_configuration(document, values, "mlucas", [{"directory": "", "preference": ""}])
			document = result["document"]
			self.assertFalse(document.config.getboolean("PrimeNet", "require_lock"))
			self.assertIn("independent CLI", lock_policy_notice(document.config))
			settings = backend_request("validate_config", text=document.text, directory=directory, config_name="prime.ini")
			self.assertFalse(settings["require_lock"])
			self.assertFalse((Path(directory) / GUI_GUARD).exists())

	def test_supervisor_reports_unverified_lock_and_guard_blocks_save_and_duplicate(self):
		from gui_controller import MonitorController
		from test_gui_monitor import fake_monitor_process, wait_event
		def factory(*args, **kwargs):
			return fake_monitor_process(*args, simulate_lock_failure=True, **kwargs)
		with tempfile.TemporaryDirectory() as directory:
			document = self.document(directory, "False")
			first, second = MonitorController(process_factory=factory), MonitorController(process_factory=factory)
			try:
				first.start(document)
				self.assertTrue(wait_event(first, "ready")["native_lock_unverified"])
				second.start(document)
				self.assertIn("guard already exists", wait_event(second, "failed")["error"])
				wait_event(second, "exited")
				with self.assertRaisesRegex(WorkspaceError, "guard already exists"):
					save_configuration(document, document.values(), "mlucas", [{"directory": "", "preference": ""}])
			finally:
				for controller in (first, second):
					if controller.active:
						controller.stop(force=True)
						wait_event(controller, "exited")
			self.assertFalse((Path(directory) / GUI_GUARD).exists())

	def test_configuration_and_runtime_data_cannot_use_guard_or_lock_names(self):
		from gui_controller import ControllerError
		with tempfile.TemporaryDirectory() as directory:
			for name in (GUI_GUARD, GUI_GUARD.upper(), "~LOCK"):
				with self.subTest(name=name), self.assertRaises(WorkspaceError):
					ConfigDocument(directory, name)
			document = self.document(directory)
			for field in ("logfile", "work_file", "results_file", "ProofArchiveDir"):
				values = document.values()
				values[field] = GUI_GUARD
				with self.subTest(field=field), self.assertRaises((WorkspaceError, ControllerError)):
					save_configuration(document, values, "mlucas", [{"directory": "", "preference": ""}])
			self.assertEqual(document.path.read_bytes(), document.data)
			self.assertFalse((Path(directory) / GUI_GUARD).exists())

	def test_original_startup_honors_saved_policy_in_both_adapters_offline(self):
		root = Path(__file__).resolve().parents[1]
		code = r'''
import ast, contextlib, hashlib, io, json, sys, threading
from pathlib import Path
import gui_backend, gui_registration, gui_runtime
sys.addaudithook(gui_backend._network_guard)
original = gui_backend._read_source
adapter = gui_runtime if sys.argv[2] == 'native' else gui_registration
def source(path):
    raw, tree, boundary = original(path)
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef) and node.name == 'lock_file':
            node.body = ast.parse("raise OSError(errno.ENOSYS, 'simulated unsupported native lock')").body
    return raw, ast.fix_missing_locations(tree), boundary
adapter._read_source = source
path = Path(sys.argv[1]) / 'prime.ini'
seen = []
def inspect(ns, *unused):
    seen.append(ns['args'].lock)
    ns['main'] = lambda: None
request = dict(protocol=1, directory=str(path.parent), config_name=path.name, interval=1800, config_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
    if sys.argv[2] == 'native':
        result = adapter.execute(request, threading.Event(), lambda event: None, inspect)
    else:
        request['operation'] = 'register_computer'
        result = adapter.execute(request, inspect)
print(json.dumps(dict(result=result, seen=seen)))
'''
		for adapter in ("native", "registration"):
			for required in (True, False):
				with self.subTest(adapter=adapter, required=required), tempfile.TemporaryDirectory() as directory:
					self.document(directory, str(required))
					process = subprocess.run([sys.executable, "-B", "-c", code, directory, adapter], cwd=root, capture_output=True, text=True, timeout=15)
					self.assertEqual(process.returncode, 0, process.stderr)
					result = json.loads(process.stdout)
					self.assertEqual(result, {"result": 1, "seen": []} if required else {"result": 0, "seen": [False]})
