"""Native scheduler lifecycle checks using temporary files and blocked sockets.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import ast
import json
import os
import queue
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import unittest
from unittest.mock import patch

from gui_backend import _read_source
from gui_monitor import StopControl, run_native, run_schedule
from gui_runtime import ROOT, Runtime, StoppingQueue, WorkerStopped, instrument


class RuntimeTests(unittest.TestCase):
	def test_stopping_queue_preserves_timeout_and_nonblocking_contract(self):
		stop = threading.Event()
		jobs = StoppingQueue(stop)
		with self.assertRaises(ValueError):
			jobs.get(timeout=-1)
		for options in ({"block": False}, {"timeout": 0}):
			with self.assertRaises(queue.Empty):
				jobs.get(**options)
			jobs.put("fixture")
			self.assertEqual(jobs.get(**options), "fixture")
		# A regression that ignores timeout must fail, rather than hang the suite.
		timer = threading.Timer(1, stop.set)
		timer.start()
		try:
			with self.assertRaises(queue.Empty):
				jobs.get(timeout=0.02)
		finally:
			timer.cancel()
			timer.join()
	def test_polling_and_watch_preferences_save_and_validate_offline(self):
		from gui_config import ConfigDocument, save_configuration
		from gui_controller import ControllerError, backend_request
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text("; retain comment\n[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\nHoursBetweenCheckins=2\n")
			document = ConfigDocument(directory)
			values = document.values()
			values.update(poll_seconds="1800", watch="False")
			result = save_configuration(document, values, "mlucas", [{"directory": "", "preference": ""}])
			document = result["document"]
			self.assertIn("; retain comment", document.text)
			self.assertEqual(document.config.getint("GUI", "PollSeconds"), 1800)
			self.assertFalse(document.config.getboolean("PrimeNet", "watch"))
			request = dict(text=document.text, directory=directory, config_name="prime.ini")
			settings = backend_request("validate_config", **request)
			self.assertEqual(settings["timeout"], 1800)
			self.assertFalse(settings["watch"])
			for interval in (1799, 7201):
				with self.subTest(interval=interval), self.assertRaises(ControllerError):
					backend_request("validate_config", **dict(request, text=document.text.replace("PollSeconds = 1800", f"PollSeconds = {interval}").replace("PollSeconds=1800", f"PollSeconds={interval}")))
			settings = backend_request("validate_config", **dict(request, text=document.text.replace("1800", "0")))
			self.assertEqual(settings["timeout"], 0)

	def test_instrumentation_retains_race_delays_and_guards_layout(self):
		_source, tree, _ = _read_source(ROOT / "autoprimenet.py")
		tree = instrument(tree)
		functions = {node.name: node for node in tree.body if isinstance(node, ast.FunctionDef)}
		for name, seconds in (("results_worker", 1), ("proofs_worker", 60)):
			self.assertIn(f"time.sleep({seconds})", ast.unparse(functions[name]))
		self.assertIn("_gui_cycles()", ast.unparse(functions["main"]))
		self.assertEqual(ast.unparse(functions["main"]).count("_gui_start("), 2)
		with self.assertRaises(ValueError):
			instrument(tree)  # A second transform must fail, not stack hooks.

	def test_stopped_queue_refuses_new_jobs_and_wakes_idle_worker(self):
		stop = threading.Event()
		jobs = StoppingQueue(stop)
		ended = threading.Event()
		def work():
			try:
				jobs.get()
			except WorkerStopped:
				ended.set()
		thread = threading.Thread(target=work)
		thread.start()
		stop.set()
		self.assertTrue(ended.wait(1))
		thread.join()
		jobs.put("ignored")
		self.assertTrue(jobs.empty())

	def test_graceful_drain_waits_for_active_worker_and_reports_failures(self):
		stop = threading.Event()
		runtime = Runtime(stop, lambda event: None, 1800)
		active, finish = threading.Event(), threading.Event()
		def work():
			active.set()
			finish.wait(2)
		worker = threading.Thread(target=runtime.wrap_worker(work))
		runtime.start_worker(worker)
		self.assertTrue(active.wait(1))
		drained = threading.Event()
		thread = threading.Thread(target=lambda: (runtime.drain(), drained.set()))
		thread.start()
		self.assertFalse(drained.wait(0.1))
		finish.set()
		self.assertTrue(drained.wait(1))
		thread.join()
		self.assertFalse(worker.is_alive())
		failed = Runtime(threading.Event(), lambda event: None, 1800)
		def error():
			raise OSError("private detail")
		failed.start_worker(threading.Thread(target=failed.wrap_worker(error)))
		with self.assertRaisesRegex(RuntimeError, "background worker failed"):
			failed.drain()

	def test_preflight_stop_and_one_pass_do_not_loop(self):
		control = StopControl()
		events = []
		def emit(event):
			events.append(event)
			if event["event"] == "ready":
				control.stop.set()
		with patch("gui_monitor.native_cycle") as cycle:
			self.assertEqual(run_native("unused", "prime.ini", 1800, True, "sha", control, emit), 0)
			cycle.assert_not_called()
		control = StopControl()
		control.begin.set()
		with patch("gui_monitor.cli_cycle", return_value=(0, False)) as cycle:
			self.assertEqual(run_schedule("unused", "prime.ini", 0, control, events.append, once=True), 0)
			cycle.assert_called_once()

	def test_original_scheduler_separates_polling_and_checkins_offline(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\nComputerGUID=0123456789abcdef0123456789abcdef\nwatch=False\nHoursBetweenCheckins=2\n")
			code = r'''
import contextlib, hashlib, io, json, sys, threading
from pathlib import Path
import gui_backend, gui_runtime
sys.addaudithook(gui_backend._network_guard)
stop = threading.Event()
events, polls = [], []
def emit(event):
    events.append(event)
    if event['event'] == 'cycle_finished' and len(polls) >= 2:
        stop.set()
def prepare(ns, runtime):
    for name in ('check_disk_space', 'process_add_file', 'get_cert_work', 'download_certs', 'adjust_rolling_average', 'version_check', 'register_instance'):
        ns[name] = lambda *args, **kwargs: None
    ns['read_workfile'] = lambda *args: []
    ns['register_assignments'] = lambda *args: False
    ns['submit_work'] = lambda *args: True
    ns['update_progress_all'] = lambda *args: None
    ns['upload_proofs'] = lambda *args: True
    ns['get_assignments'] = lambda *args: polls.append(args[-1])
    ns['_gui_pause'] = lambda delay: runtime.finished(delay)
path = Path(sys.argv[1]) / 'prime.ini'
request = dict(protocol=1, directory=str(path.parent), config_name=path.name, interval=1800, config_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
    result = gui_runtime.execute(request, stop, emit, prepare)
print(json.dumps(dict(result=result, polls=polls, events=events)))
'''
			process = subprocess.run([sys.executable, "-B", "-c", code, directory], cwd=ROOT, capture_output=True, text=True, timeout=15)
			self.assertEqual(process.returncode, 0, process.stderr)
			result = json.loads(process.stdout)
			self.assertEqual(result["result"], 0)
			self.assertEqual(result["polls"], [True, False])
			self.assertEqual([item["event"] for item in result["events"]], ["cycle_started", "cycle_finished", "cycle_started", "cycle_finished"])
			self.assertTrue(all(item.get("server_confirmation") == "unverified" for item in result["events"] if item["event"] == "cycle_finished"))

	@unittest.skipUnless(sys.platform == "darwin" or sys.platform.startswith("linux") or sys.platform == "win32", "Native watcher platform test")
	@unittest.skipUnless(os.environ.get("AUTOPRIMENET_GUI_DESKTOP_TESTS") == "1", "Requires enabled native OS integration tests")
	def test_native_watcher_delivers_real_local_result_change_and_drains_worker(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\nComputerGUID=0123456789abcdef0123456789abcdef\nwatch=True\n")
			(Path(directory) / "results.txt").write_text("")
			code = r'''
import contextlib, hashlib, io, json, sys, threading, time
from pathlib import Path
import gui_backend, gui_runtime
sys.addaudithook(gui_backend._network_guard)
stop, scanned = threading.Event(), threading.Event()
path = Path(sys.argv[1]) / 'prime.ini'
seen, runtimes = [], []
def prepare(ns, runtime):
    runtimes.append(runtime)
    for name in ('check_disk_space', 'process_add_file', 'get_cert_work', 'get_assignments', 'download_certs', 'adjust_rolling_average', 'version_check', 'register_instance'):
        ns[name] = lambda *args, **kwargs: None
    ns['read_workfile'] = lambda *args: []
    ns['register_assignments'] = lambda *args: False
    ns['update_progress_all'] = lambda *args: None
    ns['upload_proofs'] = lambda *args: True
    ns['_gui_idle'] = lambda delay: None  # Test only: skip the 5-minute cooldown.
    def submit(*args):
        seen.append((path.parent / 'results.txt').read_text())
        scanned.set()
        if 'fixture-result' in seen[-1]:
            stop.set()
        return True
    ns['submit_work'] = submit
    def change():
        if scanned.wait(5):
            time.sleep(0.2)
            (path.parent / 'results.txt').write_text('fixture-result')
    threading.Thread(target=change, daemon=True).start()
request = dict(protocol=1, directory=str(path.parent), config_name=path.name, interval=1800, config_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
    result = gui_runtime.execute(request, stop, lambda event: None, prepare)
print(json.dumps(dict(result=result, seen=seen, drained=all(not t.is_alive() for t in runtimes[0].workers))))
'''
			process = subprocess.run([sys.executable, "-B", "-c", code, directory], cwd=ROOT, capture_output=True, text=True, timeout=12)
			self.assertEqual(process.returncode, 0, process.stderr)
			result = json.loads(process.stdout)
			self.assertEqual(result["result"], 0)
			self.assertEqual(result["seen"], ["", "fixture-result"])
			self.assertTrue(result["drained"])

	def test_supervisor_forwards_stop_and_force_targets_only_owned_child(self):
		from gui_monitor import _native_process
		control = StopControl()
		control.stop.set()
		code = "import json,sys; request=json.loads(sys.stdin.buffer.readline()); assert request['interval']==1800; assert json.loads(sys.stdin.buffer.readline())['command']=='stop'"
		process = subprocess.Popen([sys.executable, "-c", code], stdin=subprocess.PIPE)
		with patch("gui_monitor.subprocess.Popen", return_value=process):
			self.assertEqual(_native_process("fixture", "prime.ini", control, 1800, "sha"), (0, False))
		control = StopControl()
		control.force.set()
		process = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)"], stdin=subprocess.PIPE)
		unrelated = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)"])
		try:
			with patch("gui_monitor.subprocess.Popen", return_value=process):
				self.assertTrue(_native_process("fixture", "prime.ini", control, 1800, "sha")[1])
			self.assertIsNotNone(process.poll())
			self.assertIsNone(unrelated.poll())
		finally:
			if process.poll() is None:
				process.kill()
			process.wait()
			unrelated.terminate()
			unrelated.wait()
