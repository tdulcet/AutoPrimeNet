#!/usr/bin/env python3
"""GUI-owned native scheduler with boundary stops and worker draining.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import ast
import contextlib
import hashlib
import json
import os
import queue
import sys
import threading
import time
from pathlib import Path

from gui_backend import _read_source
from gui_config import ConfigDocument
from gui_registration_plan import block_terminal
from gui_trace import debug_arguments

ROOT = Path(__file__).resolve().parent


class WorkerStopped(BaseException):
	"""Private clean exit raised only at an idle queue boundary."""


class StoppingQueue(queue.Queue):
	def __init__(self, stop):
		super().__init__()
		self.stop = stop

	def put(self, item, block=True, timeout=None):
		if not self.stop.is_set():
			return super().put(item, block, timeout)

	def get(self, block=True, timeout=None):
		if not block:
			return super().get(False)
		if timeout is not None and timeout < 0:
			raise ValueError("'timeout' must be a non-negative number")
		deadline = None if timeout is None else time.monotonic() + timeout
		while not self.stop.is_set():
			remaining = None if deadline is None else deadline - time.monotonic()
			if remaining is not None and remaining <= 0:
				return super().get(False)
			try:
				return super().get(timeout=0.1 if remaining is None else min(0.1, remaining))
			except queue.Empty:
				pass
		raise WorkerStopped()


class Runtime:
	def __init__(self, stop, emit, interval):
		self.stop = stop
		self.emit = emit
		self.interval = interval
		self.workers = []
		self.errors = []
		self.active_cycle = False
		self.log_error = lambda: None

	def cycles(self):
		index = 0
		while not self.stop.is_set():
			if self.errors:
				raise RuntimeError("An AutoPrimeNet background worker failed.")
			self.active_cycle = True
			self.emit({"event": "cycle_started", "time": time.time()})
			yield index
			self.finished(0)
			index += 1

	def finished(self, delay):
		if self.active_cycle:
			self.active_cycle = False
			self.emit({"event": "cycle_finished", "time": time.time(), "next_cycle": time.time() + delay, "server_confirmation": "unverified", "native_scheduler": True})

	def pause(self, delay):
		self.finished(delay)
		# Also notice background worker failures without waiting a full interval.
		deadline = time.monotonic() + delay
		while not self.stop.is_set() and not self.errors:
			if self.stop.wait(min(max(deadline - time.monotonic(), 0), 0.2)) or time.monotonic() >= deadline:
				break
		if self.errors:
			raise RuntimeError("An AutoPrimeNet background worker failed.")

	def wrap_worker(self, function):
		def worker(*args):
			try:
				function(*args)
			except WorkerStopped:
				pass
			except BaseException:
				try:
					self.log_error()
				finally:
					self.errors.append(True)
					self.stop.set()
		return worker

	def start_worker(self, worker):
		self.workers.append(worker)
		worker.start()

	def drain(self):
		self.stop.set()
		for worker in self.workers:
			if worker.ident is not None:
				worker.join()  # Never abandon an active request or file write.
		if self.errors:
			raise RuntimeError("An AutoPrimeNet background worker failed.")


def instrument(tree):
	"""Add only reviewed lifecycle hooks; reject source layout drift."""
	functions = {node.name: node for node in tree.body if isinstance(node, ast.FunctionDef)}
	main = functions["main"]
	loops = [node for node in ast.walk(main) if isinstance(node, ast.For) and isinstance(node.target, ast.Name) and node.target.id == "j" and isinstance(node.iter, ast.Call) and isinstance(node.iter.func, ast.Name) and node.iter.func.id == "count"]
	if len(loops) != 1:
		raise ValueError("Unsupported native scheduler loop.")
	loops[0].iter = ast.Call(func=ast.Name(id="_gui_cycles", ctx=ast.Load()), args=[], keywords=[])
	counts = {}
	starts = 0
	for node in ast.walk(main):
		if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name) and node.func.value.id in {"proofs_thread", "results_thread"} and node.func.attr == "start":
			node.args = [node.func.value]
			node.func = ast.Name(id="_gui_start", ctx=ast.Load())
			starts += 1
	if starts != 2:
		raise ValueError("Unsupported native worker startup layout.")
	for name in ("main", "results_worker", "proofs_worker"):
		count = 0
		for node in ast.walk(functions[name]):
			if not isinstance(node, ast.Call) or not isinstance(node.func, ast.Attribute) or not isinstance(node.func.value, ast.Name) or node.func.value.id != "time" or node.func.attr != "sleep":
				continue
			# Keep the original 1s results and 60s proof ordering delays. Only
			# scheduler waits/retry cooldowns may wake early during shutdown.
			if name != "main" and isinstance(node.args[0], ast.Constant):
				continue
			node.func = ast.Name(id="_gui_pause" if name == "main" else "_gui_idle", ctx=ast.Load())
			count += 1
		counts[name] = count
	if counts != {"main": 1, "results_worker": 2, "proofs_worker": 1}:
		raise ValueError("Unsupported native scheduler wait layout.")
	return ast.fix_missing_locations(tree)


def execute(request, stop, emit, before_main=None):
	if not isinstance(request, dict) or request.get("protocol") != 1:
		raise ValueError("Unsupported runtime request.")
	interval = request.get("interval")
	if type(interval) is not int or not 1800 <= interval <= 604800:
		raise ValueError("Native polling must be at least 1800 seconds.")
	document = ConfigDocument(request["directory"], request["config_name"])
	if document.bom or document.version is None or hashlib.sha256(document.data).hexdigest() != request.get("config_sha256"):
		raise ValueError("Configuration changed or has an unsupported encoding.")
	path = ROOT / "autoprimenet.py"
	_source, tree, _boundary = _read_source(path)
	tree = instrument(tree)
	calls = [i for i, node in enumerate(tree.body) if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name) and node.value.func.id == "main"]
	if len(calls) != 1:
		raise ValueError("Unsupported native main entry point.")
	runtime = Runtime(stop, emit, interval)
	namespace = {"__name__": "__main__", "__file__": str(path), "_gui_cycles": runtime.cycles, "_gui_pause": runtime.pause, "_gui_idle": stop.wait, "_gui_start": runtime.start_worker}
	argv = sys.argv
	sys.argv = [str(path), "--workdir", str(document.directory), "--config-file", document.path.name, "--timeout", str(interval), *debug_arguments(document.config)]
	code = 0
	try:
		if stop.is_set():
			return 0
		exec(compile(ast.Module(body=tree.body[:calls[0]], type_ignores=[]), str(path), "exec"), namespace)
		block_terminal(namespace)
		if interval > namespace["args"].hours_between_checkins * 3600:
			raise ValueError("Polling cannot exceed the progress check-in interval.")
		namespace["results_queue"] = StoppingQueue(stop)
		namespace["proofs_queue"] = StoppingQueue(stop)
		runtime.log_error = lambda: namespace["logger"].exception("A GUI-owned AutoPrimeNet background worker failed.")
		for name in ("results_worker", "proofs_worker"):
			namespace[name] = runtime.wrap_worker(namespace[name])
		# Watchers only enqueue names, so they can remain daemon threads. A
		# failed native watcher still stops monitoring and drains active writers.
		namespace["watch_files"] = runtime.wrap_worker(namespace["watch_files"])
		if before_main is not None:
			before_main(namespace, runtime)  # Tests only; never accepted via IPC.
		if not stop.is_set():
			namespace["main"]()
	except SystemExit as error:
		code = int(error.code or 0)
	finally:
		# Watchers only enqueue events and remain daemon threads. Queue writes
		# after Stop are ignored; their native handles close with this child.
		try:
			runtime.drain()
		finally:
			sys.argv = argv
	return code


def main():
	output = sys.stdout
	def emit(message):
		print(json.dumps(message), file=output, flush=True)
	stop = threading.Event()
	try:
		stream = os.fdopen(sys.stdin.fileno(), "rb", buffering=0, closefd=False)
		line = stream.readline(65537)
		if len(line) > 65536:
			raise ValueError("Runtime request is too large.")
		request = json.loads(line)
		def control():
			for line in stream:
				try:
					if json.loads(line).get("command") == "stop":
						stop.set()
				except (ValueError, AttributeError):
					pass
			stop.set()
		threading.Thread(target=control, name="RuntimeControl", daemon=True).start()
		# Native console/HTTP output must not corrupt the event channel.
		with contextlib.redirect_stdout(sys.stderr):
			return execute(request, stop, emit)
	except (Exception, SystemExit):
		emit({"event": "failed", "error": "Native monitoring failed. Inspect the private backend log and refresh before restarting."})
		return 1


if __name__ == "__main__":
	sys.exit(main())
