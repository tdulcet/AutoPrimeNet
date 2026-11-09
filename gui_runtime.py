#!/usr/bin/env python3
"""GUI-owned native scheduler with boundary stops and worker draining.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import contextlib
import hashlib
import json
import os
import queue
import sys
import threading
import time
from pathlib import Path

from gui_backend import _load_definitions
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
	def __init__(self, stop, emit, interval, push=None):
		self.stop = stop
		self.emit = emit
		self.interval = interval
		self.push = push if push is not None else threading.Event()
		self.push_cycle = False
		self.workers = []
		self.errors = []
		self.active_cycle = False
		self.log_error = lambda: None

	def cycles(self):
		index = 0
		while not self.stop.is_set():
			if self.errors:
				raise RuntimeError("An AutoPrimeNet background worker failed.")
			self.push_cycle = self.push.is_set()
			if self.push_cycle:
				self.push.clear()
			self.active_cycle = True
			self.emit({"event": "cycle_started", "time": time.time(), "push_status": self.push_cycle})
			yield index
			self.finished(0)
			index += 1

	def finished(self, delay):
		if self.active_cycle:
			self.active_cycle = False
			self.emit({"event": "cycle_finished", "time": time.time(), "next_cycle": time.time() + delay, "server_confirmation": "unverified", "native_scheduler": True, "push_status": self.push_cycle})

	def pause(self, delay):
		self.finished(delay)
		# Also notice background worker failures without waiting a full interval.
		deadline = time.monotonic() + delay
		while not self.stop.is_set() and not self.errors and not self.push.is_set():
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


def execute(request, stop, emit, before_main=None, push=None):
	if not isinstance(request, dict) or request.get("protocol") != 1:
		raise ValueError("Unsupported runtime request.")
	interval = request.get("interval")
	if type(interval) is not int or not 1800 <= interval <= 604800:
		raise ValueError("Native polling must be at least 1800 seconds.")
	document = ConfigDocument(request["directory"], request["config_name"])
	if document.bom or document.version is None or hashlib.sha256(document.data).hexdigest() != request.get("config_sha256"):
		raise ValueError("Configuration changed or has an unsupported encoding.")
	path = ROOT / "autoprimenet.py"
	runtime = Runtime(stop, emit, interval, push)
	argv = sys.argv
	sys.argv = [str(path), "--workdir", str(document.directory), "--config-file", document.path.name, "--timeout", str(interval), *debug_arguments(document.config)]
	code = 0
	try:
		if stop.is_set():
			return 0
		namespace = _load_definitions(path)
		namespace["initialize_cli"]()
		namespace.update(
			scheduler_cycles=runtime.cycles,
			scheduler_checkin=lambda: runtime.push_cycle,
			scheduler_pause=runtime.pause,
			scheduler_idle=stop.wait,
			scheduler_start=runtime.start_worker,
		)
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
	push = threading.Event()
	try:
		stream = os.fdopen(sys.stdin.fileno(), "rb", buffering=0, closefd=False)
		line = stream.readline(65537)
		if len(line) > 65536:
			raise ValueError("Runtime request is too large.")
		request = json.loads(line)
		def control():
			for line in stream:
				try:
					command = json.loads(line).get("command")
					if command == "stop":
						stop.set()
					elif command == "push-status":
						push.set()
				except (ValueError, AttributeError):
					pass
			stop.set()
		threading.Thread(target=control, name="RuntimeControl", daemon=True).start()
		# Native console/HTTP output must not corrupt the event channel.
		with contextlib.redirect_stdout(sys.stderr):
			return execute(request, stop, emit, push=push)
	except (Exception, SystemExit):
		emit({"event": "failed", "error": "Native monitoring failed. Inspect the private backend log and refresh before restarting."})
		return 1


if __name__ == "__main__":
	sys.exit(main())
