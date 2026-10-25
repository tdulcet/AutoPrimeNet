"""Validated GUI verbosity and bounded private raw backend traces.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

from contextlib import contextmanager
import os
from pathlib import Path
import tempfile
import threading

MAX_TRACE_BYTES = 8 * 1024 * 1024
TRUNCATED = b"\n[GUI trace capture limit reached; later output discarded.]\n"


def debug_level(config):
	level = config.getint("GUI", "DebugLevel", fallback=0)
	if not 0 <= level <= 3:
		raise ValueError("Debug verbosity must be 0, 1, 2 or 3.")
	return level


def debug_arguments(config):
	return ["--debug"] * debug_level(config)


def trace_notice(document):
	if debug_level(document.config) < 2:
		return ""
	return "\n\nHTTP/SMTP tracing is enabled. It can record passwords, authentication tokens, addresses and message bodies in a private local trace file (up to 8 MiB per CLI process). Review/redact before sharing; delete when no longer needed."


class TraceCapture:
	def __init__(self, directory, limit=MAX_TRACE_BYTES):
		self.stream = tempfile.NamedTemporaryFile("wb", prefix=".gui-backend-trace-", suffix=".log", dir=directory, delete=False)
		self.path = Path(self.stream.name)
		self.limit = limit
		self.thread = None
		self.failed = False

	def start(self, output):
		def drain():
			remaining = max(self.limit - len(TRUNCATED), 0)
			limited = False
			try:
				read = getattr(output, "read1", output.read)
				while data := read(64 * 1024):
					if remaining and not self.failed:
						try:
							self.stream.write(data[:remaining])
							remaining -= min(len(data), remaining)
							if remaining == 0 and not limited:
								self.stream.write(TRUNCATED)
								limited = True
							self.stream.flush()
						except OSError:
							self.failed = True
				# Continue draining after the limit/error so tracing cannot block
				# the CLI's stdout/stderr and interrupt an active upload/write.
			except OSError:
				self.failed = True
			finally:
				output.close()
		self.thread = threading.Thread(target=drain, name="PrivateTrace", daemon=True)
		self.thread.start()

	def close(self):
		if self.thread is not None:
			self.thread.join()
		try:
			self.stream.flush()
			os.fsync(self.stream.fileno())
		except OSError:
			self.failed = True
		finally:
			try:
				self.stream.close()
			except OSError:
				self.failed = True


@contextmanager
def private_trace(directory, level):
	capture = TraceCapture(directory) if level >= 2 else None
	try:
		yield capture
	finally:
		if capture is not None:
			capture.close()
