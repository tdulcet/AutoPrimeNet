"""Isolated tests for the offline GUI integration prototype.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import hashlib
import json
import os
import re
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
BRIDGE = ROOT / "gui_backend.py"
BASELINE_SHA256 = "05776d74b7b816c52774c30de438e7dcf047127a810daa8ee36335f8b8e7ec12"


class BackendTests(unittest.TestCase):
	def test_documented_parity_inventory_matches_audited_parser(self):
		from gui_reference import reference_info
		options = self.run_bridge({"protocol": 1, "operation": "capabilities"})["result"]["cli_options"]
		documented = []
		for line in (ROOT / "GUI_PARITY.md").read_text().splitlines():
			if not line.startswith("| `"):
				continue
			cells = [cell.strip() for cell in line.split("|")]
			documented.append((re.findall(r"`([^`]+)`", cells[1]), cells[2].strip("`"), cells[3]))
		expected = [(item["flags"], item["dest"], reference_info(item["dest"])[2]) for item in options]
		self.assertEqual(documented, expected)
	def test_gpu_discovery_is_offline_and_creates_no_runtime_files(self):
		response = self.run_bridge({"protocol": 1, "operation": "discover_gpus"})
		self.assertTrue(response["ok"], response)
		self.assertIsInstance(response["result"]["devices"], list)
		self.assertFalse(response["result"]["network_enabled"])
		self.assertFalse(response["result"]["files_written"])

	def test_original_cli_help_needs_no_configuration_and_writes_no_files(self):
		response = self.run_bridge({"protocol": 1, "operation": "cli_help"})
		self.assertTrue(response["ok"])
		self.assertIn("usage: autoprimenet.py", response["result"]["text"])
		self.assertIn("--register-exponents", response["result"]["text"])
		self.assertFalse(response["result"]["files_written"])
		self.assertFalse(response["result"]["network_enabled"])

	def test_all_audited_cli_entries_have_explicit_coverage_classification(self):
		from gui_reference import reference_info
		result = self.run_bridge({"protocol": 1, "operation": "capabilities"})["result"]
		self.assertEqual(result["backend_version"], "2.0.2")
		self.assertFalse([item for item in result["cli_options"] if reference_info(item["dest"])[2] == "Unmapped"])
		self.assertEqual(reference_info("timeout")[2], "Available")
		self.assertEqual(reference_info("setup")[2], "Available")
		self.assertEqual(reference_info("watch")[2], "Available")
		self.assertEqual(reference_info("lock")[2], "Available")
		self.assertEqual(sum(reference_info(item["dest"])[2] == "Available" for item in result["cli_options"]), 94)
	def run_bridge(self, request, source=None):
		with tempfile.TemporaryDirectory() as directory:
			command = [sys.executable, "-B", str(BRIDGE)]
			if source is not None:
				command.extend(["--source", str(source)])
			process = subprocess.run(
				command, input=json.dumps(request), text=True, capture_output=True,
				cwd=directory, timeout=30,
			)
			self.assertEqual(os.listdir(directory), [], "Probe created runtime files")
			self.assertEqual(process.stderr, "")
			response = json.loads(process.stdout)
			self.assertEqual(response["protocol"], 1)
			self.assertEqual(process.returncode, 0 if response["ok"] else 1)
			return response

	def test_inventory_includes_hidden_inverse_and_automatic_options(self):
		response = self.run_bridge({"protocol": 1, "operation": "capabilities"})
		self.assertTrue(response["ok"])
		result = response["result"]
		flags = {flag for option in result["cli_options"] for flag in option["flags"]}
		self.assertTrue({"--password", "--prime95", "--no-cert-work", "--help", "--setup"} <= flags)
		self.assertFalse(result["network_enabled"])
		self.assertEqual(len(result["cli_options"]), 96)

	def test_reuses_assignment_parser_and_formatter_for_all_file_worktypes(self):
		lines = [
			"Test=127,70,1", "DoubleCheck=127,70,1",
			"PRP=1,2,127,-1,70,1.3", "PRPDC=1,2,127,-1,70,0,3,1",
			"Factor=127,70,71", "Pfactor=1,2,127,-1,70,1.3",
			"Pminus1=1,2,127,-1,100000,1000000,70",
			"Pplus1=1,2,127,-1,100000,1000000,1,70",
			"ECM2=1,2,127,-1,100000,1000000,10",
			"Cert=1,2,127,-1,1000000",
		]
		response = self.run_bridge({"protocol": 1, "operation": "parse_work", "lines": lines})
		self.assertTrue(response["ok"], response)
		assignments = response["result"]["assignments"]
		self.assertEqual(len(assignments), len(lines))
		for line, item in zip(lines, assignments, strict=True):
			with self.subTest(line=line):
				self.assertTrue(item["parsed"])
				self.assertEqual(item["fields"]["n"], 127)
				self.assertEqual(item["server_confirmation"], "unverified")
		second = self.run_bridge({"protocol": 1, "operation": "parse_work", "lines": [item["canonical"] for item in assignments]})
		self.assertTrue(second["ok"])
		self.assertEqual(second["result"]["assignments"], assignments)

	def test_aid_is_not_treated_as_remote_confirmation(self):
		line = "Test=0123456789ABCDEF0123456789ABCDEF,127,70,1"
		response = self.run_bridge({"protocol": 1, "operation": "parse_work", "lines": [line]})
		self.assertTrue(response["ok"])
		item = response["result"]["assignments"][0]
		self.assertEqual(item["fields"]["uid"], "0123456789ABCDEF0123456789ABCDEF")
		self.assertEqual(item["server_confirmation"], "unverified")

	def test_malformed_work_line_is_reported_without_inventing_assignment(self):
		response = self.run_bridge({"protocol": 1, "operation": "parse_work", "lines": ["not an assignment"]})
		self.assertTrue(response["ok"])
		self.assertEqual(response["result"]["assignments"], [{"parsed": False}])

	def test_source_drift_is_rejected_before_execution(self):
		with tempfile.TemporaryDirectory() as directory:
			source = Path(directory) / "autoprimenet.py"
			source.write_text("raise RuntimeError('DO NOT EXECUTE')\n")
			response = self.run_bridge({"protocol": 1, "operation": "parse_work", "lines": []}, source)
		self.assertFalse(response["ok"])
		self.assertIn("differs from the audited version", response["error"])

	def test_mutating_operations_and_bad_protocol_are_rejected(self):
		for request in (
			{"protocol": 1, "operation": "unreserve_all"},
			{"protocol": 2, "operation": "capabilities"},
			{"protocol": 1, "operation": "parse_work", "lines": "wrong type"},
		):
			with self.subTest(request=request):
				self.assertFalse(self.run_bridge(request)["ok"])

	def test_network_guard_blocks_connection_before_any_network_io(self):
		code = "\n".join([
			"import socket, sys",
			"import gui_backend",
			"sys.addaudithook(gui_backend._network_guard)",
			"try:",
			"    socket.create_connection(('127.0.0.1', 9))",
			"except gui_backend.BackendError:",
			"    print('blocked')",
			"else:",
			"    sys.exit('Network guard did not block the connection')",
		])
		process = subprocess.run([sys.executable, "-B", "-c", code], cwd=ROOT, capture_output=True, text=True, timeout=10)
		self.assertEqual(process.returncode, 0, process.stderr)
		self.assertEqual(process.stdout.strip(), "blocked")

	def test_invalid_json_does_not_echo_secret_input(self):
		process = subprocess.run(
			[sys.executable, "-B", str(BRIDGE)], input="private-password: malformed JSON",
			capture_output=True, text=True, timeout=10,
		)
		self.assertEqual(process.returncode, 1)
		self.assertFalse(json.loads(process.stdout)["ok"])
		self.assertNotIn("private-password", process.stdout + process.stderr)

	def test_multiline_work_input_is_rejected(self):
		response = self.run_bridge({"protocol": 1, "operation": "parse_work", "lines": ["Test=127\nTest=131"]})
		self.assertFalse(response["ok"])
		self.assertIn("single line", response["error"])

	def test_existing_source_remains_byte_identical(self):
		self.assertEqual(hashlib.sha256((ROOT / "autoprimenet.py").read_bytes()).hexdigest(), BASELINE_SHA256)


if __name__ == "__main__":
	unittest.main()
