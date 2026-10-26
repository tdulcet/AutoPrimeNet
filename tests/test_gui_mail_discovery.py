"""Simulated provider lookups; no live network or SMTP operations.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import contextlib
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch

from gui_config import ConfigDocument
from gui_mail_discovery import discover_mail, execute, mail_settings


class MailDiscoveryTests(unittest.TestCase):
	def test_parent_rejects_malformed_settings_before_tk_receives_them(self):
		from types import SimpleNamespace
		with tempfile.TemporaryDirectory() as directory:
			self.request(directory)
			document = ConfigDocument(directory)
			for match in ([], "provider", {}, {"provider": "P", "security": "SSL", "settings": {}},
				{"provider": "P", "security": "SSL", "settings": {"smtp_server": "host:465", "tls": "False", "starttls": "False"}},
				{"provider": "P", "security": "SSL", "settings": {"smtp_server": "host:465", "tls": "True", "starttls": "False", "unexpected": "value"}}):
				with self.subTest(match=match), patch("gui_mail_discovery.subprocess.run", return_value=SimpleNamespace(
					returncode=0, stdout=json.dumps({"protocol": 1, "ok": True, "result": {"match": match}}))):
					with self.assertRaisesRegex(ValueError, "invalid settings"):
						discover_mail(document, "user@example.com")
			for match in (None, mail_settings(("P", "host", 465, "SSL", None))):
				with patch("gui_mail_discovery.subprocess.run", return_value=SimpleNamespace(
					returncode=0, stdout=json.dumps({"protocol": 1, "ok": True, "result": {"match": match}}))):
					self.assertEqual(discover_mail(document, "user@example.com")["match"], match)
	def request(self, directory):
		path = Path(directory) / "prime.ini"
		path.write_text("[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\nProxyHost=proxy.example:8080\nProxyUser=fixture\nProxyPass=secret\n")
		return {"protocol": 1, "operation": "discover_mail", "directory": directory, "config_name": "prime.ini", "config_sha256": hashlib.sha256(path.read_bytes()).hexdigest(), "email": "user@example.com"}

	def run_execute(self, request, callback):
		with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
			return execute(request, callback)

	def test_security_modes_and_unknown_username(self):
		for security, tls, starttls in (("SSL", "True", "False"), ("STARTTLS", "False", "True"), ("plain", "False", "False")):
			with self.subTest(security=security):
				result = mail_settings(("Provider", "smtp.example.com", 465, security, None))
				self.assertEqual(result["settings"], {"smtp_server": "smtp.example.com:465", "tls": tls, "starttls": starttls})

	def test_invalid_provider_fields_are_rejected(self):
		for record in ([], ("P", "bad\nhost", 465, "SSL", None), ("P", "host", 0, "SSL", None), ("P", "host", 465, "unknown", None), ("P", "host", 465, "SSL", "user\nsecret")):
			with self.subTest(record=record), self.assertRaises(ValueError):
				mail_settings(record)

	def test_original_provider_xml_lookup_uses_saved_proxy_without_writes(self):
		with tempfile.TemporaryDirectory() as directory:
			request = self.request(directory)
			original = (Path(directory) / "prime.ini").read_bytes()
			def simulate(namespace):
				self.assertEqual(namespace["PROXIES"], {"http": "http://fixture:secret@proxy.example:8080", "https": "http://fixture:secret@proxy.example:8080"})
				self.assertEqual(namespace["TIMEOUT"], 8)
				response = Mock()
				response.content = b'<clientConfig><emailProvider id="Fixture"><displayName>Fixture Mail</displayName><outgoingServer type="smtp"><hostname>smtp.example.com</hostname><port>587</port><socketType>STARTTLS</socketType><username>%EMAILADDRESS%</username></outgoingServer></emailProvider></clientConfig>'
				response.url = "https://autoconfig.example.com/mail/config-v1.1.xml"
				response.history = []
				client = Mock()
				client.get.return_value = response
				manager = Mock()
				manager.__enter__ = Mock(return_value=client)
				manager.__exit__ = Mock(return_value=False)
				# Patch only HTTP transport; run the original provider parser and lookup.
				mock = patch.object(namespace["requests"], "Session", return_value=manager)
				mock.start()
				self.addCleanup(mock.stop)
			result = self.run_execute(request, simulate)
			self.assertEqual(result["match"]["settings"]["email_username"], "user@example.com")
			self.assertEqual(result["match"]["settings"]["starttls"], "True")
			self.assertFalse(result["email_sent"])
			self.assertFalse(result["files_written"])
			self.assertEqual((Path(directory) / "prime.ini").read_bytes(), original)
			self.assertEqual([p.name for p in Path(directory).iterdir()], ["prime.ini"])

	def test_no_match_and_configuration_change(self):
		with tempfile.TemporaryDirectory() as directory:
			request = self.request(directory)
			result = self.run_execute(request, lambda ns: ns.update(email_autoconfig=lambda args, email: None))
			self.assertIsNone(result["match"])
			def mutate(namespace):
				def lookup(args, email):
					with (Path(directory) / "prime.ini").open("a") as stream:
						stream.write("; changed\n")
					return None
				namespace["email_autoconfig"] = lookup
			with self.assertRaisesRegex(ValueError, "changed during"):
				self.run_execute(request, mutate)

	def test_original_dns_srv_fallback_uses_original_record_selection(self):
		with tempfile.TemporaryDirectory() as directory:
			request = self.request(directory)
			lookups = []
			def simulate(namespace):
				namespace["get_email_config"] = lambda *args, **kwargs: None
				def dns(args, domain, kind):
					lookups.append((domain, kind))
					if kind == "MX":
						return {"Status": 0}
					return {"Status": 0, "Question": [{"type": 33}], "Answer": [{"type": 33, "data": "10 1 465 smtp.example.com."}], "AD": True}
				namespace["dns_lookup"] = dns
			result = self.run_execute(request, simulate)
			self.assertEqual(lookups, [("example.com", "MX"), ("_submissions._tcp.example.com", "SRV")])
			self.assertEqual(result["match"]["settings"]["smtp_server"], "smtp.example.com:465")
			self.assertEqual(result["match"]["settings"]["tls"], "True")
			self.assertNotIn("email_username", result["match"]["settings"])

	def test_stale_and_invalid_requests_never_start_network_discovery(self):
		with tempfile.TemporaryDirectory() as directory:
			request = self.request(directory)
			for changes in ({"config_sha256": "stale"}, {"email": "bad\naddress"}, {"operation": "send_email"}):
				with self.subTest(changes=changes), patch("gui_mail_discovery._load_definitions") as load, self.assertRaises(ValueError):
					self.run_execute(dict(request, **changes), None)
				load.assert_not_called()

	def test_parent_timeout_is_bounded_and_stdin_carries_request(self):
		with tempfile.TemporaryDirectory() as directory:
			self.request(directory)
			document = ConfigDocument(directory)
			with patch("gui_mail_discovery.subprocess.run", side_effect=subprocess.TimeoutExpired("helper", 90)) as run:
				with self.assertRaisesRegex(ValueError, "90 seconds"):
					discover_mail(document, "user@example.com")
				self.assertEqual(run.call_args.kwargs["timeout"], 90)
				self.assertNotIn("user@example.com", str(run.call_args.args))
				self.assertEqual(json.loads(run.call_args.kwargs["input"])["email"], "user@example.com")

	def test_invalid_ipc_failure_is_sanitized_and_offline_bridge_rejects_operation(self):
		root = Path(__file__).resolve().parents[1]
		for helper in ("gui_mail_discovery.py", "gui_backend.py"):
			process = subprocess.run([sys.executable, "-B", str(root / helper)], input=json.dumps({"protocol": 1, "operation": "discover_mail", "email": "private\nsecret"}), capture_output=True, text=True, timeout=30)
			response = json.loads(process.stdout)
			self.assertFalse(response["ok"])
			self.assertNotIn("secret", process.stdout + process.stderr)
