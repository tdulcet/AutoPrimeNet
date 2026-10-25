"""Offline password persistence tests, using disposable credentials only.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from gui_config import ConfigDocument, WorkspaceError, save_configuration
from gui_controller import ControllerError, backend_request


BASE = "[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\nProxyHost=localhost:8080\n[Email]\nfrom_email=sender@example.org\nsmtp_server=localhost\n"
WORKERS = [{"directory": "", "preference": ""}]


def save(document, credentials, **fields):
	return save_configuration(document, document.values() | fields, "mlucas", WORKERS, credentials)


class CredentialTests(unittest.TestCase):
	def protected_save(self, document, credentials, **fields):
		try:
			return save(document, credentials, **fields)
		except ControllerError as error:
			if "OpenSSL encryption is unavailable" in str(error):
				self.skipTest("Native OpenSSL encryption unavailable")
			raise

	def test_encrypted_replacements_decrypt_exactly_and_never_reach_argv(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text(BASE)
			secrets = {"email": "  mail%fixture password  ", "proxy": "proxy-fixture-password"}
			with patch("gui_controller.subprocess.run", wraps=subprocess.run) as run:
				result = self.protected_save(ConfigDocument(directory), secrets)
				for call in run.call_args_list:
					for secret in secrets.values():
						self.assertNotIn(secret, " ".join(call.args[0]))
			text = path.read_text()
			for secret in secrets.values():
				self.assertNotIn(secret, text)
			self.assertIn("encrypted_password=", text)
			self.assertIn("encrypted_ProxyPass=", text)
			self.assertTrue(result["document"].config.has_option("PrimeNet", "HardwareGUID"))
			# Read the exact saved ciphertext using the original decrypt function;
			# only hashes leave this test child, with its socket guard active.
			code = """import gui_backend as b, sys, json, hashlib
from pathlib import Path
sys.addaudithook(b._network_guard)
p = Path('autoprimenet.py').resolve()
_, tree, boundary = b._read_source(p)
ns = b._load_definitions(p, tree, boundary)
b._validate_config(ns, tree, boundary, {'text': Path(sys.argv[1], 'prime.ini').read_text(), 'directory': sys.argv[1]})
print(json.dumps({key: hashlib.sha256(getattr(ns['args'], attr).encode()).hexdigest() for key, attr in [('email', 'email_password'), ('proxy', 'proxy_password')]}))
ns['session'].close()
"""
			process = subprocess.run([sys.executable, "-B", "-c", code, directory], capture_output=True, text=True, timeout=30)
			self.assertEqual(process.returncode, 0, process.stderr)
			self.assertEqual(json.loads(process.stdout), {key: hashlib.sha256(secret.encode()).hexdigest() for key, secret in secrets.items()})
			for secret in secrets.values():
				self.assertNotIn(secret, process.stdout + process.stderr)

	def test_replace_preserves_unselected_ciphertext_and_existing_guid(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text(BASE)
			first = self.protected_save(ConfigDocument(directory), {"email": "mail-before", "proxy": "proxy-unchanged"})["document"]
			second = self.protected_save(first, {"email": "mail-after"})["document"]
			self.assertEqual(first.config.get("PrimeNet", "encrypted_ProxyPass"), second.config.get("PrimeNet", "encrypted_ProxyPass"))
			self.assertEqual(first.config.get("PrimeNet", "HardwareGUID"), second.config.get("PrimeNet", "HardwareGUID"))
			self.assertNotEqual(first.config.get("Email", "encrypted_password"), second.config.get("Email", "encrypted_password"))
			self.assertIsNone(save(second, {})["backup"])

	def test_remove_corrupt_password_without_decrypting_it(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text(BASE + "encrypted_password=corrupt\npassword=old-fixture\nCustom=keep\n")
			original = path.read_bytes()
			result = save(ConfigDocument(directory), {"email": None})
			self.assertNotIn("password=", path.read_text())
			self.assertIn("Custom=keep", path.read_text())
			self.assertEqual(Path(result["backup"]).read_bytes(), original)

	def test_encryption_disabled_or_unavailable_never_replaces_file(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text(BASE)
			document = ConfigDocument(directory)
			with self.assertRaisesRegex(ControllerError, "Enable password encryption"):
				save(document, {"email": "fixture-secret"}, encrypt="False")
			with patch("gui_config.backend_request", side_effect=ControllerError("OpenSSL encryption is unavailable")):
				with self.assertRaises(ControllerError):
					save(document, {"email": "fixture-secret"})
			self.assertEqual(path.read_bytes(), document.data)
			self.assertFalse(list(Path(directory).glob("*.bak")))

	def test_invalid_password_and_inherited_password_refused(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			path.write_text(BASE)
			document = ConfigDocument(directory)
			for changes in ({"email": ""}, {"email": "bad\nfixture"}, {"unknown": "fixture"}, {"proxy": "a" * 4097}):
				with self.subTest(keys=list(changes)), self.assertRaises(WorkspaceError):
					save(document, changes)
			self.assertEqual(path.read_bytes(), document.data)
			path.write_text("[DEFAULT]\npassword=inherited-fixture\n" + BASE)
			with self.assertRaisesRegex(WorkspaceError, "Inherited passwords"):
				save(ConfigDocument(directory), {"email": None})

	def test_backend_redacts_new_password_on_validation_error(self):
		with tempfile.TemporaryDirectory() as directory:
			secret = "unique-fixture-secret"
			try:
				backend_request("protect_credentials", text="[PrimeNet]\nusername=ANONYMOUS\nmlucas=True\n", directory=directory, credentials={"proxy": secret})
			except ControllerError as error:
				self.assertNotIn(secret, str(error))
			else:
				self.fail("A proxy password without a proxy server must be rejected")
			self.assertEqual(list(Path(directory).iterdir()), [])

	def test_native_encryption_failure_is_sanitized_without_plaintext_output(self):
		with tempfile.TemporaryDirectory() as directory:
			secret = "native-encryption-failure-fixture"
			code = """import gui_backend as b, sys
load = b._load_definitions
def failing_load(*args):
    ns = load(*args)
    def fail(*args):
        raise RuntimeError('native-encryption-failure-fixture')
    ns['encrypt'] = fail
    return ns
b._load_definitions = failing_load
sys.exit(b.main())
"""
			process = subprocess.run([sys.executable, "-B", "-c", code], input=json.dumps(dict(protocol=1, operation="protect_credentials", text=BASE, directory=directory, credentials={"email": secret})), capture_output=True, text=True, timeout=30)
			self.assertEqual(process.returncode, 1)
			response = json.loads(process.stdout)
			self.assertFalse(response["ok"])
			self.assertNotIn(secret, process.stdout + process.stderr)
			self.assertEqual(process.stderr, "")
			self.assertEqual(list(Path(directory).iterdir()), [])

	def test_existing_proxy_spelling_is_preserved_on_noop_save(self):
		with tempfile.TemporaryDirectory() as directory:
			path = Path(directory) / "prime.ini"
			original = BASE.replace("ProxyHost=localhost:8080", "ProxyHost=localhost:8080\nproxy_type=HTTP\nencrypt=yes")
			path.write_text(original)
			result = save(ConfigDocument(directory), {}, encrypt="True")
			self.assertIsNone(result["backup"])
			self.assertEqual(path.read_text(), original)


if __name__ == "__main__":
	unittest.main()
