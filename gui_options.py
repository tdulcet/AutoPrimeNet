"""Typed metadata and validation for graphical configuration forms.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

from dataclasses import dataclass
import math
from pathlib import Path


@dataclass(frozen=True)
class Field:
	key: str
	label: str
	tab: str
	default: str = ""
	kind: str = "text"
	minimum: float | None = None
	maximum: float | None = None
	choices: tuple[str, ...] = ()
	destination: str = ""
	section: str = "PrimeNet"
	option: str = ""
	dialog: str = ""

	@property
	def ini_key(self):
		return self.option or self.key


FIELDS = (
	Field("username", "GIMPS username (or ANONYMOUS)", "PrimeNet"),
	Field("ComputerID", "Computer name (optional)", "PrimeNet"),
	Field("HoursBetweenCheckins", "Progress check-in interval (hours)", "PrimeNet", "1", "integer", 1, 168),
	Field("CPUHours", "Expected computation hours per day", "PrimeNet", "24", "integer", 1, 24),
	Field("CpuBrand", "Processor model (CPU or GPU)", "PrimeNet", destination="cpu_brand", dialog="Hardware"),
	Field("cpu_features", "Processor features", "PrimeNet", dialog="Hardware"),
	Field("CpuSpeed", "Processor frequency (MHz)", "PrimeNet", kind="integer", destination="cpu_speed", dialog="Hardware"),
	Field("memory", "Total physical memory (MiB)", "PrimeNet", kind="integer", dialog="Hardware"),
	Field("Memory", "Maximum stage 2 memory (MiB)", "PrimeNet", kind="integer", destination="day_night_memory", dialog="Hardware"),
	Field("WorkerDiskSpace", "Proof residue disk limit (GiB per worker; 0: omit)", "PrimeNet", kind="decimal", destination="worker_disk_space", dialog="Hardware"),
	Field("L1", "L1 data cache (KiB)", "PrimeNet", kind="integer", destination="cpu_l1_cache_size", dialog="Hardware"),
	Field("L2", "L2 cache (KiB)", "PrimeNet", kind="integer", destination="cpu_l2_cache_size", dialog="Hardware"),
	Field("L3", "L3 cache (KiB)", "PrimeNet", kind="integer", destination="cpu_l3_cache_size", dialog="Hardware"),
	Field("NumCores", "Physical processor cores", "PrimeNet", kind="integer", destination="num_cores", dialog="Hardware"),
	Field("CpuNumHyperthreads", "Threads per core (0: unknown)", "PrimeNet", kind="integer", destination="cpu_hyperthreads", dialog="Hardware"),
	Field("DaysOfWork", "Days of work to queue", "Assignments", "", "decimal", 0, 180),
	Field("num_cache", "Legacy extra assignment cache", "Assignments", "0", "integer", 0),
	Field("work_file", "Work filename", "Settings", "worktodo.txt", "filename"),
	Field("results_file", "Results filename (blank: program default)", "Settings", "", "filename"),
	Field("logfile", "Activity log path", "Settings", "autoprimenet.log"),
	Field("ProofArchiveDir", "Proof archive directory (optional)", "Settings"),
	Field("proxy_type", "Proxy type (blank: http)", "Settings", kind="choice", choices=("", "http", "https", "socks5", "socks5h"), dialog="Connection"),
	Field("ProxyHost", "Proxy server (optional hostname:port)", "Settings", destination="proxy", dialog="Connection"),
	Field("ProxyUser", "Proxy username (optional)", "Settings", destination="proxy_username", dialog="Connection"),
	Field("encrypt", "Backend password encryption policy", "Settings", kind="boolean", dialog="Connection"),
	Field("require_lock", "Require successful native instance locking", "Settings", kind="boolean", destination="lock", dialog="Connection"),
	Field("version_check", "Check for AutoPrimeNet/engine updates", "Settings", kind="boolean", dialog="Behavior"),
	Field("version_check_channel", "Preferred update channel (blank: stable)", "Settings", kind="choice", choices=("", "alpha", "beta", "stable"), dialog="Behavior"),
	Field("color", "Native CLI console color", "Settings", kind="boolean", dialog="Behavior"),
	Field("poll_seconds", "Polling interval (seconds; 0: once)", "Settings", "3600", "integer", 0, 604800, destination="timeout", section="GUI", option="PollSeconds", dialog="Behavior"),
	Field("watch", "Watch results/proof files immediately", "Settings", kind="boolean", dialog="Behavior"),
	Field("debug_level", "Debug verbosity (0–3; 2+: raw trace)", "Settings", "0", kind="choice", choices=("0", "1", "2", "3"), destination="debug", section="GUI", option="DebugLevel", dialog="Behavior"),
	Field("GetMinExponent", "Minimum assignment exponent", "Advanced", "", "integer", 2, 9999999999),
	Field("GetMaxExponent", "Maximum assignment exponent", "Advanced", "", "integer", 2, 9999999999),
	Field("CertWork", "Receive certification work (PRPLL only)", "Advanced", "", "boolean"),
	Field("CertDailyCPULimit", "Certification time limit (%)", "Advanced", "10", "integer", 1, 100),
	Field("min_bit", "Minimum trial-factoring bit level", "Advanced", kind="integer"),
	Field("max_bit", "Maximum trial-factoring bit level", "Advanced", kind="integer"),
	Field("force_target_bits", "Factor to target bit level (depth first)", "Advanced", kind="boolean"),
	Field("tests_saved", "P−1 tests saved / force P−1", "Advanced", kind="decimal"),
	Field("pm1_multiplier", "P−1 retry threshold multiplier", "Advanced", kind="decimal"),
	Field("pm1_bounds", "Optimal P−1 bounds", "Advanced", kind="choice", choices=("", "MIN", "MID", "MAX")),
	Field("ECMBoundsMultiplier", "ECM bounds multiplier", "Advanced", kind="decimal", destination="ecm_multiplier"),
	Field("MaxECMCurves", "Maximum ECM curves", "Advanced", kind="integer", destination="max_ecm_curves"),
	Field("convert_ll_to_prp", "Convert LL assignments to PRP", "Advanced", kind="boolean"),
	Field("convert_prp_to_ll", "Convert PRP assignments to LL", "Advanced", kind="boolean"),
	Field("no_report_100m", "Withhold prime results at ≥100 million digits", "Advanced", kind="boolean"),
	Field("SilentVictory", "Silence the new-prime sound", "Notifications", kind="boolean"),
	Field("notification_send", "Send configured notifications", "Notifications", kind="boolean", section="Email", option="send"),
	Field("from_email", "From email address", "Notifications", destination="fromemail", section="Email"),
	Field("to_emails", "Recipients (comma-separated; blank: sender)", "Notifications", kind="recipients", destination="toemails", section="Email"),
	Field("smtp_server", "SMTP server (optional hostname:port)", "Notifications", destination="smtp", section="Email"),
	Field("email_username", "SMTP username (optional)", "Notifications", section="Email", option="username"),
	Field("tls", "Connect using SSL/TLS", "Notifications", kind="boolean", section="Email"),
	Field("starttls", "Upgrade connection using StartTLS", "Notifications", kind="boolean", section="Email"),
)

# Upstream argparse destinations whose names differ from their INI keys.
DESTINATIONS = {
	"username": "user_id", "ComputerID": "computer_id", "HoursBetweenCheckins": "hours_between_checkins",
	"CPUHours": "cpu_hours", "DaysOfWork": "days_of_work", "ProofArchiveDir": "archive_dir",
	"GetMinExponent": "min_exp", "GetMaxExponent": "max_exp", "CertWork": "cert_work",
	"CertDailyCPULimit": "cert_cpu_limit",
}


def field_for_destination(destination):
	return next((field for field in FIELDS if (field.destination or DESTINATIONS.get(field.key, field.key)) == destination), None)


def validate_fields(values):
	"""Reject malformed graphical input before passing it to the backend."""
	result = {}
	for field in FIELDS:
		value = str(values.get(field.key, field.default)).strip()
		if field.key == "proxy_type":
			value = value.lower()
		if "\n" in value or "\r" in value or "\x00" in value:
			raise ValueError(field.label + ": enter a single-line value.")
		if field.key in {"username", "ComputerID"} and len(value) > 20:
			raise ValueError(field.label + ": maximum 20 characters.")
		if field.key == "username" and not value:
			raise ValueError("A GIMPS username or ANONYMOUS is required.")
		if value and field.kind in {"integer", "decimal"}:
			try:
				number = int(value) if field.kind == "integer" else float(value)
			except ValueError as error:
				raise ValueError(field.label + ": enter a valid number.") from error
			if (isinstance(number, float) and not math.isfinite(number)) or (field.minimum is not None and number < field.minimum) or (field.maximum is not None and number > field.maximum):
				raise ValueError(field.label + ": value is outside the supported range.")
		if value and field.kind == "filename" and (Path(value).name != value or value in {".", ".."}):
			raise ValueError(field.label + ": enter a filename without a directory.")
		if field.kind == "boolean" and value not in {"", "True", "False"}:
			raise ValueError(field.label + ": choose inherit, True or False.")
		if field.kind == "choice" and value not in field.choices:
			raise ValueError(field.label + ": choose one of the listed values.")
		if field.kind == "recipients" and value:
			# The CLI splits this option on commas. Normalize surrounding space,
			# while leaving address syntax validation to its existing parser.
			addresses = [address.strip() for address in value.split(",")]
			if not all(addresses):
				raise ValueError(field.label + ": remove empty recipient entries.")
			value = ",".join(addresses)
		result[field.key] = value or None
	if result["tls"] == result["starttls"] == "True":
		raise ValueError("Choose either SSL/TLS or StartTLS, not both.")
	return result
