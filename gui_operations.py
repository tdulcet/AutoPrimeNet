"""Allowlisted one-shot operations exposed by the graphical interface.

Copyright (C) 2026 Jacob Pollicove
SPDX-License-Identifier: GPL-3.0-only
"""

from dataclasses import dataclass


@dataclass(frozen=True)
class Operation:
	title: str
	tab: str
	flags: tuple[str, ...]
	destination: str
	effects: str


OPERATIONS = {
	"ping": Operation("Ping PrimeNet", "PrimeNet", ("--ping",), "ping", "Contact PrimeNet and write the server response/version information to the AutoPrimeNet log."),
	"test_email": Operation("Send test email", "Notifications", ("--test-email",), "test_email", "Send the original backend's test message to the configured email recipients. It may include computer/account details. SMTP acceptance does not prove recipient delivery."),
	"report_results": Operation("Report results", "Assignments", ("--report-results",), "results", "Submit pending results from all configured workers. This can update result files, local state and assignment reservations, and send configured notifications."),
	"upload_proofs": Operation("Report results and upload proofs", "Assignments", ("--upload-proofs",), "proofs", "Submit results from all configured workers, then upload available PRP proofs. Successfully uploaded proofs can be archived or deleted according to the existing configuration. This can update local state and assignment reservations and send notifications."),
}


def operation_for_destination(destination):
	return next((key for key, operation in OPERATIONS.items() if operation.destination == destination), None)
