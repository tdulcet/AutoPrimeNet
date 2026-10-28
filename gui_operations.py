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
	confirmation: str = ""
	backup_work: bool = False
	requires_exponent: bool = False


OPERATIONS = {
	"push_status": Operation("Push Status to PrimeNet Now", "Dashboard", (), "push_status", "Run a complete AutoPrimeNet communication pass with progress reporting now. This also reports results, handles proofs and requests work according to the saved configuration. Reports the latest engine progress written to disk; it does not force a computation checkpoint."),
	"ping": Operation("Ping PrimeNet", "PrimeNet", ("--ping",), "ping", "Contact PrimeNet and write the server response/version information to the AutoPrimeNet log."),
	"ping_v6": Operation("Ping experimental v6 API", "PrimeNet", ("--ping", "--v6"), "v6", "Contact the experimental PrimeNet v6 ping endpoint and log its response. This does not switch normal assignment operations to v6."),
	"register_computer": Operation("Register or update computer", "PrimeNet", ("--setup",), "setup", "Register/update this computer and synchronize its program options using saved graphical settings. The graphical adapter skips terminal setup and does not request assignments or automatically send a test email."),
	"register_exponents": Operation("Register exponent batch", "Assignments", ("--register-exponents",), "register_exponents", "Append the validated batch to the selected worker's work file, then use the original registration workflow. This ALSO registers other unregistered assignments already in that worker's work file and may rewrite work lines using configured conversion/factoring settings. Pause the affected computation engine first.", "REGISTER", True),
	"test_email": Operation("Send test email", "Notifications", ("--test-email",), "test_email", "Send the original backend's test message to the configured email recipients. It may include computer/account details. SMTP acceptance does not prove recipient delivery."),
	"status": Operation("Write work status to backend log", "Logs & Status", ("--status",), "status", "Write the original queued-work/estimated-completion report to the AutoPrimeNet log. Reads computation progress files and can normalize configuration during CLI startup. This command does not request assignments or submit results."),
	"report_results": Operation("Report results", "Assignments", ("--report-results",), "results", "Submit pending results from all configured workers. This can update result files, local state and assignment reservations, and send configured notifications."),
	"upload_proofs": Operation("Report results and upload proofs", "Assignments", ("--upload-proofs",), "proofs", "Submit results from all configured workers, then upload available PRP proofs. Successfully uploaded proofs can be archived or deleted according to the existing configuration. This can update local state and assignment reservations and send notifications."),
	"no_more_work": Operation("Pause new-work requests", "Assignments", ("--no-more-work",), "no_more_work", "Set QuitGIMPS locally so future AutoPrimeNet cycles stop requesting new assignments. Existing computation and reservations continue; this does not stop monitoring."),
	"resume_work": Operation("Resume new-work requests", "Assignments", ("--resume-work",), "resume_work", "Remove the local QuitGIMPS override. Future monitoring cycles may request new assignments. This command itself does not request new work."),
	"recover": Operation("Recover assignments", "Assignments", ("--recover",), "recover", "Report pending results, recover outstanding assignments and OVERWRITE configured work/certification files for all workers. Pause affected computation engines first. Result/state changes and notifications may also occur.", "RECOVER", True),
	"recover_all": Operation("Recover all assignments", "Assignments", ("--recover-all",), "recover_all", "Report results and OVERWRITE configured work/certification files, including expired PrimeNet assignments. TF1G recovery can collect assignments from all systems/workers into the first worker. Pause affected computation engines first.", "RECOVER ALL", True),
	"unreserve": Operation("Unreserve an exponent", "Assignments", ("--unreserve",), "exponent", "Release the specified reservation and remove its assignment from a work file. Only do this when you will not finish that assignment. The CLI acts on the FIRST matching exponent across workers, not a selected worker or AID. Pause affected computation engines first.", "UNRESERVE", True, True),
	"unreserve_all": Operation("Unreserve all assignments", "Assignments", ("--unreserve-all",), "unreserve_all", "Report pending results and RELEASE ALL reservations represented in the configured workers. TF1G can release all assignments associated with a worker. Remove successfully released assignments from work files. Pause affected computation engines first.", "UNRESERVE ALL", True),
}


def operation_arguments(key, parameters=None):
	if key not in OPERATIONS:
		raise ValueError("Unsupported one-shot operation.")
	parameters = {} if parameters is None else parameters
	if not isinstance(parameters, dict):
		raise ValueError("Operation parameters must be a dictionary.")
	operation = OPERATIONS[key]
	if key == "register_exponents":
		from gui_registration_plan import validate_shape
		validate_shape(parameters)
		return operation.flags
	if operation.requires_exponent:
		value = parameters.get("exponent")
		if set(parameters) != {"exponent"} or type(value) is not int or not 2 <= value <= 9999999999:
			raise ValueError("Enter an exponent between 2 and 9,999,999,999.")
		return (*operation.flags, str(value))
	if parameters:
		raise ValueError("This operation does not accept parameters.")
	return operation.flags


def operation_for_destination(destination):
	return next((key for key, operation in OPERATIONS.items() if operation.destination == destination), None)
