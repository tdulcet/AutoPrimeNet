# GUI development and validation

This document records architecture and validation evidence for the optional
Python 3.15.0-or-later GUI. See [GUI.md](GUI.md) for installation and usage and
[GUI_PARITY.md](GUI_PARITY.md) for the audited parser-entry inventory.

## Current status

The 94 ordinary CLI parser entries have graphical controls within the documented
limits. Configuration saving, encrypted password replacement, native monitoring,
watching, one-shot operations, registration, discovery and private reports are
implemented. This inventory is not release acceptance: exact Python 3.15.0,
other operating systems and controlled live-service workflows remain unverified.

Milestone sections below are **historical records**, ordered by implementation.
Their earlier counts and statements about unfinished features describe that
milestone, not the current application. The final review section records the
latest checks.

## Milestone: environment and offline backend prototype

Validated on October 24, 2026 on the development Apple Silicon macOS machine:

| Component | Observed version/result |
| --- | --- |
| Homebrew Python / `.venv` interpreter | 3.15.1 |
| Native Tcl and Tk | 9.1.0 |
| Requests | 2.34.2 |
| urllib3 | 2.8.0 |
| certifi | 2026.10.23 |
| charset-normalizer | 3.5.2 |
| idna | 3.20 |
| `python -m pip check` | No broken requirements |
| Tk window smoke check | A real ttk window mapped, processed events, and closed successfully |
| Offline prototype suite | 10 tests passed |
| Existing CLI smoke checks | `autoprimenet.py --help` and `gimps_status.py --help` both passed |

Homebrew installed `python-tk@3.15` and its native `tcl-tk` and `libtommath`
dependencies. Requests and its dependencies were installed only inside `.venv`.
The graphical smoke check aborted inside the restricted tool sandbox; it passed
when run with access to the macOS graphical session. That first failure was not
treated as a successful GUI test.

Python 3.15.0 itself has not been runtime-tested. Windows, Linux, FreeBSD, tray
integration, and the full GUI have not been tested. Tested dependency versions
above are evidence from one environment, not cross-platform pins or a lockfile.

## Offline bridge

`gui_backend.py` is a short-lived private child process. It accepts one
JSON request on standard input and returns one JSON response on standard output.
Its offline operation allowlist is:

* `capabilities`: reads the audited parser inventory without executing upstream
  definitions or startup. Includes hidden/inverse flags and automatic help.
* `parse_work`: executes the reviewed upstream definition prefix in a private
  namespace, then reuses `parse_assignment()` and `output_assignment()` to inspect
  supplied work lines. It does not open the user's work files.
* `validate_config`: initializes the existing argument parser and merges proposed
  configuration text in memory, reuses decryption and `check_options()`, and
  returns only non-secret effective settings. It does not write configuration,
  acquire locks, run prompted setup, register the computer or enter the scheduler.
* `protect_credentials`: validates configuration offline and strictly encrypts
  explicit SMTP/proxy password replacements using the original backend. Returns
  only selected ciphertext and the hardware GUID needed to retain its binding.
  It does not write files; the existing save layer patches and validates the
  result before atomic replacement.
* `preview_registration`: supplies validated form answers to the original
  exponent-registration function using in-memory files and no-op registration.
  It returns canonical work lines without writing files or making a lookup.
* `debug_report`: captures the original diagnostic function offline, redacts
  configured passwords, and returns explicitly private report text. Export
  requires a separate GUI confirmation and creates an owner-private local file.
* `cli_help`: builds the original parser and returns its visible help without a
  configuration or CLI startup. Capabilities also include the audited version.
* `discover_gpus`: reuses local GPU discovery and returns reviewed hardware form
  values without server access or runtime-file writes. SMTP discovery uses its
  separate network-enabled helper rather than this offline bridge.

The source SHA-256 must exactly match the reviewed backend. Source drift fails
closed before execution. An update to that guard requires a new integration
review, not just replacing the hash. No copy of the PrimeNet parser, serializer,
or API implementation is maintained by the bridge.

The executed prefix initializes native capabilities, locale, and an HTTP session;
it is therefore isolated from the Tk process. Normal CLI startup, disk-based
configuration loading, instance locking, file logging, prompted setup and the
scheduler are not executed. Configuration validation initializes the parser and
configuration in memory only. The bridge explicitly closes its session afterward.

Python socket audit guards deny DNS resolution, connections, and datagram sends
for these offline operations. This is a precaution around trusted, hash-checked
upstream code, not a general security sandbox for arbitrary code. No mutation or
server-operation request is accepted. Diagnostics are suppressed and failure
responses are sanitized to avoid reflecting secrets or corrupting the JSON stream.

Parsing is not mathematical validation or reservation confirmation. Even a line
with an AID is returned with `server_confirmation: "unverified"`.

## Running the tests

From the repository root, after following the environment setup in GUI.md:

```sh
.venv/bin/python -B -m unittest discover -s tests -p 'test_gui_*.py' -v
.venv/bin/python -m pip check
```

On Windows PowerShell:

```powershell
.\.venv\Scripts\python.exe -B -m unittest discover -s tests -p 'test_gui_*.py' -v
.\.venv\Scripts\python.exe -m pip check
```

The default suite skips tests that initialize a native graphical session. To
include all desktop and native watcher checks, run from a logged-in desktop:

```sh
AUTOPRIMENET_GUI_DESKTOP_TESTS=1 .venv/bin/python -B -m unittest discover -s tests -p 'test_gui_*.py' -v
```

Windows PowerShell:

```powershell
$env:AUTOPRIMENET_GUI_DESKTOP_TESTS = '1'
.\.venv\Scripts\python.exe -B -m unittest discover -s tests -p 'test_gui_*.py' -v
Remove-Item Env:AUTOPRIMENET_GUI_DESKTOP_TESTS
```

Native macOS/Windows tray tests require `requirements-gui-tray.txt`; they report
an explicit skip when those optional packages are absent. With packages installed,
a native tray startup failure fails the test. Linux/FreeBSD tray-host tests use
simulated GI/D-Bus backends; actual panel/desktop acceptance remains manual.

For an optional static bug-pattern check with Ruff installed separately, run on
macOS/Linux/FreeBSD:

```sh
ruff check --isolated --target-version py315 --select F,B,PLE autoprimenet_gui.py gui_*.py tests/test_gui_*.py
```

This deliberately ignores repository-wide configuration and checks only the GUI
additions. It does not change the upstream Python compatibility/lint targets.
Ruff and coverage tooling are review/development tools, not GUI runtime or
standard-library test-suite requirements.

The standard-library tests launch the bridge in isolated child processes. They
cover parser inventory, the ten work-file formats, canonical round trips,
unverified AIDs, malformed/multiline input, protocol/action rejection, source
drift, sanitized JSON errors, blocked network access, absence of generated
runtime files, and byte preservation of the upstream backend. No GIMPS account,
real assignments, live server, or test email is used.

In VSCode, use **Python: Select Interpreter** from the Command Palette and select
the repository's `.venv/bin/python` (Windows: `.venv\Scripts\python.exe`). The
repository does not require a committed VSCode settings file. The commands above
also work without activating the environment because they use its executable
directly.

The initial milestone was evidence for read-only helper reuse only. It did not establish correct
configuration precedence, encryption, lock coordination, registration, selective
server actions, process shutdown, or scheduler integration. Those require later
tests before exposing them in the GUI.

## Milestone: read-only desktop foundation and native tray helper

The new `autoprimenet_gui.py` launcher provides eight tabs, directory/configuration
selection, local identity/worker/disk/assignment previews, GUI activity, and a
searchable CLI reference. `gui_config.py` reads bounded, case-sensitive snapshots
without writing or decrypting. `gui_controller.py` serializes background jobs,
uses timeout-bounded private backend requests, and owns the tray helper process.

`gui_tray.py` uses pystray in a separate process to keep its native event loop
independent of Tk. The optional dependency file resolves to pystray 0.19.5,
Pillow 13.0.0, six 1.17.0 and PyObjC core/Cocoa/Quartz 12.2.2 on the development
Mac. All were installed inside `.venv`. Runtime readiness is established before
withdrawing the window; helper failure restores a hidden window. Taskbar/Dock
minimization is the fallback. Linux/FreeBSD tray integration is not enabled yet.

Validation on the same macOS/Python 3.15.1/Tk 9.1 environment:

* 18 core tests passed: the previous 10, plus read-only configuration/worker
  discovery, symlink conflict detection, PRPLL indexed files, exclusion of secret
  settings from snapshots, invalid values/paths, bounded request size, job
  serialization, and backend failure reporting.
* Five opt-in real-desktop tests passed: tab navigation/search/workspace loading
  and repeated refresh, tray hide/programmatic restore/helper failure recovery,
  reachable taskbar/Dock fallback without tray support, clean shutdown of a healthy
  tray helper, and macOS native Quit dispatch through application cleanup.
* The user confirmed the requested manual macOS menu-bar test passed on October
  24, 2026: closing the window, reopening it through the menu-bar icon, and Quit.
  This supplements the programmatic event-delivery checks above.

Run the desktop tests only in an accessible graphical session. On macOS:

```sh
AUTOPRIMENET_GUI_DESKTOP_TESTS=1 .venv/bin/python -B -m unittest discover -s tests -p 'test_gui_window.py' -v
```

On Windows PowerShell:

```powershell
$env:AUTOPRIMENET_GUI_DESKTOP_TESTS = '1'
.\.venv\Scripts\python.exe -B -m unittest discover -s tests -p 'test_gui_window.py' -v
Remove-Item Env:AUTOPRIMENET_GUI_DESKTOP_TESTS
```

The default suite skips desktop tests to avoid initializing Tk in headless or
restricted sessions. The earlier crash report confirms SIGABRT during macOS
application registration, with `TkMacOSXDisplayChanged` / `TkpOpenDisplay` in the
stack. This is consistent with the restricted-session failure, not proof of a
defect in application logic; subsequent desktop-access tests passed. Do not run
graphical checks in the same restricted context that caused that abort.

No monitoring, server mutation, notification delivery, configuration persistence,
or engine management is available in this milestone. Full initialization parity,
editable forms and process safety for an actual monitoring backend remain work
for later milestones. No live PrimeNet operations were performed.

## Milestone: configuration forms, safe persistence and offline initialization

Validated October 25, 2026 on macOS with Python 3.15.1 and Tk 9.1.0: **46 tests
passed**, comprising 39 core tests and seven opt-in desktop tests. No tests were
skipped in that combined desktop-enabled run. The dependency check also passed.
No new dependencies were required for this milestone.

`gui_options.py` defines typed metadata for the first fourteen configuration
fields. `gui_forms.py` presents them in the main tabs and adds program selection,
worker-count editing and a per-worker dialog. Saving is an explicit user action;
unsaved changes can be retained when cancelling reload or Quit. Forms and path
selectors are disabled during background operations to prevent competing edits.

`gui_config.py` now retains a loaded version fingerprint and patches only changed
single-line keys. It preserves comments, BOM/CRLF, unknown keys/sections,
untouched interpolation and ciphertext. New literals escape percent signs. It
uses the CLI-compatible instance lock, checks for external edits, writes a
private backup, flushes a same-directory temporary file, and atomically replaces
the target. Read-only/symbolic-link targets and known live-data filename conflicts
are refused. No-op saves preserve exact bytes without a backup. Old worker
sections remain when reducing the active count; program/hours changes reset the
same cached estimate keys as setup.

Offline validation executes the reviewed source's parser declarations and reuses
`merge_config_and_options()`, `decrypt()` and `check_options()`. It resolves
program-dependent defaults and support sets without running the CLI startup
block or scheduler. Python 3.15's lazy-import bindings required using the bridge's
standard-library ConfigParser rather than directly calling a potentially
unresolved dictionary binding. The audited upstream source itself was unchanged.

New verification covers:

* Effective defaults for all eight computation programs, and comparison of
  key effective values with the normal CLI's status path in a disposable
  workspace under a network-blocking audit hook.
* Real upstream OpenSSL encryption/decryption using a synthetic proxy password;
  an unrelated edit retains ciphertext and the original backup without storing
  the decrypted value. A separate fake-ciphertext formatting test mocks validation
  explicitly and is not counted as evidence of decryption.
* Initial creation, private-file modes, backups, comments/unknown/multiline
  preservation, literal percent paths, multiple workers and preferences,
  external edits (including restored mtime), lock contention, read-only files,
  failed replacement, temp cleanup, invalid input and engine-change resets.
* Real Tk interaction through the application methods for invalid input,
  successful save/reload, unsaved-change cancellation, and all prior tray tests.

The atomic rename is not a compare-and-swap against unrelated editors that ignore
the shared lock. Avoid concurrent writers; narrow races with such editors remain
possible after the final version check. Extended ACL/xattr preservation, network
filesystems, Windows/FreeBSD/Linux execution and Python 3.15.0 runtime validation
remain untested. Multiline values being edited are deliberately refused. Full
credential editing, registration, network initialization/proxy setup, monitoring,
selective server operations, notifications and complete graphical parity remain
later work. No live PrimeNet operations or real assignment changes occurred.

## Milestone: scheduled monitoring lifecycle

Validated October 25, 2026 on the same macOS/Python 3.15.1/Tk 9.1.0 environment:
**59 tests passed**, comprising 51 core tests and eight real-desktop tests. All
monitoring cycles in these tests are simulated or replaced with owned sleeping
test children; no live PrimeNet cycle, assignment change or notification send was
performed. The older CLI status comparison remains network-blocked.

`gui_monitor.py` is a private scheduled runner. It validates the selected
configuration offline, holds `~gui-monitor.lock`, and runs unmodified CLI passes
with `--timeout 0` at the configured check-in interval. This avoids leaving
daemon proof/result workers active when stopping at a cycle boundary. It is a
scheduled mode only, not implementation of native immediate file watching or
independent polling/check-in cadences. A completed initial registration can be
followed by a normal work pass; tests verify this glue with stubbed subprocesses,
not real registration.

Each Start preserves a private, byte-for-byte configuration backup before the
CLI can normalize the file. Tests verify the backup contents and POSIX private
file permissions. This backup does not undo server operations or checkpoints.

`MonitorController` owns the helper process, serialized control writes, lifecycle
events and restart generations. A ready/begin handshake prevents a Stop during
offline preflight from starting a server cycle afterward. The helper reads control
commands without buffered stdin read-ahead or buffered-reader shutdown locks.
Parent-pipe EOF requests a graceful stop. A confirmed force-stop command targets
only the CLI child created by this helper. No process discovery, arbitrary PID
killing, unreservation, or automatic stale-lock removal is implemented.

Dashboard Start/Stop/Force controls are integrated with tray state and start/stop
menu actions. Closing retains the GUI/runner; confirmed Quit waits asynchronously
for shutdown. Settings/path editing is disabled while monitoring, and the save
layer independently checks the runner lock. The CLI's native lock protects every
pass against independent CLI processes; the GUI-only lock does not prevent an
independent CLI from starting during a scheduled idle interval. A subsequent
native lock conflict stops the runner rather than killing the foreign process.

New tests cover duplicate starts/runners, native lock conflicts, changed config,
save exclusion, startup cancellation, idle/running-cycle Stop, parent EOF,
nonzero-cycle failure, initialization follow-up, private argv, and forced stopping
of an owned test child while an unrelated test process remains alive. The real
desktop test hides the window to the actual macOS menu-bar helper while a
simulated runner remains active, then tests cancelled and confirmed Quit.

Tray state updates/activation/shutdown now use PyObjC's native main-thread
dispatch on macOS; the Tk event loop remains in the GUI process. No new package
dependencies were needed. Native menu clicks for the new Start/Stop actions have
not been manually tested, and Windows/Linux/FreeBSD and Python 3.15.0 runtime
validation remain pending.

CLI stdout/stderr is not streamed into the GUI, avoiding pipe backpressure and
credential exposure. Detailed diagnostics remain in the existing rotating CLI
log; GUI cycle events are bounded and explicitly do not confirm server acceptance.
Long uploads, retries, or stale sidecar locks can delay graceful Stop. Force-stop
risks and scheduled-mode limitations are documented in GUI.md. The next work is
complete graphical operation coverage, immediate-watch lifecycle and safe live
validation after review; this milestone does not establish full parity.

## Milestone: advanced assignment configuration

Added ten graphical settings for trial-factoring bit limits and target bits,
P−1 tests saved/retry multiplier/optimal bounds, ECM bounds/curve limits, and
LL/PRP conversion directions. Existing exponent and certification controls now
share a scrollable Advanced dialog. Dialog edits are staged separately: Cancel
discards them, Apply updates the main form, and Save uses the existing offline
backend and atomic persistence path. Applying while monitoring or local work is
active is refused. Mutually exclusive conversions are rejected in the dialog
and again by the original backend at save time. No new ranges beyond the
original backend's rules were imposed on the added numeric options.

The CLI reference maps all current configuration fields to their tab and label,
searches those labels, and supports double-click/Return navigation. Mapped
advanced rows open and focus the relevant control; unmapped entries remain
reference-only. This does not establish complete CLI parity.

Validated October 25, 2026 on macOS/Python 3.15.1/Tk 9.1.0: **62 tests passed**,
including nine desktop tests. Added tests round-trip the new settings through
the real offline backend, verify conflicting/invalid settings cannot alter the
file or create backups, and exercise dialog cancellation, application, reference
navigation and saving. All server cycles remain simulated or network-blocked.
No live assignments were changed and no original upstream files were edited.
Other platforms remain untested. Notifications, full operation coverage and
immediate-watch lifecycle remain future milestones.

## Milestone: local notification configuration

Added Notifications forms for send enablement, From address, recipients, SMTP
server, SMTP username, SSL/TLS and StartTLS. Field metadata now identifies its
INI section and option independently of the form key, so `[Email] username`
cannot collide with `[PrimeNet] username`. Existing field mappings still use
the same PrimeNet keys. CLI reference navigation includes the new mapped flags.

Save remains an offline, validated configuration operation. Changed recipient
lists normalize comma separators and surrounding spaces; unchanged values retain
their original formatting. SSL/TLS and StartTLS cannot both be enabled. The
backend checks email syntax, server scheme and required sender/server fields.
Send enablement uses the original backend's `[Email] send` flag; it does not
introduce a separate notification implementation. Blank boolean fields remove
explicit overrides and retain existing INI/backend inheritance semantics.

Validated October 25, 2026 on macOS/Python 3.15.1/Tk 9.1.0: **66 tests passed**,
including ten desktop tests. New coverage checks cross-section identity,
recipient normalization, TLS conflicts, invalid address/server rejection,
disable/reset behavior, preservation of plaintext and real upstream-encrypted
SMTP credentials, GUI save/reload and reference navigation. No SMTP message,
server discovery or live PrimeNet cycle was performed. No original upstream
files changed, and no dependencies were added.

Password editing, test-message sending, automatic SMTP discovery and per-event
notification controls remain unfinished. Saving other notification fields does
not encrypt plaintext passwords or replace the password for a changed SMTP
account. Those limits are documented in GUI.md. Full operation coverage,
immediate-watch lifecycle and other-platform validation remain future work.

## Milestone: hardware and resource configuration

Added eleven registration settings: processor model/features/frequency, total
physical memory, maximum stage 2 memory, proof residue disk limit, L1/L2/L3
cache sizes, physical cores and threads per core. They live in a scrollable
dialog opened from PrimeNet and are mapped in the searchable CLI reference.
The advanced assignment dialog and hardware dialog share the same staged
Apply/Cancel implementation. A modal dialog cannot apply edits while monitoring,
local operations or Quit are active.

Blank fields preserve INI inheritance and the backend's automatic detection or
defaults without materializing machine-specific values during an unrelated save.
The case-sensitive `memory` and `Memory` options remain distinct. Save uses the
original backend's type conversion and maximum-versus-total-memory check; the
GUI also rejects malformed/nonfinite numeric input. Hardware-only edits preserve
existing timing estimates, matching the absence of an upstream setup reset for
these settings. No computation-program settings or system resource limits are
changed by the forms.

Validated October 25, 2026 on macOS/Python 3.15.1/Tk 9.1.0: **69 tests passed**,
including eleven desktop tests. Added coverage includes all hardware fields,
case-sensitive memory keys, no-op saves, clearing overrides, estimate retention,
malformed input, backend memory conflicts, dialog cancellation, CLI-reference
navigation and GUI save/reload. Existing advanced-dialog tests pass after reuse.
No registration, hardware update, SMTP send or live PrimeNet cycle was performed.
Original upstream files remain unchanged; no dependencies were added.

Detected-hardware preview, automatic GPU selection, standalone graphical
registration, credential editing, selective server operations, immediate-watch
lifecycle and other-platform validation remain unfinished. GUI.md documents
units, detected/default behavior and the distinction between reported resource
settings and actual computation-program configuration.

## Milestone: connection settings and encrypted password management

Added proxy type/server/username and backend encryption policy in a Connection
dialog under Settings. Added masked SMTP/proxy password management under Settings
and Notifications, with CLI reference navigation for the corresponding flags.
Keep preserves pending edits, Replace stages a new secret, Remove stages deletion
of plaintext and encrypted entries, and Use saved cancels a pending change.
Cancel discards only that dialog's new edits. No saved password is loaded into
an entry; entries are cleared on Apply/Cancel. Successful Save or workspace
reload clears pending replacements. The removed legacy account-password feature
is intentionally not implemented.

The new offline `protect_credentials` operation reuses the original `encrypt()`
with strict encryption and limits its working mapping to explicitly replaced
passwords. Selected entries are removed from a private candidate before
preflight, allowing a damaged selected credential to be removed without first
decrypting it. No plaintext fallback is allowed. The existing atomic save layer
patches only returned ciphertext and any newly needed hardware GUID, then uses a
fresh offline validation process to decrypt/check the final candidate before
writing. Existing hardware GUIDs cannot change through this path; unrelated
ciphertext is retained byte-for-byte. Passwords inherited from DEFAULT are
refused for explicit adjustment outside the GUI.

Secrets travel to the private backend on stdin, not command-line arguments.
Backend diagnostics are suppressed and encryption errors are sanitized. Pending
values remain in GUI/worker memory until saved or discarded; this is not an
OS credential-store integration. Existing plaintext credentials are preserved
unless explicitly replaced or removed. Backups retain the previous file,
including any old plaintext passwords, with private backup permissions.

Validated October 25, 2026 on macOS/Python 3.15.1/Tk 9.1.0: **79 tests passed**,
including thirteen desktop tests. Coverage includes exact decryption of spaces
and percent signs, no secrets in argv/activity/errors, preservation of other
ciphertext and GUIDs, removal of damaged entries, disabled/unavailable encryption,
simulated native encryption failure, no-op proxy spelling preservation, dialog
Cancel/Keep/Replace/Remove/Use saved, connection settings and GUI encrypted saves.
No SMTP, proxy authentication or live PrimeNet operation was performed. Original
upstream files remain unchanged and no packages were added. OpenSSL libcrypto
availability is now documented as required for password replacement or reading
existing encrypted credentials; SOCKS remains an optional Requests extra.

Test-message sending, automatic SMTP discovery, per-event notification controls,
standalone registration, selective server operations, immediate-watch lifecycle
and other-platform runtime testing remain unfinished.

## Milestone: confirmed one-shot CLI commands

Added an allowlisted operation registry for normal PrimeNet ping, test email,
result reporting and combined result/proof upload. Dedicated buttons live in
PrimeNet, Notifications and Assignments. Each operation describes its effects
and fixed CLI flags in a confirmation; unsaved/missing/mismatched workspace
configuration prevents launch. CLI-reference navigation focuses the button and
does not start an operation.

The existing owned runner now executes one-shot commands with `--timeout 0`
instead of entering its schedule. It performs the same source/fingerprint/
offline checks, private configuration snapshot, readiness acknowledgement and
shared locks. A single CLI invocation runs without the scheduled mode's initial
registration follow-up. Test email additionally requires saved sender/server
settings and notification sending enabled. No arbitrary argument field or
interactive terminal is introduced.

The GUI disables competing commands and edits while a command is active. Stop,
Force, background hiding and asynchronous Quit reuse the existing ownership
controls. Completion is reported as a local zero exit, with server acceptance
and delivery unverified; detailed output remains in the original configured log.
The snapshot protects only configuration, not server reservations, proof files
or results changed by the original backend. GUI.md documents these effects.

Validated October 25, 2026 on macOS/Python 3.15.1/Tk 9.1.0: **88 tests passed**,
including fifteen desktop tests. New tests verify exact allowlisted/noninteractive
argv, exactly-once execution without registration follow-up, startup cancellation,
failure/force outcomes, real supervisor locking/backups/release, email preflight,
confirmation cancellation, duplicate clicks, disabled controls, dirty-form
rejection and reference navigation. All command bodies are mocked or simulated;
no PrimeNet ping, SMTP message, result submission or proof upload was performed.
Original upstream files remain unchanged and no dependencies were added.

Live command validation, experimental v6 ping, full debugging reports,
standalone registration, assignment recovery/unreservation, exponent registration,
immediate-watch lifecycle and other-platform runtime testing remain unfinished.

## Milestone: assignment management and private work snapshots

Added graphical pause/resume of new-work requests, recovery/recover-all,
single-exponent unreservation and unreserve-all. They reuse the allowlisted
one-shot runner and original CLI functions. Assignment buttons are arranged in
two columns to retain table space. Recovery and unreservation require exact
typed phrases; single unreservation has a bounded integer form, optionally
prefilled from a local table row. It explicitly follows the original CLI's
first-matching-exponent behavior across workers rather than promising AID or
worker selection. Reference navigation continues to focus without execution.

Operation parameters are structured, validated in both controller and helper,
and serialized only into allowlisted arguments. Exponent zero, boolean/string
values, extra parameters and parameters attached to scheduled mode are refused
to prevent accidental fall-through into a normal work cycle. Recovery requires
an existing computer GUID; single unreservation verifies the exponent is still
present in current local work files before launch. Neither check confirms a
remote reservation.

`gui_assignment_backup.py` creates private, byte-exact work/certification
snapshots before those four destructive commands. It handles worker directories,
custom work filenames, PRPLL indexed files and missing originals. The manifest
records original paths, backup names, hashes, sizes, operation and parameters.
Inputs must be regular non-symlink files, at most 2 MiB each and 16 MiB combined;
metadata checks reject concurrent changes, including changes detected after all
reads. Incomplete snapshots are removed on failure and the CLI is not launched.
The native instance lock protects preflight from another AutoPrimeNet instance;
computation engines remain independently managed. Snapshots are point-in-time
copies, not a transaction, and exclude result/proof/checkpoint/server state.
Typed confirmations and GUI.md instruct users to pause affected engines and
explain why copying files back cannot restore released reservations. There is
no automatic restoration or reservation rollback.

Validated October 25, 2026 on macOS/Python 3.15.1/Tk 9.1.0: **101 tests passed**,
including sixteen desktop tests. Coverage includes backup contents/permissions,
multiworker/PRPLL paths, missing files, unsafe/oversized/changing inputs, cleanup,
launch prevention on snapshot failure, operation parameter bounds, registration
and local-exponent preflight, typed confirmation cancellation and simulated
launches. The actual Tk confirmation was displayed, checked against desktop
dimensions and automatically cancelled. Two initial test failures were fixed by
comparing resolved macOS `/var` and `/private/var` paths; the final full suite
passes, including concurrent-change detection.

The original CLI's pause/resume flags were also executed in disposable
workspaces with socket operations blocked: they set/remove QuitGIMPS, retain work
files and do not create a computer GUID. All recovery/unreservation command
bodies remain simulated; no live reservation, result, SMTP or proof operation
occurred. Original upstream files remain unchanged and no dependencies were
added. Snapshot directories are ignored when generated in the checkout root.

Live assignment-management validation, exponent registration, standalone
computer registration, v6 ping, full debugging reports, immediate-watch lifecycle
and other-platform runtime validation remain unfinished.

## Milestone: graphical registration, reporting and explicit parity inventory

This broader checkpoint adds graphical exponent batches, standalone computer
registration/update, v6 ping, original work-status reporting, bounded native-log
viewing, private diagnostic export, original CLI help/version and update/output
preferences. The Advanced reference now classifies all 96 audited parser entries
and navigates worker/program/path controls as well as fields and operations.
GUI_PARITY.md records Available, Partial, CLI-only and removed/hidden cases;
parser-entry counts are explicitly not a claim of complete functional parity.

### Source-based graphical registration

`gui_registration_plan.py` validates bounded form data and supplies only reviewed
answers to the original `register_exponents()` prompts. The offline preview uses
that original function, `Assignment`, parser and formatter with an in-memory
append target, virtual lock and no-op registration. It suppresses the optional
mersenne.ca lookup because every input is explicit. Unexpected/repeated prompts
fail instead of requesting terminal input. Original primality and cumulative
known-factor divisibility checks are reused before execution. Resource limits
are 100 entries, 48 KiB normalized data, 32 factors per entry and 1024-bit integer
inputs/factors, with original type-specific ranges and finite numeric checks.

`gui_registration_form.py` provides one-worker batches for all eight original
work types, conditional fields, add/replace/remove, asynchronous offline preview,
scrollable canonical lines and `REGISTER N` confirmation. Queued edits invalidate
preview; reload/Quit protects queued rows; a closed dialog discards delayed
results. Draft edits require Add/Replace before affecting the queue. Plans are
in-memory only. A changed saved configuration requires another preview.

`gui_registration.py` is a private live child. It checks the source hash and
saved configuration fingerprint, executes the original startup up to its final
main call, then binds validated graphical answers before invoking the original
main function. Exponent registration follows the original append/register path,
including registration of other unregistered tasks already in the selected
worker's file. Computer registration skips the terminal setup initializer and
uses main's setup-completion branch with saved settings, preserving the original
computer/program-options routines without starting work retrieval or test email.
No source file is patched and no PrimeNet API implementation is copied. Original
startup retains logging, native locking, encryption and proxy initialization.

The owned supervisor reruns offline registration preview and creates private
work/certification snapshots before exponent registration, requires an existing
computer GUID, and passes bounded plan data through stdin, not argv. It retains
the readiness handshake, source/fingerprint guards and Stop/Force/Quit ownership.
An explicit computer-registration action does not add a normal monitoring cycle.
Automatic GPU selection and SMTP-provider discovery remain unfinished.

### Reports, preferences and remaining limits

`gui_reports.py` reads at most the latest 128 KiB/2000 lines from a regular,
non-symlink configured native log into a separate private window. It does not
copy native content into GUI activity. Native status uses the original `--status`
command and writes its report to that log. Diagnostic export calls the original
`debug_info` in the network-blocked bridge, returns at most 256 KiB, redacts
configured passwords and exclusively creates a private `.gui-debug-report-*.txt`.
The report still contains account/computer/hardware identifiers and is never
uploaded automatically. Configuration staleness prevents export. Report files
are ignored if generated in the checkout root.

Added version-check enablement/channel, native console-color preference,
large-prime result reporting policy and new-prime sound suppression, using
existing INI semantics and offline save validation. The withholding policy's
need for another notification method is stated in the form and guide. About uses
the version literal from the hash-guarded source; CLI help builds the original
parser offline without requiring a workspace.

A disposable, network-blocked probe confirmed that the original CLI rejects
UTF-8 BOM-prefixed configurations with exit 2/MissingSectionHeaderError. Local
GUI editing continues to preserve BOM bytes; runner/live-adapter startup now
fails before CLI execution with instructions to back up and save as UTF-8 without
BOM. New GUI configurations already omit BOM. No upstream encoding change was
made. The original GUI save preservation tests still apply.

### Validation

Validated October 25, 2026 on macOS/Python 3.15.1/Tk 9.1.0: **122 tests passed**,
including nineteen desktop tests. New coverage checks all eight original work
formats, known factors/residue modes, GPUOwl bounds, composite/invalid input,
prompt drift, multiple queued rows, existing unregistered work, multiworker and
PRPLL target files, stale configuration, stdin-only plans, supervisor snapshots,
batch UI mutation/preview/cancellation/confirmation, private log isolation,
diagnostic permissions/redaction/staleness, original help, version/preferences
and explicit classification of every audited parser entry. Batch action controls
were checked to remain within the rendered dialog.

Isolated source executions use blocked sockets and simulated API responses. The
real `register_instance`/`program_options` functions made only simulated `uc`/`po`
transactions; the real exponent-registration flow appended and normalized work
using simulated assignment replies. No live computer registration, assignment
registration, v6 ping, result/proof operation or notification was performed.
Original upstream files remain unchanged and no packages were added. Native
watching/separate polling, disabling GUI locking, verbose HTTP tracing, automatic
GPU/SMTP discovery, live validation and other-platform runtime testing remain
open. See GUI_PARITY.md for exact coverage rather than treating this as release
completion.

## Local GPU discovery and reviewed hardware selection

Added **PrimeNet → hardware settings → Detect GPUs** using the original
`get_gpus` implementation in the existing network-blocked, hash-guarded helper.
OpenCL, CUDA and NVML remain native driver capabilities; no Python dependencies
were added. The picker shows device/source and proposed settings before applying
them to the staged hardware dialog. Applying the dialog and saving remain
separate, so discovery and cancellation do not write configuration or contact
PrimeNet. Duplicate devices remain distinguishable by discovery source/index.

The mapping follows original setup, including its 90% stage 2 memory estimate,
conditional core/thread and cache overrides, and original MiB/KiB/MHz units.
Unknown cores/caches retain existing settings. Unusable records are omitted;
empty results and driver failures leave manual editing available. Results for a
closed/replaced dialog are ignored. Detailed helper errors are not shown in
message boxes. SMTP discovery and native watching remain pending, as recorded in
GUI_PARITY.md.

Validation covers complete and missing GPU measurements, rejected malformed
records, reuse of original discovery, helper-session cleanup, real local discovery
with networking blocked, staged selection, cancellation, driver errors, empty
results, and late-result isolation. The actual discovery probe created no runtime
files. Final verification on macOS/Python 3.15.1/Tk 9.1: **129 tests passed**,
including **21 desktop tests**. Dependency checks and `git diff --check` passed.
No live service requests or assignment changes were performed.

## Reviewed SMTP-provider discovery

Added **Notifications → Discover SMTP provider** with a sender-address field,
network confirmation, provider/security/SMTP/username review, and explicit Apply
to form. Save remains separate. Passwords, recipients, notification send policy,
and the separate test-email operation are unchanged. Edited addresses/workspaces
invalidate results; closed dialogs discard late completions. No-match and failed
lookups retain manual editing, and raw helper errors never appear in the dialog.

A separate private helper reuses the audited original `email_autoconfig`, XML
parser, MX/SRV fallback and proxy initialization. It does not execute CLI startup,
main, setup, SMTP sending or PrimeNet operations. Saved config fingerprints are
checked before and after lookup. Requests use saved proxy settings and the normal
Requests environment, eight-second per-request timeouts and a 90-second parent
limit. Sender/configuration inputs travel through stdin. The offline bridge
continues to reject this operation and retains its socket audit guard.

Provider data is checked for valid ports, single-line descriptions and supported
security modes. Unknown security is rejected. Explicit plain SMTP is displayed
with both TLS options disabled; a missing username retains the old value. The
confirmation and review explain original HTTP and unsigned-DNS fallback behavior.
No dependencies or original upstream files changed.

Automated coverage includes real original XML discovery with simulated HTTP,
original DNS SRV selection with simulated DNS responses, saved proxy credentials,
no-match/stale-config handling, invalid data and IPC, bounded parent timeout,
confirmation refusal, staged apply, recipient/password/send-policy preservation,
address invalidation, errors and cancellation. No live provider, SMTP or PrimeNet
requests were performed. Manual acceptance remains deferred at the user's request
until implementation is ready, with tests planned across their available machines.
Setup is now classified Available in the 96-entry inventory, with live and platform
acceptance still pending. Native watching/separate polling, lock bypass and verbose
HTTP tracing remain the outstanding runtime gaps.

Final automated verification: **139 tests passed**, including **23 desktop
tests**, on macOS/Python 3.15.1/Tk 9.1. Dependency checks and `git diff --check`
passed. Manual and live-service testing remain pending. Quit during a bounded
lookup asks the user to retry after it finishes, matching existing job handling.

## Native monitoring cadence, file watching and graceful worker shutdown

Positive polling intervals now run a continuous owned native scheduler through
`gui_runtime.py`. The original `main` still controls check-ins, work requests,
certification, rolling averages, native watchers, proof handling and notifications.
`--timeout` is passed explicitly from `[GUI] PollSeconds`, since upstream does not
persist that CLI option. The original `[PrimeNet] watch` preference is editable.
Zero performs one complete pass (including new-registration follow-up if needed).
The Dashboard and native tray show Watching files between polling passes, and
tray Stop remains enabled in that state. Settings are reachable from the CLI
reference, typed, validated offline and saved through the existing preservation
path. Default polling remains 3600 seconds and default watching is enabled.

The original source is not edited. The source-hash guard and exact AST-layout
checks permit narrowly scoped in-memory hooks: replace the scheduler's outer
counter with a stop-aware iterator, make scheduler/retry cooldown waits wakeable,
and register report/upload threads before starting them. The original one-second
result-read and 60-second proof-upload ordering delays are preserved. Stop drops
new queue submissions, exits idle queue consumers, lets active work/batches finish,
and joins every report/upload worker before the child exits. Pending names are
not a durable job queue; unchanged source result/proof files are scanned on restart.
Native watcher threads remain daemon threads and only enqueue names; their handles
close at process exit. Watcher/report/upload failures stop the scheduler, record a
private native-log exception and drain active writers before returning failure.

The supervisor retains preflight cancellation and its ready/begin handshake,
passes a config hash to the native child, forwards Stop/parent EOF, and handles
explicit force by terminating/reaping only that child. One-shot operations keep
their existing execution path. A cycle-completed event marks local scheduling
work, not completion or server acceptance of asynchronous uploads. No computation
engine is started/stopped, no upstream CLI behavior is changed on disk, and no
packages were added.

Validation includes two actual original scheduler polls with simulated server
functions and blocked sockets: the first checked in and the second did not.
The original macOS FSEvents watcher delivered a real temporary results-file
change to the original reporting worker; all reporting/upload threads exited
before the adapter returned. The test retains original result-read ordering and
skips only the five-minute cooldown to keep runtime bounded. macOS FSEvents
cannot start within this sandbox, so that native integration test joins the
explicitly enabled, unsandboxed desktop run. Other platforms remain pending.
Additional tests cover source-layout rejection, queue stop/wakeup, active-worker
draining, worker failures, Stop during preflight, zero-interval single-pass,
Stop forwarding, owned-only force termination, saved polling/watch preferences,
invalid intervals, reference navigation and desktop editing/saving. No live
PrimeNet, provider, SMTP, result submission or proof upload was performed.

Manual acceptance remains deferred until implementation is ready. Remaining
runtime parity gaps are lock bypass and verbose HTTP tracing; platform/live
acceptance remains separate from the implemented feature inventory.

Final automated verification: **148 tests passed**, including **24 desktop tests**
and the native macOS FSEvents integration test, on Python 3.15.1/Tk 9.1.
Dependency checks and `git diff --check` passed. Original-file diffs against
the audited baseline remain empty.

## Debug verbosity and bounded private HTTP/SMTP tracing

Added typed `[GUI] DebugLevel` (0–3) under monitoring/output preferences and CLI
reference navigation for `--debug`. Original repeated debug flags apply to every
owned one-shot/one-pass child, native scheduler and graphical registration child.
Level 1 enables the original native debug log; levels 2–3 additionally preserve
raw console/HTTP/SMTP output in a separate `.gui-backend-trace-*.log`. These files
are now ignored by Git. Original upstream files and dependencies are unchanged.

Trace files are exclusively created with private temporary-file permissions.
Dedicated capture threads drain raw output, cap storage at 8 MiB including a
limit marker, discard excess while continuing to drain, and flush captured chunks
for live viewing. Capture errors do not stop backend writes/uploads. The native
runtime's JSON event stdout stays separate from stderr/raw trace output; ordinary
CLI stdout/stderr are captured together. Only a generated filename and generic
capture warning are sent to GUI activity. Raw contents remain in the private file.
The original backend log has its own unchanged upstream rotation/permissions.

Existing Start/operation confirmations include the credential/message-body
implications when tracing is enabled. Logs & Status offers a latest-trace viewer
using the same bounded non-symlink file reader as native logs. Opening native logs
and traces switches the private view rather than copying data to GUI activity or
diagnostic reports. The trace viewer reads only the latest regular matching file;
older traces remain accessible with local editors. Retention is manual.

Automated coverage checks all verbosity levels and offline validation, original
HTTP debug startup in both source-executing adapters with sockets blocked, exact
CLI flags, channel separation, the capture size cap and continued draining of a
large simulated output stream, write-error behavior, private file permissions,
latest-file selection and symlink avoidance, confirmation text, saved controls,
reference navigation, private viewer switching and activity isolation. No live
HTTP/SMTP tracing or PrimeNet/provider requests were performed. Manual/live and
other-platform acceptance remain deferred. Lock bypass is the remaining explicit
CLI runtime difference; the GUI still requires exclusive native instance leases.

Final automated verification: **156 tests passed**, including **25 desktop
tests** and the native macOS FSEvents check, on Python 3.15.1/Tk 9.1. Desktop
Save confirmations are explicitly answered by test mocks, with no user input
required. Invalid debug preferences are blocked before Start/action confirmation.
Dependency checks, trace ignore-rule verification and `git diff --check` passed;
original-file diffs against the audited baseline remain empty.

## Native-lock policy parity and atomic GUI ownership

Added **Settings → Connection → Require successful native instance locking**,
backed by the original `[PrimeNet] require_lock` and CLI `--lock` / `--no-lock`
policy. Blank/True stays strict. False still attempts native locks, refuses
`EAGAIN`/`EACCES` live-owner failures and permits other native-lock acquisition
errors, matching the audited original startup. Lock-file open failures, symbolic
links and non-regular native lock paths remain fatal. Configuration saves use
the explicitly selected candidate policy; server actions use saved policy.

A mandatory `.gui-runner.guard` now coordinates all GUI monitoring/actions/saves
in addition to existing native locks. It is exclusively created with private
permissions, stores host/PID/random token, and lasts for the operation's ownership
scope. Cleanup checks the original inode and exact token contents after closing
the writer, avoiding timestamp assumptions that differ on Windows. Existing,
stale, modified or replaced guards are not automatically deleted. Failed metadata
initialization cleans only the newly created inode. The documentation explains
manual stale-guard inspection and that an exited supervisor PID does not prove
its draining child has finished. The guard is ignored by Git.

Existing Save/Start/action confirmations explain optional native locking and the
need to exclude independent CLI instances manually when locking is unavailable.
Ready events report unverified native preflight locking without raw OS errors.
Known live owners remain refused in every mode. Original per-work `.lck` locks
are unchanged; atomic file creation must still work. Reserved native/GUI lock
names cannot be configuration, work, results, log or archive targets.

Automated checks simulate unsupported native locking, known live-owner errors,
strict/optional save paths, guard exclusivity/private metadata, stale and symlink
refusal, replacement protection, changed-timestamp cleanup, FIFO refusal and
metadata-write failure cleanup. A real supervisor with simulated unavailable
native locks reports unverified ownership, blocks a second GUI runner and blocks
a save from a native-lock-capable process. Original startup in both native and
registration adapters honors saved strict/optional policies under simulated
native failures with sockets blocked. Desktop checks cover reference navigation,
saved policy and existing confirmation text. All 94 ordinary parser entries now
have graphical controls/operations; hidden experimental Prime95 remains excluded
and legacy account-password authentication remains removed upstream. Inventory
coverage is not release/platform/live-service acceptance. No original upstream
files or dependencies changed, and no live server requests were performed.

Final automated verification: **166 tests passed**, including **26 desktop
tests** and native macOS filesystem-event integration, on Python 3.15.1/Tk 9.1.
Dependency checks, guard ignore-rule verification and `git diff --check` passed.
Original-file diffs against the audited baseline remain empty. Real unsupported
filesystems, other platforms and manual/live-service acceptance remain deferred.

## Optional GTK tray integration and resilient helper retries

Linux/FreeBSD now attempt menu-capable GTK 3/AppIndicator tray integration in the
existing private native helper, without importing GTK into the Tk GUI process.
Optional requirements-gui-tray-gtk.txt installs PyGObject plus the existing tray
packages; GUI.md separates venv packages from native GTK 3/GObject/Cairo/build
prerequisites and desktop tray/extension requirements, with primary documentation
links. Base GUI use remains independent of GTK. No packages were installed on
the macOS development host for this change, and original upstream files remain
unchanged.

Automatic backend choice prefers AppIndicator when its local session bus reports
a registered StatusNotifier visualization host, otherwise GTK legacy embedding.
Missing AppIndicator typelibs can fall back to GTK; explicit PYSTRAY_BACKEND is
respected. Menu-less backends are refused. GTK readiness checks StatusIcon
embedding; AppIndicator checks IsStatusNotifierHostRegistered with a bounded,
non-autostarting D-Bus property request, not just existence of a watcher service.
The helper gives initial embedding five seconds and checks established hosts
every two seconds. Host loss stops the helper so the GUI restores a hidden
window and retains taskbar/Dock fallback. These checks cannot prove desktop
visibility when a user's panel configuration intentionally hides an icon.

Settings offers Retry tray integration without restarting monitoring. The GUI
also stops/reaps startup attempts that exceed 15 seconds. Tray events include
attempt generations, so stale readiness/menu/failure events do not affect a
replacement helper. Readers and reapers capture the exact old process rather
than dereferencing a mutable current handle; stop is idempotent. GTK operations
are dispatched through its main loop, with the existing macOS AppHelper dispatch
retained. The control reader uses unbuffered binary input to avoid a blocked
stdin buffer during host-loss interpreter shutdown.

Automated coverage simulates GTK and local D-Bus host states, typelib fallback,
explicit backend policy, menu capability, embedding timeout and later host loss.
The actual helper main-loop/control path exits cleanly in a simulated GTK child
while its parent input remains open. Tests verify Linux controller dispatch,
old-reader/reaper process isolation, stale-generation rejection, retry/no-duplicate
behavior, hidden-window restoration and startup timeout reaping. Native macOS
tray tests continue to run. These are not evidence of actual Linux/FreeBSD
libraries, Wayland/X11/panel integration or physical desktop acceptance; those
remain deferred along with live-service and user manual testing.

Final automated verification: **175 tests passed**, including **28 desktop
tests**, native macOS tray checks and filesystem-event integration, on Python
3.15.1/Tk 9.1. Dependency checks and `git diff --check` passed. Original-file diffs
against the audited baseline remain empty. No PrimeNet/provider/SMTP requests or
assignment changes were performed.

## Acceptance preparation and backend response handling

Added GUI_ACCEPTANCE.md as the consolidated manual acceptance plan. It separates
offline configuration checks, desktop lifecycle, controlled monitoring, deliberate
live operations and platform/version completion. Each machine records its tested
commit, interpreter/Tk/dependency versions, desktop and filesystem, outcomes and
blocked prerequisites. It includes automated suite commands and expected results;
unchecked items are explicitly unverified. Manual acceptance remains deferred.

Updated GUI.md's stale overview, watching/tray statements and historical smoke
test wording to distinguish implemented inventory coverage from current release
validation. No new platform or live-service acceptance is claimed.

Hardened the offline controller's JSON envelope handling: non-object responses,
missing successful results, non-boolean success values and malformed error
payloads now produce a controlled ControllerError instead of leaking unexpected
AttributeError/KeyError or accepting a malformed success envelope. A regression
test exercises these malformed responses while retaining the existing real
offline-bridge failure test.

Validated October 25, 2026 on macOS/Python 3.15.1/Tk 9.1: **176 tests passed**
with desktop/native integration enabled. The default suite ran 176 tests with
29 desktop/native cases skipped. Dependency checks and `git diff --check` passed;
the original source hash and original-file baseline diff remain unchanged.
No live-service operations, assignment changes or user manual tests were run.

## Responsive failed-start cleanup and helper event recovery

Reviewed runner startup and found that a failed initial pipe write/flush could
wait five seconds on the Tk thread, propagate a second pipe-close error, or
leave an unreaped child after timeout. Failed startup now retains the specific
owned process and generation, marks it stopping, and runs termination, bounded
wait, kill escalation and stream cleanup on a background thread. The initial
begin handshake has not been sent, so no communication cycle is authorized.
The cleanup tolerates exit races and broken pipe closure; it emits the normal
generation-tagged exit notification. Start/operation error paths refresh control
availability so conflicting actions are disabled while cleanup is still active.

Tray and runner readers also reject non-string event names before allowlist
membership checks. Previously an array/object event name could raise TypeError
and stop delivery of later valid events.

New regression coverage checks malformed event recovery in both readers,
startup errors returning while cleanup is deliberately held, duplicate-start
exclusion during cleanup, timeout escalation and process-generation isolation.
A real subprocess test verifies a failed startup request is reaped and its pipes
closed while an unrelated process remains alive. No real backend cycle or
external service is invoked by these tests.

Validated October 25, 2026 on macOS/Python 3.15.1/Tk 9.1: **180 tests passed**
with desktop/native integration enabled. Dependency checks, `git diff --check`
and the original-file baseline check passed. Manual, other-platform and exact
Python 3.15.0 acceptance remain pending under GUI_ACCEPTANCE.md.

## Stable workspace reads and nonregular-file handling

Extended the same hardening milestone without an intervening commit. Workspace
preview reads previously used ordinary blocking opens, and configuration version
checks did not verify the opened descriptor against the pathname before reading.
The shared bounded regular-file reader now compares initial path metadata,
opened-descriptor metadata, post-read descriptor metadata and final path metadata.
Configuration reads refuse symbolic links; read-only work previews retain support
for links to regular targets. File limits remain 2 MiB. POSIX nonblocking opens
prevent FIFO replacement races from waiting for a writer; this is not a general
network-filesystem timeout mechanism.

Existing nonregular work paths and dangling work links now cause explicit errors
instead of silently appearing absent. Missing ordinary work files remain valid.
Assignment-snapshot and configuration-save no-symlink policies are unchanged.
The existing end-of-load configuration-version check still rejects changes
between loading editor settings and assembling the workspace preview.

New tests cover nonregular/oversized preview inputs, replacement between stat
and open, valid work-file symlinks, refused configuration symlinks and POSIX
FIFOs, including replacement after stat. The FIFO checks run in a subprocess
with a five-second deadline so a regression cannot hang the entire test suite.

Combined automated verification October 25, 2026: **184 tests passed**, including
all enabled desktop/native checks, on macOS/Python 3.15.1/Tk 9.1. The default run
also passed with 29 desktop/native cases skipped. Dependency checks,
`git diff --check` and original-file baseline checks passed. No live-service
operations or user manual tests were performed. Remaining acceptance is tracked
in GUI_ACCEPTANCE.md; other operating systems and exact Python 3.15.0 remain
unverified.

## Comprehensive code, regression and documentation review — October 26, 2026

Reviewed the GUI additions across configuration/credential persistence, offline
and live adapters, registration planning, scheduling, worker shutdown, tray
integration, reports and Tk forms. Original upstream files were preserved.

### Corrections

* `gui_paths.py` validates effective file roles before Save and runner launch:
  configuration, log and five rotated logs, work/results/certification/history,
  `.add` imports, sidecar locks, instance ownership and proof archive directory.
  It covers PRPLL indexed names, worker-relative paths and existing hard-link or
  symlink aliases, plus case-only names on case-insensitive macOS volumes and
  Windows. The Darwin case-policy constant was checked against the local SDK's
  sys/unistd.h. Existing runtime file paths must be regular files; an archive
  must be a directory. A noncooperating process can still replace paths after
  validation, so this is not a replacement for ownership/locking.
* Reload/Save closes old form dialogs, clears unapplied password entries and
  closes the old saved configuration's private log viewer. Worker dialog callbacks
  retain their originating document. Directory selection confirms discarding
  edits once; a failed load retains the old values and dirty state.
* One-pass initial registration treats an empty ComputerGUID like a missing one,
  and runs its follow-up only after a nonempty GUID appears and Stop is not set.
* Runner messages validate the fields consumed by Tk, while preserving both
  scheduled and one-shot readiness formats. SMTP responses are checked before
  reaching forms. Non-string tray states and extreme GPU measurements fail
  safely instead of breaking reader/callback threads or overflowing conversion.
* StoppingQueue preserves queue timeout/nonblocking behavior while retaining
  stop-at-idle-boundary semantics. Assignment previews reject wrong row counts
  instead of silently truncating through zip.
* `.gitignore` covers separate `.venv*` test environments. Unused imports and
  test fixtures were cleaned up after the scoped static check.

### Regression coverage and documentation

Added focused checks for the corrections above, changing/disappearing files
during reads, failed private-report cleanup, malformed/oversize private-helper
requests, native console/event channel separation and parent EOF. The parity
inventory is now checked against all audited parser entries, including coverage
classification. Native tray tests explicitly skip absent optional packages;
installed packages with a failing native helper still fail the test.

The user guide now groups Features, Installation, Usage and Development, with
discovery/debug instructions alongside the settings they describe. GUI documents
use the upstream README's asterisk lists, fenced commands, Markdown headings,
tables and relative links. Earlier milestone claims are labeled historical;
current inventory coverage is separated from pending platform/live acceptance.
The user's downloaded VM testing documents were not restored to the repository.

### Final automated verification

On October 26, 2026, macOS/Python 3.15.1/Tk 9.1 passed **210 tests** with
desktop/native checks enabled and no skips. This review added 26 tests to the
184-test baseline. The default run also passed, with 32 desktop/native checks
skipped. Coverage 7.17.0 measured **87% combined statement/branch coverage**
across the 21 GUI modules, including helper subprocesses (3,173 of 3,567
statements executed). Coverage does not establish acceptance of other operating
systems, live services or exact Python 3.15.0; these remain pending in
GUI_ACCEPTANCE.md.

The scoped Ruff 0.17.2 checks passed. All 40 GUI/test Python sources parsed,
the 12 shell command blocks passed syntax checks, and local documentation links,
dependency consistency and `git diff --check` passed. Review tools and coverage
artifacts stayed outside the repository. All ten original upstream files still
match baseline b4426a1. No live-service operations or user manual acceptance
tests were performed.

## Fedora acceptance follow-up: pending Tk polling callback

The Fedora GNOME/Wayland manual window/fallback and AppIndicator tray rounds
passed, including extension disable/re-enable, Retry and shutdown. The subsequent
desktop-enabled automated run reported 210 tests, OK with three skips, but also
printed repeated Tcl `invalid command name ...poll` errors. This is not a clean
desktop acceptance result despite the unittest success status. Computation/live
acceptance was not established by these Fedora GUI/tray checks.

Application shutdown now cancels its pending Tk polling callback before
destroying the root window. Previously the callback's Tcl command was deleted
while its timer remained queued, which could surface when later test windows
pumped events. A desktop regression verifies that Quit removes the timer from
Tk's pending callback list. Repeating the suite on Fedora remains necessary to
confirm that the reported messages are gone.

Local verification on macOS/Python 3.15.1/Tk 9.1 passed all 211 tests with
desktop/native checks enabled, no skips and no Tcl callback errors. Scoped Ruff
checks and `git diff --check` also passed. Only GUI-added files were changed.

## PR notes: Ubuntu packaged Mlucas work filename

Ubuntu 26.04.1 ARM64's packaged Mlucas 20.1.1 documents `worktodo.ini` as its
assignment input. The GUI defaults to `worktodo.txt`; selecting Mlucas does not
automatically change that filename. For this engine setup, users must explicitly
set **Settings → Work filename** to `worktodo.ini` and save before starting
monitoring. Otherwise the GUI/backend and engine may use different assignment
files. Include this configuration requirement in the eventual PR description;
it is not an automatic filename-selection feature or an upstream source change.

## Ubuntu acceptance follow-up: visible save errors

Ubuntu desktop testing exposed an inaccessible bottom status message while
configuration saves were failing. The expanding notebook was packed before the
status label and could consume its available space. The status area is now
reserved first, and messages wrap to its actual width. Failed background saves
also display the same sanitized error in a dialog; unapplied edits remain intact.
New desktop regressions cover a long message at the minimum window size and
save failure notification with draft preservation. The underlying Ubuntu save
failure was subsequently identified as the missing required GIMPS username (or
literal ANONYMOUS). Once the user supplied a username, saving, refreshing and
reloading the same workspace after a full GUI restart preserved the settings.

Local desktop/native verification passed all 213 tests on macOS/Python 3.15.1/
Tk 9.1, with no skips. Scoped Ruff and `git diff --check` passed. Ubuntu needs
the updated GUI to verify the layout. The user subsequently confirmed the error
dialog exposed the missing username requirement and the configuration reload
check passed. The user guide now includes the complete initial configuration
sequence, save-success check, Mlucas filenames and explicit workspace reselection.

## Automatic saving and post-operation refresh

Ubuntu acceptance exposed repeated stale-document conflicts after the backend
normalized or updated prime.ini. Automatic saving and refresh are now required
behavior rather than release wishlist items. Valid form edits are submitted to
the existing validated, locked, backed-up save path after a two-second debounce.
Open editor/registration dialogs defer submission; Apply stages values and Cancel
does not apply the dialog draft. Explicit Save retains its confirmation. Saves
remain local and do not launch monitoring or server operations.

Save completion refreshes the preview. Runner exit schedules a configuration and
workspace reload after ownership ends, including failed runs that may have
modified files before failing. Dirty forms and changed workspace selections are
preserved, and pending exponent batches retain their entries but lose their old
preview. Automatic saving never merges over an externally changed configuration;
the existing fingerprint check refuses it and reports the failure. Failed saves
are not repeatedly retried without another edit or an explicit save. Quit flushes
eligible pending edits, remaining open when the save fails.

Desktop regressions cover debouncing, automatic preview updates, operation-exit
reload, open-dialog deferral, invalid input, external-file conflicts, preservation
of drafts and Quit success/failure. Existing explicit-save tests disable automatic
updates so they continue testing the manual action independently. Ubuntu manual
retesting of the automatic behavior and computation integration remain pending.

Automated verification on macOS/Python 3.15.1/Tk 9.1 passed all 221 tests with
desktop/native checks enabled. The default run also passed (43 desktop/native
skips). Scoped Ruff checks, Python parsing, original-file preservation and
`git diff --check` passed. The eight added regressions use local fixtures and
simulated runner-exit events; they do not establish live-service acceptance.

Before the eventual PR, prepare gui_release_notes.md and review/remove
agent-specific development material as requested. Retain user documentation and
meaningful tests; no original upstream files are to be removed or changed without
the user's approval.

## Remembering the last workspace

The GUI now remembers the last successfully loaded working directory and its
configuration filename in per-user preferences outside the checkout and engine
workspace. On restart it loads that local preview after offline capabilities
initialization; monitoring and server operations are not resumed. Failed loads do
not replace the remembered selection. Invalid preferences are ignored with an
activity message, unavailable workspaces remain visible for manual correction,
and preference-write failure does not prevent normal workspace use.

Preferences use a bounded, versioned JSON record and atomic replacement with a
private temporary file. They contain no credentials or runner state. Tests cover
round-trip/non-ASCII paths, platform locations, malformed/oversized records,
failed-write cleanup, actual GUI restart with a custom configuration filename,
and a missing restored directory. Desktop tests use isolated preference paths so
they do not read or overwrite the user's selection.

Verification passed all 227 tests with desktop/native checks enabled on macOS/
Python 3.15.1/Tk 9.1. The four isolated preference tests, scoped Ruff checks and
`git diff --check` also passed. Ubuntu restart acceptance remains pending.

## Original-file changes

None. All GUI work so far is in newly added files. Existing upstream source,
README, pyproject.toml, and workflows remain unchanged. No files have been staged
or committed by the agent.
