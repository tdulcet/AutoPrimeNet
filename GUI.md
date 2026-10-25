# AutoPrimeNet GUI

The planned optional Tkinter/ttk GUI will provide a graphical interface to
AutoPrimeNet. The current desktop foundation provides local previews, initial
configuration forms with validated saving, scheduled CLI monitoring, and
experimental macOS/Windows tray integration. Starting monitoring performs real
server operations. Immediate file watching and standalone graphical assignment
actions are not implemented yet. This is not a complete GUI release.
See [GUI_DEVELOPMENT.md](GUI_DEVELOPMENT.md) for prototype tests and results.

## Python requirements

**The GUI requires Python 3.15.0 or later.** This minimum supersedes the original
Python 3.4 compatibility requirement for the GUI, its supporting modules, and
GUI-specific tests. New GUI code may use features available in Python 3.15.0.

Use a current maintenance release of Python 3.15 or a later supported version.
Python 3.15.0 is the compatibility floor, not a requirement to install that exact
patch release. GUI validation must include Python 3.15.0; support for later
versions must be verified rather than assumed.

The GUI interpreter must have working Tkinter and ttk bindings. AutoPrimeNet's
existing Requests dependency must also be available to the backend interpreter.
A virtual environment does not supply missing native Tk bindings.

The intended default is to run the GUI and its AutoPrimeNet backend with the same
Python 3.15.0-or-later interpreter, in an isolated development environment.

## Independent CLI compatibility

The GUI-only minimum does not change the CLI's declared Python 3.4 minimum.
Existing CLI source, dependency declarations, and startup paths remain unchanged.
CLI users will not need Tkinter or the GUI modules.

The source audit found an existing unconditional `EmailMessage` import in
`autoprimenet.py` that is incompatible with stock Python 3.4. Raising the GUI
minimum removes that issue as a GUI prerequisite; it does not repair or verify
the CLI's historical compatibility claim.

## Background operation and window closing

The intended default is **close to tray/menu bar and keep monitoring**. Closing
the main window hides it while both the GUI and its managed AutoPrimeNet backend
remain running. This differs from exiting the GUI and leaving a detached backend.

- Windows: use the notification area (system tray).
- macOS: use a menu bar status item.
- Linux and FreeBSD desktops: use an available compatible tray/status-item host.
  Availability depends on the desktop session, not just the operating system.

The tray/menu-bar menu should offer **Open AutoPrimeNet GUI**, monitoring status,
start/stop controls for the GUI-managed backend, and **Quit**. Callbacks must
dispatch GUI updates onto Tk's main thread. Hiding and reopening must not start
duplicate backend processes.

Hide the window only after establishing a working restore control. If no usable
tray host exists, minimize to the taskbar/Dock instead and explain the fallback.
If tray support fails while hidden, restore the window or another reachable
control. Do not leave an inaccessible hidden application.

**Quit** is separate from closing the window. When monitoring is active, Quit
should explain that it will stop the GUI-managed AutoPrimeNet backend and confirm
that action. An AutoPrimeNet instance launched independently remains outside the
GUI's shutdown control. Hiding or quitting the GUI must never terminate Mlucas,
Prime95, or another computation engine, unreserve assignments, or change the
stop/resume-new-work setting as a side effect.

The prototype uses optional `pystray` in a separate child process with its own
native event loop. Tkinter does not directly provide a portable tray API; using
this library avoids maintaining separate native tray implementations. Its LGPLv3
license is compatible with the GUI's GPLv3 licensing. Dependencies include Pillow,
six, and platform bindings (PyObjC Cocoa/Quartz on macOS). These packages are not
required by the CLI. They are declared separately in `requirements-gui-tray.txt`.

Native tray integration has been programmatically tested on macOS with Python
3.15.1. Windows remains untested. Linux/FreeBSD currently use taskbar minimization;
their tray hosts have not yet been validated. This follows the event-loop and
desktop constraints described in
[pystray's integration documentation](https://pystray.readthedocs.io/en/latest/faq.html).
If the helper fails while hidden, the GUI restores itself. The helper also exits
when its parent closes its input pipe, including after a parent-process failure.

## Environment setup for users and testers

These instructions prepare an environment for the current GUI foundation. The
backend and opt-in desktop test suites are documented in
[GUI_DEVELOPMENT.md](GUI_DEVELOPMENT.md). Live PrimeNet monitoring has not been
validated; lifecycle tests use simulated cycles. Full parity remains unfinished.
All GUI-specific dependency declarations and documentation are new
files; existing CLI installation instructions remain unchanged.

### Required components

| Location | Required component | Purpose |
| --- | --- | --- |
| System/interpreter installation | Python 3.15.0 or later | Runs the GUI and, by default, its backend |
| System/interpreter installation | Matching Tcl/Tk and working `tkinter`/`ttk` bindings | Provides the graphical toolkit; cannot be supplied by a venv alone |
| User session | Graphical desktop/display | Displays Tk windows; headless CLI operation is separate |
| Project `.venv` | Packages from `requirements-gui.txt` (currently Requests and its resolved dependencies) | Existing backend HTTP support |
| Optional `.venv` extra | Requests SOCKS extra, only for SOCKS proxy users | Adds PySocks support |
| Optional `.venv` packages on macOS/Windows | `requirements-gui-tray.txt`: pystray, Pillow, six and platform dependencies | Tray/menu-bar helper; no tray packages needed for taskbar-only mode |
| Separate working directory | Computation engine and its existing work/configuration files | Actual computation; engines are not Python GUI dependencies |

Users and testers need the same runtime environment. The initial automated tests
use standard-library `unittest` and disposable fixtures; no pytest,
Ruff, or Pylint installation is currently required. Backend dependencies should
be installed even for mocked integration tests that load backend definitions.
No real account, assignments, proof upload, or email send is needed for isolated
tests. Future dependency additions must update this table and the requirements
files in the same change.

### macOS with Homebrew

From the repository root (on this development machine,
`/Users/jacobpollicove/Git-Projects/autoprimenet`):

```sh
cd /Users/jacobpollicove/Git-Projects/autoprimenet
brew install python@3.15 python-tk@3.15
python3.15 --version
python3.15 -m venv .venv
.venv/bin/python -m pip install -r requirements-gui.txt
.venv/bin/python -m pip check
.venv/bin/python -m tkinter
```

Other contributors should replace the `cd` path with their checkout's actual
location. Homebrew installs native interpreter/Tk components outside `.venv`;
pip installs project packages inside it. Do not use `sudo pip` or modify Apple's
system Python. The final command should open a small Tk demonstration window;
close it after checking. If `_tkinter` is missing, fix the matching interpreter's
Tk installation rather than attempting `pip install tkinter`.

[Homebrew's Python 3.15 Tk formula](https://formulae.brew.sh/formula/python-tk@3.15)
documents the matching package. The
[python.org macOS installers](https://www.python.org/download/mac/tcltk/) provide
another route with bundled Tk; choose one interpreter and create the venv from it.
If `.venv` already exists, inspect its interpreter before reusing it; do not
overwrite an existing environment blindly.

### Windows (PowerShell)

Install Python 3.15 or later with Tcl/Tk support, then enter your checkout's root.
For a Python installation registered with the `py` launcher:

```powershell
py -3.15 --version
py -3.15 -m venv .venv
.\.venv\Scripts\python.exe -m pip install -r requirements-gui.txt
.\.venv\Scripts\python.exe -m pip check
.\.venv\Scripts\python.exe -m tkinter
```

If `py` is unavailable, use the full path of your chosen Python executable for
the first two commands. Calling the venv executable directly avoids activation
and PowerShell execution-policy changes.

### Linux and FreeBSD

Install Python 3.15 or later, its matching Tk bindings, venv support, and Tcl/Tk
through your distribution's supported installation method. Package names and
availability vary; a default `python3-tk` package may target an older Python and
must not be assumed to work with Python 3.15. A tray host or desktop extension
may also be needed for future Linux/FreeBSD tray support; it is not enabled yet.

From the checkout root, for an interpreter available as `python3.15`:

```sh
python3.15 --version
python3.15 -m venv .venv
.venv/bin/python -m pip install -r requirements-gui.txt
.venv/bin/python -m pip check
.venv/bin/python -m tkinter
```

Use the actual interpreter path if it has another name. A failed display test
may indicate a missing graphical session or display access, not a missing pip
dependency. Linux/FreeBSD setup and tray behavior have not yet been tested.

### Optional SOCKS proxies and environment records

On macOS/Linux/FreeBSD, install SOCKS support only if needed:

```sh
.venv/bin/python -m pip install 'requests[socks]'
```

On Windows, use `.\.venv\Scripts\python.exe` in place of `.venv/bin/python`.
For a test report, record the OS, desktop session, Python version, Tcl/Tk versions,
and installed package versions (`python -m pip list` using the venv interpreter).
Redact usernames, credentials, proxy URLs, and private paths before sharing.
The current requirements file declares runtime dependencies, not a tested lockfile.

### Launching the GUI

From the repository root on macOS/Linux/FreeBSD:

```sh
.venv/bin/python -B autoprimenet_gui.py
```

On Windows PowerShell:

```powershell
.\.venv\Scripts\python.exe -B autoprimenet_gui.py
```

For the experimental native tray/menu-bar helper on macOS or Windows, install
the optional dependency file in the same environment first:

```sh
.venv/bin/python -m pip install -r requirements-gui-tray.txt
```

On Windows substitute `.\.venv\Scripts\python.exe`. Without these packages, or
with the `--no-tray` launcher flag, close minimizes to the taskbar/Dock. The tray
menu shows the scheduled runner's current state and provides Start/Stop actions.
Closing the window keeps the GUI and any active scheduled monitoring running.
Start requires confirmation because it performs real server operations; simply
opening the GUI or refreshing a local preview does not.

Choose a working directory and press **Refresh preview** to inspect identity,
workers, configured request state, disk space, and local assignments. Settings
lets you choose a configuration filename within that directory. Preview limits
are 128 workers, 1000 total work lines, 2 MiB per file and 1 MiB per backend
request. Refresh does not save or lock these files, start computation software,
or contact PrimeNet. If files change while being read, refresh again; this is a
local snapshot rather than a synchronized view of an active computation engine.

Use **File → Quit** or the tray menu's Quit item to exit. If a bounded local
preview is still running, wait for it to finish and choose Quit again. The
Advanced tab provides a searchable flag reference and an advanced assignment
settings dialog described below. Notifications provides local SMTP configuration;
Logs & Status displays GUI activity only.

### Configuring AutoPrimeNet locally

Load a working directory with **Refresh preview** before editing. An existing
configuration is loaded without saving; a missing configuration starts with
backend defaults. Choose a computation program and provide a GIMPS username or
`ANONYMOUS` before the first save. These forms do not register the computer.

| Tab | Current graphical settings |
| --- | --- |
| PrimeNet | Username, computer name, progress check-in hours, expected computation hours per day |
| Workers | One of the eight supported computation programs, worker count, per-worker directories and preference codes |
| Assignments | Days of queued work and legacy extra-assignment cache |
| Settings | Work/results filenames, activity-log path, optional proof-archive directory |
| Advanced | Minimum/maximum exponent and factoring bit level, target factoring bits, P−1 tests saved/retry threshold/optimal bounds, ECM bounds multiplier/curve limit, LL↔PRP conversions, PRPLL certification enablement and daily time limit |
| Notifications | Send enablement, sender, recipients, SMTP server/username, SSL/TLS and StartTLS |

Choose **Edit advanced assignment settings…** to open the scrollable dialog.
Blank values use the backend default; boolean fields also offer explicit True
and False. **Apply to form** retains edits in the GUI; **Cancel** discards that
dialog's edits. **Save settings** performs offline backend validation and writes
the configuration. Merely opening or applying the dialog does not write files
or contact a server. These settings can affect assignment selection and rewrite
assignments when monitoring next runs. Opposite LL/PRP conversion directions
cannot both be enabled. The P−1 retry threshold applies with force P−1; optimal
bounds can also be used independently, following the CLI's semantics.

The searchable CLI reference includes a **GUI location** column for the current
configuration fields. Double-click a mapped row or press Return to select its
tab; advanced settings open with the relevant control focused. Unmapped rows
remain reference entries and do not imply implemented graphical parity.

Use **Apply worker count** after changing the count. Select a worker in the table
and choose **Edit selected worker…** to set its directory and preference. A blank
preference uses the backend's program default. A blank single-worker directory
uses the working directory; multiple non-PRPLL workers require distinct existing
directories. PRPLL uses one working directory and indexed work files, so its
worker-directory fields must be blank. This GUI currently supports 1–128 workers.

**Save settings** (also File → Save local configuration) asks for confirmation,
then validates the proposed values through AutoPrimeNet's parser, configuration
merge/decryption, and `check_options()` in an isolated, network-blocked process.
It does not run the CLI startup block or scheduler. Unsupported program/preference
combinations, conflicting conversions in existing settings, invalid limits,
missing directories, and other backend errors prevent saving.

Only changed form values are patched; unrelated keys, unknown sections, comments,
and existing ciphertext remain intact. Untouched interpolation and implicit
defaults remain as written. Enter literal text in the fields; new percent signs
are escaped automatically for the INI format. Clearing an optional field removes
its explicit override so backend defaults or INI inheritance apply. Edited
multiline values are refused rather than flattened. Password editing is not yet
available, and encrypted passwords are never shown in the forms.

### Notification configuration

Use the **Notifications** tab to edit the existing backend's email settings.
Provide both a From address and SMTP server when configuring email. Enter an
optional port as `hostname:port`. Recipients are comma-separated; surrounding
spaces are removed on an edited value. A blank recipient field uses the sender.
The backend's comma-separated format cannot represent a display name containing
a comma. Use plain email addresses for multiple recipients.

Choose SSL/TLS for a secure connection from the start or StartTLS to upgrade the
connection; both cannot be True. Blank boolean fields inherit INI/backend
defaults. The CLI defaults to port 465 with SSL/TLS and port 25 otherwise unless
you specify a port. Set **Send configured notifications** to False to suppress
notifications while retaining the SMTP configuration. Clearing that field
removes the explicit override, normally enabling configured notifications again.

**Save settings** validates and saves locally without sending a message or
contacting SMTP. The original backend validates addresses and required fields;
offline validation cannot confirm server reachability, credentials, certificate
validity or delivery. Scheduled monitoring may send the original backend's
notifications using these settings. Start confirms that possibility.

SMTP password editing, automatic server discovery, per-event notification
controls, and **Send test message** are not implemented yet. Existing plaintext
or encrypted password entries are preserved when editing the other notification
fields. Changing SMTP servers/usernames does not replace their saved password;
ensure the existing credential is appropriate before starting monitoring. The
GUI does not display passwords, decrypt them into a form, or convert plaintext
passwords into encrypted storage during Save.

Before replacement, the GUI acquires its `~gui-monitor.lock` scheduled-runner lock
and the same `~lock` instance lock as the CLI
and checks that the loaded configuration has not changed. Stop independently
running AutoPrimeNet before saving. The shared lock file is retained, never
deleted or truncated. A changed existing file is backed up as
`<config-name>.gui-backup-<unique-id>.bak` in the working directory, with
owner-only access where POSIX modes apply. Backups can contain existing
credentials and should remain private. A new configuration is also owner-only;
an existing configuration's POSIX mode is preserved. Extended ACLs and filesystem
metadata preservation have not been verified.

The replacement uses a flushed same-directory temporary file and atomic rename.
A second version check rejects external edits detected during validation. Editors
that ignore the shared lock can still race that final check; avoid editing the
same file concurrently. No-op saves retain exact bytes and do not create backups.
Read-only and symbolic-link configuration files are refused. Work, results and
certification files cannot be chosen as conflicting configuration destinations.

Changing program or computation hours resets cached speed/rolling estimates in
the same way as setup; unrelated state and inactive worker sections remain.
Reducing the active worker count does not delete any worker files. Refresh after
saving to update the displayed local snapshot. Reload or Quit asks before
discarding unsaved form changes; closing to the tray retains them in memory.

For backup recovery, stop the GUI and any AutoPrimeNet instance, review the
content of the desired `.bak`, and copy it back to the original configuration
filename using your file manager. Keep its permissions appropriate, then reopen
and refresh the GUI. Do not copy a backup over a work/results file.

The progress check-in interval is distinct from the scheduler's `--timeout`.
AutoPrimeNet does not persist `--timeout` through its INI mapping, so the GUI does
not add an INI field that pretends to control it. A validated saved
configuration is not evidence of registration, connectivity or successful server
operations. Full graphical CLI parity remains later work.

### Scheduled monitoring

Dashboard → **Start scheduled monitoring…** (or the tray Start item) asks before
starting a GUI-owned runner. Save or reload unsaved form changes first. The
runner checks the selected configuration's loaded fingerprint and performs
offline validation before any CLI cycle starts. Startup errors, changed source
files, an active independent CLI, or another GUI runner prevent startup.

This first mode runs the unmodified AutoPrimeNet CLI with `--timeout 0` now and
then at the configured **progress check-in interval**, in hours. Each pass can
register/update the computer, request/register work, report results/progress,
upload proofs, download certification starting data, check versions and send
existing configured notifications. Proof archival/deletion and all PrimeNet
business logic remain the CLI's existing behavior. For a previously unregistered
computer, a completed initial registration is followed by a work cycle unless
Stop was requested in between. No computation engine is launched or terminated.

The cadence intentionally matches the check-in interval in this scheduled mode;
it does not offer the native CLI's separate polling interval or immediate file
watchers yet. Results/proofs discovered between cycles wait for the next pass.
Changing the cadence requires stopping, editing/saving, and restarting. The
normal independent CLI remains available for its full native monitoring behavior.

Each Start creates an owner-private configuration snapshot named
`<config-name>.gui-monitor-backup-<unique-id>.bak` before beginning a cycle. The
unchanged CLI writes configuration/state normally and may normalize INI comments
and formatting; GUI save preservation cannot prevent that backend behavior.
This snapshot protects the original configuration, not server reservations or
computation checkpoints. Restoring it cannot undo server operations.

Dashboard and tray state distinguish Starting, Running cycle, Waiting, Stopping,
Stopped and Failed. The displayed last-cycle timestamp is local process
completion, and the next-cycle time is a plan. Exit zero is not proof that every
server operation succeeded: some existing CLI paths log errors without returning
a failing exit code. Connectivity and per-operation acceptance stay unverified;
review AutoPrimeNet's configured log for detailed results. Raw CLI output and
credentials are not copied into GUI activity, whose display is capped at 2000
lines. Refresh local snapshots to inspect current files.

**Stop after current cycle** prevents another pass and interrupts an idle wait.
It lets an active CLI cycle finish its writes/uploads before exiting. This can
take time during retries, a large proof upload, or waits on an existing `.lck`.
**Force stop…** requires a separate confirmation and terminates only the owned
CLI child; it can interrupt a write/upload and leave sidecar locks. Those locks
are never removed automatically. Inspect the affected workspace before restarting
after a forced stop. Neither stop action unreserves work or changes QuitGIMPS.

Closing the window hides/minimizes it while monitoring continues. **Quit** asks
to stop monitoring, waits for the current cycle to finish, then closes the GUI
and tray helper. A force-stop control remains reachable while Quit is waiting.
If the GUI process disappears unexpectedly, pipe EOF requests a graceful runner
shutdown; it may still wait for the active cycle. This is not a guarantee of
immediate shutdown when files or network operations are blocked.

The GUI holds `~gui-monitor.lock` across cycles to prevent duplicate GUI runners
and configuration saves. Each CLI pass holds its own normal `~lock`. An independent
CLI can start between passes; a subsequent conflicting pass fails its native
lock and the GUI runner stops, without terminating the independent process.
Lock files can remain after exit; existence alone does not mean an OS lock is
held. Do not delete them to bypass a live process. Refresh after stopping before
editing/restarting, because the CLI may have updated configuration/state.

Automated tests use disposable workspaces and simulated cycles. A live monitoring
trial has not been performed. Starting against a real workspace is an operational
action with the side effects above, not a read-only test.

### Local files and Git hygiene

The new `.gitignore` excludes local environments, bytecode/tool caches, build and
test output, editor/OS state, local `.env` secrets, and common root-level
AutoPrimeNet runtime files. Keep real computation workspaces outside the source
checkout. Use `.local-work/` for disposable local fixtures and `test-output/` for
generated reports; these directories are ignored. Intentional reusable test
fixtures belong under `tests/` and should remain eligible for version control.

Custom configuration filenames, arbitrary worker directories, proof archives,
and engine checkpoints cannot all be safely identified by broad ignore rules.
Keep them outside the checkout or add local-only patterns to `.git/info/exclude`
yourself. Review `git status --short` before staging. `.gitignore` does not protect
tracked upstream files from edits or prevent changes to files already tracked.
The GUI additions leave the original CLI files unchanged.

## Validation and tooling

- Test GUI startup, forms, background operations, configuration handling, and
  backend integration on Python 3.15.0, then on selected later releases.
- Reject older interpreters with a clear version message before importing
  supporting GUI modules. The small launcher version check must itself use
  syntax understood by the older interpreters it is intended to diagnose.
- Scope future GUI linting and test configuration to the GUI's minimum version.
  The existing repository-wide Ruff and Pylint settings target older versions;
  changing them globally could affect the independent CLI and requires review.
- Preserve the CLI's independence by avoiding imports of GUI code from existing
  CLI entry points.
- Target macOS, Windows, Linux, and FreeBSD where practically testable. Record
  actual runtime/platform results; intended support is not evidence of testing.

The development environment now has Python 3.15.1, working Tcl/Tk 9.1.0 bindings,
and Requests inside `.venv`. A real Tk window smoke check has passed on macOS.
The user also confirmed the manual macOS hide/reopen/Quit test passed.
Complete GUI, Python 3.15.0-floor, and cross-platform validation remain pending;
see [GUI_DEVELOPMENT.md](GUI_DEVELOPMENT.md) for the scope of actual checks.
