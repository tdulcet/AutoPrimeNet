# AutoPrimeNet GUI

The optional Tkinter/ttk GUI provides configuration forms with validated saving,
local previews, native scheduled monitoring and file watching, confirmed one-shot
commands, graphical computer/exponent registration, and private reports. Optional
tray integration supports macOS, Windows and compatible Linux/FreeBSD desktops.
Starting monitoring or confirming a server/email command performs real external
operations.

The ordinary CLI parser-entry inventory is covered, but platform and live-service
acceptance remain pending. This is not a validated release. See
[GUI_PARITY.md](GUI_PARITY.md) for the audited inventory and explicit limits,
[GUI_DEVELOPMENT.md](GUI_DEVELOPMENT.md) for automated test evidence, and
[GUI_ACCEPTANCE.md](GUI_ACCEPTANCE.md) for the consolidated acceptance checklist.

## Features

* Graphical configuration, worker editing and validated local saving
* Offline assignment and exponent-registration previews
* Confirmed computer registration and one-shot CLI operations
* Native monitoring, file watching and graceful worker shutdown
* Optional tray/menu-bar integration with a reachable fallback
* Reviewed GPU/SMTP discovery, masked password replacement and private reports

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

## Upstream file preservation

The implementation should consist entirely of new files wherever feasible.
Preserve all original upstream files, including source, documentation, dependency
declarations, and CI/lint configuration. Avoid unrelated cleanup and refactoring.

Before changing any original file:

1. Explain the specific requirement that makes the change necessary and identify
   the affected file and code path.
2. Explain why an implementation using only new files is insufficient.
3. Present the smallest proposed change, its effects on existing behavior, and
   the validation needed.
4. Obtain the user's explicit approval before applying it.

For each approved exception, document the rationale, alternatives considered,
exact scope, and validation results in the GUI development documentation and
eventual proposed pull request description. Keep untested behavior explicit.

No original upstream file changes have been approved or made for the GUI.

## Background operation and window closing

The intended default is **close to tray/menu bar and keep monitoring**. Closing
the main window hides it while both the GUI and its managed AutoPrimeNet backend
remain running. This differs from exiting the GUI and leaving a detached backend.

* Windows: use the notification area (system tray).
* macOS: use a menu bar status item.
* Linux and FreeBSD desktops: use an available compatible tray/status-item host.
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

The GUI uses optional `pystray` in a separate child process with its own
native event loop. Tkinter does not directly provide a portable tray API; using
this library avoids maintaining separate native tray implementations. Its LGPLv3
license is compatible with the GUI's GPLv3 licensing. Dependencies include Pillow,
six, and platform bindings (PyObjC Cocoa/Quartz on macOS). These packages are not
required by the CLI. They are declared separately in `requirements-gui-tray.txt`.

Native tray integration has been programmatically tested on macOS with Python
3.15.1. Windows remains untested. Linux/FreeBSD have optional GTK tray integration
with taskbar fallback; their actual tray hosts have not yet been validated.
This follows the event-loop and
desktop constraints described in
[pystray's integration documentation](https://pystray.readthedocs.io/en/latest/faq.html).
If the helper fails while hidden, the GUI restores itself. The helper also exits
when its parent closes its input pipe, including after a parent-process failure.

## Installation

These instructions prepare an environment for the current GUI foundation. The
backend and opt-in desktop test suites are documented in
[GUI_DEVELOPMENT.md](GUI_DEVELOPMENT.md). Live PrimeNet monitoring has not been
validated; automated checks use simulated service responses, with native macOS
tray and filesystem-event integration checks. Parser-entry coverage is complete
within the documented limits; live-service and platform acceptance remain pending.
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
| System/interpreter library, required for password replacement or existing encrypted passwords | Loadable OpenSSL `libcrypto` compatible with the original backend | Existing AES-256-GCM password encryption; this is a native library, not a pip package |
| Optional `.venv` packages on macOS/Windows | `requirements-gui-tray.txt`: pystray, Pillow, six and platform dependencies | Tray/menu-bar helper; no tray packages needed for taskbar-only mode |
| Optional system and `.venv` packages on Linux/FreeBSD | Native GTK 3, GObject introspection, Cairo and a tray host; `requirements-gui-tray-gtk.txt` in the selected venv | Optional GTK/AppIndicator tray helper; see the GTK installation section |
| Separate working directory | Computation engine and its existing work/configuration files | Actual computation; engines are not Python GUI dependencies |

Users and testers need the same runtime environment. The initial automated tests
use standard-library `unittest` and disposable fixtures; no pytest,
Ruff, or Pylint installation is currently required. Backend dependencies should
be installed even for mocked integration tests that load backend definitions.
No real account, assignments, proof upload, or email send is needed for isolated
tests. Future dependency additions must update this table and the requirements
files in the same change.

### macOS with Homebrew

From your source checkout:

```sh
cd /path/to/autoprimenet
brew install python@3.15 python-tk@3.15
python3.15 --version
python3.15 -m venv .venv
.venv/bin/python -m pip install -r requirements-gui.txt
.venv/bin/python -m pip check
.venv/bin/python -m tkinter
```

Replace the `cd` path with your checkout's actual location. Homebrew installs native interpreter/Tk components outside `.venv`;
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
may also be needed for optional Linux/FreeBSD tray support (see below).

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

For the optional native tray/menu-bar helper on macOS or Windows, install
the optional dependency file in the same environment first:

```sh
.venv/bin/python -m pip install -r requirements-gui-tray.txt
```

On Windows substitute `.\.venv\Scripts\python.exe`. Without these packages, or
with the `--no-tray` launcher flag, close minimizes to the taskbar/Dock. The tray
menu shows the scheduled runner's current state and provides Start/Stop actions.
Closing the window keeps the GUI and any active scheduled monitoring running.
Use **Settings → Retry tray integration** after fixing optional dependencies or
re-enabling a desktop tray host. Retry does not restart monitoring.
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
Logs & Status includes GUI activity, a separate private native-log viewer,
original work-status reporting and offline diagnostic export.

### Optional Linux/FreeBSD GTK tray integration

The optional helper now attempts menu-capable GTK 3/AppIndicator backends on
Linux and FreeBSD. Native toolkit work runs in its own process, separate from
Tkinter. Base GUI use still needs only requirements-gui.txt and matching Tk;
GTK/GObject dependencies are optional. Real Linux/FreeBSD desktop acceptance is
pending; current tests simulate GTK/D-Bus behavior on the macOS development host.

For this optional feature, the **system** needs GTK **3**, GLib/GIO/GObject
introspection runtime data, Cairo and any build tools/headers required by the
chosen PyGObject build, including headers for the chosen Python 3.15+ interpreter.
The desktop must provide a tray host. For AppIndicator menus, install compatible
AppIndicator3 or AyatanaAppIndicator3 libraries and their introspection data.
Packages and desktop extensions vary by distribution; use its supported package
manager and the [PyGObject installation guide](https://pygobject.gnome.org/getting_started.html)
for build prerequisites. That guide's GTK 4 example does not replace this helper's
GTK 3 requirement. A system Python's `gi` module may not match your 3.15 venv;
do not copy or symlink another interpreter's extension modules into it.

Install the **venv** packages after the native prerequisites are available:

```sh
.venv/bin/python -m pip install -r requirements-gui-tray-gtk.txt
.venv/bin/python -m pip check
.venv/bin/python -c "import gi; gi.require_version('Gtk', '3.0'); from gi.repository import Gtk; print(Gtk.get_major_version())"
```

This adds pystray/Pillow and PyGObject to the selected venv; pip may build native
Python bindings locally. See [pystray's virtualenv guidance](https://pystray.readthedocs.io/en/latest/faq.html).
For a running session with a registered StatusNotifier visualization host, the
helper prefers AppIndicator and falls back to GTK if its typelib is unavailable.
Otherwise it tries GTK's legacy status icon. An explicit `PYSTRAY_BACKEND`
selection is respected. XOrg-only pystray backends without menus are refused so
the window cannot be hidden behind an icon lacking the required menu controls.

Readiness requires a menu and a detected host: GTK uses its
[embedded status-icon check](https://docs.gtk.org/gtk3/method.StatusIcon.is_embedded.html),
while AppIndicator checks the local session bus's
[registered StatusNotifier host](https://specifications.freedesktop.org/status-notifier-item/latest/status-notifier-watcher.html).
A watcher service alone is insufficient. The D-Bus property call has a one-second
timeout and does not request watcher-service autostart. The helper allows five
seconds for initial embedding, then checks host availability every two seconds.
If no host appears, a backend fails, or a host disappears later, the tray helper
stops and the GUI returns to its reachable window/taskbar behavior. These checks
cannot guarantee that a desktop visibly exposes an icon hidden by user policy.

The GUI aborts a helper that has not become ready within 15 seconds. Menu events
from stopped/replaced helpers are ignored; their shutdown targets only their own
process. Use **Settings → Retry tray integration** after the panel, extension or
libraries are ready. A retry during startup does not create a duplicate helper.
As before, `--no-tray` disables automatic startup; Retry is an explicit opt-in.
No tray lookup contacts PrimeNet or a mail provider, or changes assignments.

## Usage

### Configuring AutoPrimeNet locally

Load a working directory with **Refresh preview** before editing. An existing
configuration is loaded without saving; a missing configuration starts with
backend defaults. Choose a computation program and provide a GIMPS username or
`ANONYMOUS` before the first save. These forms do not register the computer.

For a new workspace:

1. Select the computation engine's working directory using **Browse**, or enter
   its path and select **Refresh preview**. This is the directory containing
   the engine's work files, which may differ from the GUI source checkout.
2. In **PrimeNet**, supply your GIMPS username or the literal `ANONYMOUS`.
3. In **Workers**, select the computation program and apply the intended worker
   count; configure per-worker directories where needed.
4. In **Settings**, match the work/results filenames to the engine. Ubuntu's
   packaged Mlucas 20.1.1 uses `worktodo.ini` and `results.txt`; explicitly change
   the GUI's default `worktodo.txt` for this setup. Program selection does not
   automatically change the work filename.
5. Valid form edits save automatically after a two-second pause, once all editor
   dialogs have closed. Apply a dialog's changes to include them; Cancel does
   not apply its draft. Wait for the successful-save/automatic-refresh status.
   **Save settings** remains available to save immediately with confirmation.
   A validation failure leaves edits unsaved and displays an error; correct it
   before refreshing. Decline any discard prompt to retain those edits.
6. The preview refreshes automatically after saving. After quitting and reopening, reselect
   the same working directory and configuration filename to reload them. The GUI
   does not currently remember the last directory between launches. Keep
   monitoring stopped until engine setup and intended live operations are ready.

| Tab | Current graphical settings |
| --- | --- |
| PrimeNet | Username, computer name, progress check-in hours, expected computation hours per day; hardware/resource settings dialog |
| Workers | One of the eight supported computation programs, worker count, per-worker directories and preference codes |
| Assignments | Days of queued work and legacy extra-assignment cache |
| Settings | Work/results filenames, activity-log path, optional proof-archive directory; connection/password management; version-check channel/enablement and native console-color preference |
| Advanced | Minimum/maximum exponent and factoring bit level, target factoring bits, P−1 tests saved/retry threshold/optimal bounds, ECM bounds multiplier/curve limit, LL↔PRP conversions, ≥100M-digit prime reporting policy, PRPLL certification enablement and daily time limit |
| Notifications | Send enablement, sender, recipients, SMTP server/username, SSL/TLS, StartTLS and new-prime sound suppression |

Choose **Edit advanced assignment settings…** to open the scrollable dialog.
Blank values use the backend default; boolean fields also offer explicit True
and False. **Apply to form** stages edits for automatic saving; **Cancel** discards
that dialog's edits. Opening a dialog does not save it. Automatic saves and
**Save settings** perform offline backend validation before writing; neither
contacts a server. These settings can affect assignment selection and rewrite
assignments when monitoring next runs. Opposite LL/PRP conversion directions
cannot both be enabled. The P−1 retry threshold applies with force P−1; optimal
bounds can also be used independently, following the CLI's semantics.

The searchable CLI reference includes **GUI location** and **Coverage** columns
for every audited parser entry. Double-click a mapped row or press Return to
select its tab; dialog settings open with the relevant control focused, while
operation rows focus their button without executing it. Partial/CLI-only entries
describe remaining limitations. **Help → Original CLI help** displays the
original parser's complete visible help offline without needing a workspace.
**Help → About** includes the audited backend version.

Use **Settings → Edit monitoring and output preferences…** for version checks,
alpha/beta/stable preference and native CLI console color. Saving performs no
update check. These settings apply when the original backend next runs; console
color does not style the GUI or plain backend log. The Advanced reporting policy
can withhold prime results at or above 100 million digits, matching the CLI's
`--no-report-100m` option; configure another notification method if enabling it.

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
multiline values are refused rather than flattened. Saved passwords are never
shown in the forms; use the password-management dialog to replace or remove them.

The GUI preserves an existing UTF-8 byte-order mark during local editing, but
the audited original CLI cannot read BOM-prefixed INI files. Runner startup
therefore refuses them before launching a CLI command. Keep a private backup,
use your text editor to save the INI as **UTF-8 without BOM**, then refresh the
GUI. This limitation was verified with the original CLI; no upstream source was
changed to alter its encoding behavior. New GUI-created configurations already
use UTF-8 without BOM.

### Hardware and resource settings

On **PrimeNet**, choose **Edit hardware and resource settings…** to configure
the values AutoPrimeNet reports during computer registration and updates:

| Setting | Unit or meaning |
| --- | --- |
| Processor model and features | CPU or GPU description and feature text |
| Processor frequency | MHz |
| Total physical memory | MiB; stored as the lowercase `memory` option |
| Maximum stage 2 memory | MiB for P−1/P+1/ECM; stored as the uppercase `Memory` option |
| Proof residue disk limit | GiB per worker; 0 omits this value from reporting |
| L1 data, L2 and L3 cache | KiB |
| Physical cores | Processor core count |
| Threads per core | 0 means unknown, 1 means no hyperthreading |

Blank fields retain INI inheritance or the original backend's hardware
detection/defaults. The GUI does not automatically select a GPU. To report GPU
hardware instead of the detected CPU, enter the relevant values explicitly.
The dialog does not display an inventory of detected hardware yet.

**Apply to form** retains edits in the main form; **Cancel** discards the
dialog's edits. **Save settings** validates offline and saves locally. Maximum
stage 2 memory cannot exceed total physical memory. When reducing total memory,
also specify a suitable maximum: a blank maximum still uses the backend's
default based on detected system memory. Numeric fields use the original CLI's
integer/decimal types, with nonfinite values rejected.

These settings describe the computer to AutoPrimeNet and PrimeNet; they do not
change operating-system limits or configure Mlucas, PRPLL or another computation
program. Saving does not register a computer or send a hardware update. A later
monitoring cycle can report the settings. The CLI may subsequently update its
configuration, so stop monitoring and refresh before editing again.

### Discovering GPUs

In **PrimeNet → Edit hardware and resource settings → Detect GPUs**, the GUI
calls the original local OpenCL/CUDA/NVML discovery functions in its isolated,
network-blocked helper. Installed vendor drivers determine what can be detected;
no additional Python package is required. Discovery may show duplicate devices.
Choose the device used by your computation program, review the proposed values,
and select **Use in hardware dialog**, then **Apply to form** and **Save settings**.
Cancel leaves the form unchanged. Nothing is saved or sent during discovery.

The selected GPU changes hardware reported to PrimeNet; it does not select a
GPU for your computation engine. The mapping follows original setup: processor
name/features/frequency, total memory and 90% stage 2 memory, cores and one thread
per core when available, and cache overrides when both caches are available.
Unknown cores/caches retain existing values; review these before saving. No GPUs
or a driver failure leaves manual editing available. CPU defaults still apply
when no hardware overrides are supplied. Native driver behavior on Windows,
Linux and FreeBSD still requires platform testing.

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

Automatic server discovery and per-event notification controls are not
implemented yet. **Send test email…** is a confirmed one-shot action described
below. Changing SMTP servers/usernames does not automatically replace their
saved password; use password management as needed.

### Discovering an SMTP provider

Choose **Notifications → Discover SMTP provider** and enter a sender address
(optionally including its display name). **Look up provider** asks for confirmation
before any network access. It uses the original provider-autoconfiguration code,
including provider endpoints, the Mozilla ISP database, and DNS-over-HTTPS
fallbacks. The sender address may be included in provider requests; lookups may
use unencrypted HTTP or unsigned DNS. Review returned settings with your provider.

Lookup uses **saved** proxy settings, including saved proxy credentials, and the
normal system proxy environment. Save connection edits first. It runs in a
separate helper with an eight-second timeout per request and a 90-second overall
limit. Closing the dialog discards its result; an in-flight lookup may continue
until completion or timeout. Retry Quit after this bounded job finishes. Discovery does not
send an SMTP password, email, or PrimeNet request and creates no runtime files.
The original offline bridge continues to reject network-enabled operations.

Review provider, SMTP server/port, connection security and optional username,
then choose **Apply to form**. This replaces those form fields and the sender
address. An unknown username retains the existing username; review it manually.
A changed sender or workspace requires another lookup. Unknown connection
security is rejected; explicitly advertised plain SMTP is shown as `plain` with
both TLS switches off. Passwords, recipients and notification send policy remain
unchanged. Applied values enter the automatic-save workflow. A test email remains a separate,
confirmed operation. Empty results or errors leave manual SMTP editing available.

### Connections and passwords

In **Settings**, choose **Edit connection settings…** to set proxy type, server,
username and the original backend's encryption policy. Proxy fields require a
proxy server; SOCKS types require the optional Requests SOCKS extra described
above. Enter credentials separately rather than embedding a password in the
server URL. Saving validates syntax offline and cannot confirm proxy access.

The encryption policy follows the CLI: True requires encryption, blank uses its
opportunistic default, and False disables encryption. Existing encrypted
passwords require True or blank. Regardless of that policy, the GUI always
requires successful encryption for a newly entered password and refuses to save
a replacement when encryption is disabled or OpenSSL is unavailable.

Choose **Manage SMTP and proxy passwords…** in Settings or Notifications:

| Action | Effect when applied to the form |
| --- | --- |
| Keep | Retains the saved password and any already pending change |
| Replace | Stages the newly entered, masked password |
| Remove | Stages removal of both plaintext and encrypted entries |
| Use saved | Cancels a pending change for that password |

**Apply to form** stages changes; **Cancel** discards edits made in that dialog.
**Save settings** encrypts replacements through the original backend, validates
the resulting configuration and writes atomically with a private backup. No
server is contacted. Passwords can include spaces and percent signs; replacement
values must be 1–4096 characters without line breaks or NUL. Existing passwords
are never populated into the entry fields, and entries are cleared when the
dialog closes. Pending replacements stay in process memory until saved or
discarded; they are sent to the offline helper through stdin, never argv.

Only explicitly selected passwords change. Other plaintext/ciphertext entries
remain as written; Save does not automatically migrate old plaintext passwords.
To migrate one, choose Replace and re-enter it. The original backend's
hardware-GUID binding is saved with new ciphertext and retained for later edits.
Encrypted credentials are not portable between systems under the backend's
rules. Passwords inherited from `[DEFAULT]` must be adjusted outside the GUI.
The hidden legacy account-password flag remains unsupported by the original
backend; these controls cover SMTP and proxy authentication only.

Backups preserve the original file, including any old plaintext passwords.
Protect those backups with the same care as the configuration. The GUI does not
verify credentials or delivery when saving. Testing email requires the separate,
confirmed **Send test email…** command.

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
Read-only and symbolic-link configuration files are refused. Configuration and
work previews read bounded regular files and check the opened file and pathname
for replacement or modification during reading. Nonregular work-file paths and
broken work-file links are reported explicitly. Read-only work previews may
follow a link to a regular file; this does not relax the separate no-symlink
rules for configuration saving or assignment snapshots. On POSIX systems,
nonblocking opens prevent a file replaced by a FIFO from waiting for a writer.
These checks do not guarantee a timeout for an unresponsive network filesystem.
Configuration, log, work, results, certification, sent-history, import and lock
paths must not overlap, including effective indexed PRPLL filenames and detected
symlink/hard-link aliases and the five rotated-log destinations. Existing runtime
file paths must be regular files. Proof archive directories must have a separate
path. Validation runs before saving and again during runner preflight. These
checks do not prevent a noncooperating program replacing paths after validation.
Case-only names are compared using the macOS volume's case-sensitivity policy
and Windows path normalization; distinct names on a case-sensitive volume remain
distinct.

Reloading or saving a configuration closes old settings/worker/password dialogs,
clears unapplied password entries and closes the saved configuration's old log
viewer. A failed workspace change retains the unsaved form values and their
dirty state. Queued exponent drafts still require a fresh preview after a saved
document changes.

Changing program or computation hours resets cached speed/rolling estimates in
the same way as setup; unrelated state and inactive worker sections remain.
Reducing the active worker count does not delete any worker files. Saves and
completed backend runs automatically reload configuration and refresh the local
snapshot after the owned runner exits. This includes one-shot commands, one-pass
monitoring and normal Stop. Live operations still require their confirmations.

Automatic saving waits while an editor or registration dialog is open, a local
job is running or monitoring owns the workspace. A failed save is reported once
per attempted edit/save; it is not repeatedly retried until another edit or
explicit save. External-file conflicts retain both the file on disk and the GUI
draft, requiring deliberate resolution. Automatic refresh never discards a dirty
configuration or changes the selected workspace. A pending registration batch is
retained but its old preview is invalidated when configuration reloads.

Quit flushes a pending form save before exiting when no draft dialog is open;
failed validation/conflict keeps the window and edits available. With an open
dialog or queued batch, the discard confirmation still applies. Closing to the
tray keeps the application running and allows eligible automatic saves.

For backup recovery, stop the GUI and any AutoPrimeNet instance, review the
content of the desired `.bak`, and copy it back to the original configuration
filename using your file manager. Keep its permissions appropriate, then reopen
and refresh the GUI. Do not copy a backup over a work/results file.

The progress check-in interval is distinct from the polling interval (`--timeout`).
Use **Settings → Edit monitoring and output preferences** to set polling seconds
and native file watching. The GUI saves polling in `[GUI] PollSeconds`, because
the original CLI does not persist `--timeout`; the GUI passes this value explicitly
to its owned runtime. Standalone CLI users must still supply `--timeout` themselves.
The watch preference is the original `[PrimeNet] watch` setting and also applies
to the standalone CLI. A validated configuration is not evidence of registration,
connectivity or successful server operations.

### One-shot commands

Save or reload unsaved edits before running these commands. Each button asks
for confirmation, describing its effects and showing the related CLI flags:

| Tab and action | Original CLI flags | Effect |
| --- | --- | --- |
| PrimeNet → Ping PrimeNet… | `--ping` | Contacts the normal PrimeNet API and logs its response/version information |
| PrimeNet → Ping experimental v6 API… | `--ping --v6` | Pings the experimental endpoint; does not switch assignment operations to v6 |
| PrimeNet → Register or update computer… | Graphical `--setup` completion | Sends saved registration/program settings without terminal prompts or automatic work fetching |
| Notifications → Send test email… | `--test-email` | Sends the backend's test message to configured recipients |
| Assignments → Report results… | `--report-results` | Submits pending results for all configured workers |
| Assignments → Report results and upload proofs… | `--upload-proofs` | Reports results and uploads available PRP proofs, using configured archive/delete behavior |
| Assignments → Pause new-work requests… | `--no-more-work` | Sets local QuitGIMPS policy; existing computation/reservations continue |
| Assignments → Resume new-work requests… | `--resume-work` | Removes QuitGIMPS policy; future cycles may request new assignments |
| Assignments → Recover assignments… | `--recover` | Reports results and overwrites work/certification files with recovered assignments |
| Assignments → Recover all assignments… | `--recover-all` | Also includes expired PrimeNet work and broader TF1G recovery |
| Assignments → Unreserve an exponent… | `--unreserve EXPONENT` | Releases/removes the first locally matching exponent across workers |
| Assignments → Unreserve all assignments… | `--unreserve-all` | Reports results and releases assignments represented by configured workers |
| Assignments → Register exponent batch… | Graphical `--register-exponents` | Opens a batch form and offline preview; contacts PrimeNet only after typed confirmation |
| Logs & Status → Write work status to backend log… | `--status` | Writes the original queued-work/ETA report to the configured native log |

The email test requires a saved SMTP server, From address and notification
sending enabled. Its message contains version, username, computer name and GUID
information. Confirm it only when ready to send to the configured recipients.
The proof action can archive/delete successfully uploaded proofs. Result/proof
actions can update local state, result files and server reservations, and send
configured notifications. Do not run them against real assignments merely to
exercise the GUI.

These commands use the original backend once with `--timeout 0`; they do not
start a scheduled loop or add the new-computer registration follow-up used by
scheduled monitoring. Registration uses private graphical-input adapters around
the original startup/main functions, described below. Other actions use the
unchanged CLI entry point. The helper checks the saved fingerprint, validates
offline and creates the same private `.gui-monitor-backup-*.bak` configuration
snapshot used by monitoring. This backup does not undo server actions or recover
deleted/archived proofs or changed result files. Original CLI configuration
writes can normalize comments/formatting.

One command or scheduled monitor can run per GUI at a time. Settings, Save and
other command buttons remain disabled until it exits. The same runner/native
locks protect against overlapping GUI/CLI operations. Dashboard shows lifecycle
state; closing retains background execution. **Stop after active work** lets
an active command finish, while a stop received during startup can cancel it
before execution. **Force stop…** can interrupt writes/uploads and requires a
separate confirmation. **Quit** waits asynchronously for the owned command.

CLI output remains in the configured AutoPrimeNet log rather than being copied
into GUI activity; open the separate private log viewer to read it. A zero exit
code records local completion only; some CLI paths
log server errors without returning failure. The GUI therefore leaves server
acceptance and message delivery unverified. Review the log; local snapshots
refresh automatically after completion. CLI-reference navigation focuses the corresponding
button without running it. Server acceptance remains unverified until you review
the original log and relevant server state.

### Graphical computer and exponent registration

Configure username, program, workers and optional hardware/notification settings,
then **Save settings**. Choose **PrimeNet → Register or update computer…** when
ready to send them to PrimeNet. The private adapter executes the original CLI's
startup, then enters its setup-completion branch with saved graphical values.
It calls the original computer-registration and program-options routines,
including their configuration updates and server overrides, without running the
terminal setup questions, automatically sending test email or fetching work.
The workspace refreshes automatically afterward. GPU discovery is available in the hardware dialog, and
SMTP-provider discovery is available in Notifications (see below).

For explicit exponents, choose **Assignments → Register exponent batch…**:

1. Select one configured worker and a supported work type.
2. Enter the explicit parameters, then **Add row**. Select a queued row to load
   its values; use **Replace selected row** or **Remove selected row** as needed.
   Editing draft fields alone does not change a queued row.
3. Choose **Validate and preview offline**. The original registration constructor
   and formatter generate canonical work lines in memory, with no files written
   or network access. Composite exponents and invalid known factors are rejected
   using the original backend's checks. Changing the worker or queued rows
   invalidates the preview.
4. Review the queued rows and scrollable work-line preview. Choose **Register
   validated batch…** only when ready, pause the affected computation engine,
   and type `REGISTER N`, where N is the batch size.

The eight original work types are trial factoring, P−1 with bounds, P−1 factoring,
ECM, LL, LL double-check, PRP and PRP double-check. Fields enable according to the
selected type and engine: TF bits/end bits, prior P−1 state, tests saved, P−1/ECM
B1/B2, ECM curves, PRP base/residue type and known prime factors. The dialog does
not infer these values from mersenne.ca; enter them explicitly. Known factors
are comma-separated and must divide the Mersenne number with their supplied
multiplicity. PRP double-check known factors require residue type 5, matching
the original workflow. Use work types supported by your computation engine;
offline preview is not a server capability or acceptance check.

GUI resource limits are one worker, 1–100 queued rows, a normalized plan up to
48 KiB, at most 32 known factors per row, and integer inputs/factors up to 1024
bits. Exponents and other type-specific ranges follow the original prompts;
nonfinite numeric values and duplicate work-type/exponent pairs within a batch
are refused. Cancel discards the in-memory queue. Reload/Quit asks before
discarding queued rows. A preview result arriving after the dialog closes is
discarded safely. Queues are not persisted across application restarts.

Live registration requires an existing computer GUID and reruns offline
validation in the supervisor before creating private work/certification
snapshots. The adapter supplies only reviewed, validated answers to the original
registration prompts; unexpected/repeated prompts fail rather than opening a
terminal. It appends the batch to the selected worker and then registers **all
unregistered work already in that worker's file**, as the original command does.
Configured conversions/factoring adjustments can rewrite work lines. Selected
worker directories and PRPLL indexed files follow the original CLI's behavior.

The adapter executes the hash-guarded original source without editing it. Plan
data travels through stdin rather than command-line arguments, and the child
rechecks the saved configuration fingerprint. Failures can leave appended or
partially registered work, just as the original workflow can; snapshots do not
undo server changes. Stop/Force/Quit retain the existing owned-process semantics.
Inspect the original log after completion; the workspace refreshes automatically.
Automated tests use simulated registration API responses. Manual Ubuntu testing
confirmed computer registration; live exponent registration remains unverified.

### Native logs, work status and private diagnostics

**Logs & Status → Write work status to backend log…** runs the original
`--status` workflow once, reading available computation progress and estimates.
It can normalize configuration during CLI startup but does not fetch assignments
or submit results. Choose **View private backend log…** to read the configured
log in a separate, read-only window. Refresh reads at most the latest 128 KiB and
2000 lines, without loading the whole file. Missing, symlink or nonregular logs
are refused. Log viewing can remain available during monitoring; it is a snapshot
of changing output, not a synchronized live feed. Native log contents can include
private account/path details or verbose diagnostics and are not copied into GUI
activity.

**Export private diagnostics…** asks before running the original `debug_info`
function in the network-blocked offline bridge. It creates a new owner-private
`.gui-debug-report-<id>.txt` in the workspace, showing its path in GUI activity.
The report includes software/runtime, detected hardware and private identifiers,
including username/computer GUID; review and redact before sharing. Configured
password values are redacted from the returned report. Configuration, work and
checkpoint files are not changed. A changing configuration or an oversized
report prevents export. Existing files are never overwritten. The file is local
only; there is no automatic upload, email or public bug-report submission.

### Recovery, unreservation and new-work policy

**Pause new-work requests** and **Resume new-work requests** are local policy
commands. They do not stop computation, stop monitoring, release reservations,
or fetch work immediately. The preview refreshes afterward to show the configured
request state. Stop an active GUI runner before changing this policy.

Pause affected computation engines before recovery or unreservation. The GUI
does not pause them for you. Recovery replaces the work and certification files
for the active worker configuration and requires an existing computer GUID.
**Recover all** additionally includes expired PrimeNet assignments and can
recover TF1G reservations from all systems/workers into the first worker, under
the original backend's rules. Recovery may report pending results first.

**Unreserve an exponent** opens an integer form, prefilled from the selected
local table row when available. The CLI operates on the **first matching
exponent across configured workers**, regardless of which worker/AID row was
selected. The helper verifies that the exponent still appears in the current
local work files before launch. This is not confirmation of a server reservation.
Use it only when you will not finish that assignment. **Unreserve all** reports
pending results and releases assignments represented by the active workers;
for TF1G it can release all assignments associated with a worker.

These four commands require an exact typed confirmation:

| Command | Required phrase |
| --- | --- |
| Recover assignments | `RECOVER` |
| Recover all assignments | `RECOVER ALL` |
| Unreserve exponent 127 (example) | `UNRESERVE 127` |
| Unreserve all assignments | `UNRESERVE ALL` |

Before launch, the helper creates an owner-private directory named
`.gui-assignment-backup-<unique-id>` in the workspace. It snapshots each active
worker's work and certification files byte-for-byte, including PRPLL's indexed
filenames, and records absent files in `manifest.json`. The manifest identifies
original paths, backup filenames, sizes and SHA-256 hashes. GUI activity records
the snapshot directory. Finder and other file managers may hide dot directories;
on macOS, Command–Shift–Period shows them.

Snapshots refuse symlinks, nonregular files, files over 2 MiB, combined contents
over 16 MiB, or detected concurrent changes. A snapshot failure prevents launch
and removes its incomplete directory. The native CLI instance lock is held
during this preflight, but computation engines can still alter files afterward.
These are point-in-time copies, not a transaction or an engine checkpoint.

Snapshots do not include result files, proof/checkpoint data or server state.
Do not blindly restore work files after unreservation: copying an old file back
cannot restore a released reservation and can cause invalid/duplicate work.
For any manual recovery, stop AutoPrimeNet and the computation engine, inspect
the private manifest and current reservations, and restore only files appropriate
to the current state. No automatic restore or server rollback is implemented.
Recovery/unreservation have been tested with simulated command bodies only;
never change real reservations merely to test these controls.

### Scheduled monitoring

Dashboard → **Start monitoring…** (or the tray Start item) asks before starting
a GUI-owned runner. Save or reload unsaved edits first. The runner checks the
configuration fingerprint, audited source and native instance lock, validates
offline and creates its private backup before asking the GUI for permission to
begin. Stop during preflight prevents any server cycle from starting.

Positive polling intervals run the original native scheduler continuously in a
private child. Configure **Polling interval** and **Watch results/proof files
immediately** in Settings → Edit monitoring and output preferences. Polling must
be at least 1800 seconds and no longer than the progress check-in interval in
PrimeNet. Blank watch policy uses the original enabled default. With watching off,
results/proofs are checked on each poll. With watching on, the original native
watchers enqueue result reporting and proof uploads between polls. Original
ordering delays (one second for result reads, 60 seconds before proof uploads)
and retry cooldowns remain in effect during normal operation. A stopped run does
not retry pending queued work; source files remain available for the next run.

**Polling interval = 0** performs one complete pass and stops. For a newly
registered computer this includes the normal work-cycle follow-up unless Stop
was requested after registration. One-shot buttons still perform exactly their
selected action, without starting a continuous scheduler.

Each poll can register/update the computer, request/register work, report
results/progress, download certification data, upload proofs, check versions and
send configured notifications. The original scheduler decides which polls are
progress check-ins and when certification/rolling-average work is due. All server
logic and proof archival/deletion behavior remain original. No computation engine
is launched or terminated. Stop before changing and saving monitoring preferences.

The separate GUI runtime adds reviewed, in-memory lifecycle hooks to the audited
source: scheduler-boundary stops, wakeable idle waits and reporting/upload worker
draining. The original file is not edited. Native watchers only enqueue file names;
they remain daemon threads whose OS handles close when this owned child exits.
Watcher or worker failure stops monitoring and drains active writers; inspect the
private backend log and retry with watching disabled if the filesystem cannot
support it. Native FSEvents delivery has been tested on macOS with simulated
server calls; other platform/runtime acceptance remains pending.

Each Start creates an owner-private configuration snapshot named
`<config-name>.gui-monitor-backup-<unique-id>.bak` before beginning a cycle. The
unchanged CLI writes configuration/state normally and may normalize INI comments
and formatting; GUI save preservation cannot prevent that backend behavior.
This snapshot protects the original configuration, not server reservations or
computation checkpoints. Restoring it cannot undo server operations.

Dashboard and tray state distinguish Starting, Running cycle, Watching files,
Waiting, Stopping, Stopped and Failed. A cycle timestamp marks completion of the
local scheduling pass; queued background uploads may still be active. The next
poll time is a plan. A completed cycle or zero exit is not proof that every
server operation succeeded: some existing CLI paths log errors without returning
a failing exit code. Connectivity and per-operation acceptance stay unverified;
review AutoPrimeNet's configured log for detailed results. Raw CLI output and
credentials are not copied into GUI activity, whose display is capped at 2000
lines. Refresh local snapshots to inspect current files.

**Stop after active work** prevents another poll, wakes idle scheduler/worker
waits, and ignores new watcher queue entries. It lets the active scheduling pass
and active reporting/upload batches finish their writes before exiting. The
original short ordering delays are preserved even after Stop. This can
take time during retries, a large proof upload, or waits on an existing `.lck`.
**Force stop…** requires a separate confirmation and terminates only the owned
CLI child; it can interrupt a write/upload and leave sidecar locks. Those locks
are never removed automatically. Inspect the affected workspace before restarting
after a forced stop. Neither stop action unreserves work or changes QuitGIMPS.

Closing the window hides/minimizes it while monitoring continues. **Quit** asks
to stop monitoring, waits for active work and reporting/upload workers, then closes the GUI
and tray helper. A force-stop control remains reachable while Quit is waiting.
If the GUI process disappears unexpectedly, pipe EOF requests a graceful runner
shutdown; it may still wait for the active cycle. This is not a guarantee of
immediate shutdown when files or network operations are blocked.

If sending the initial runner request fails, the GUI reports a launch error and
reaps that owned child in the background, escalating to termination/kill as
needed. No cycle has been authorized by the begin handshake at that point.
Conflicting actions remain disabled while that child is still running; cleanup
does not target an independent CLI or computation engine. Inspect any preflight
artifacts normally before retrying.

The GUI holds `.gui-runner.guard` across monitoring/actions/saves and also
attempts `~gui-monitor.lock`. The continuous CLI child holds its own normal
`~lock` for its lifetime; one-shot/one-pass children acquire it for each process.
Native lock files can remain after exit; their existence alone does not mean an
OS lock is held. Do not delete them to bypass a live process. After stopping,
the GUI reloads backend state automatically before further editing/restarting.

### Debug verbosity and private traces

Use **Settings → Edit monitoring and output preferences → Debug verbosity**:

| Level | Original backend behavior |
| --- | --- |
| 0 | Normal logging (default) |
| 1 | Detailed debug logging in the original backend log |
| 2 | Detailed logging plus original HTTP/SMTP wire tracing |
| 3 | All logging plus wire tracing; higher repeated `--debug` counts have the same upstream logging threshold |

The GUI stores this preference as `[GUI] DebugLevel` and supplies repeated
`--debug` flags to its owned CLI processes and graphical registration/native
runtime adapters. The standalone CLI ignores this GUI preference and still needs
its own `--debug` flags. Offline previews, validation, mail discovery and diagnostic
exports do not enable raw trace capture or create trace files.

At levels 2–3, the existing Start/action confirmation explains that raw traces
can contain SMTP/proxy passwords, authentication tokens, email addresses and
message bodies. Each CLI child gets a new owner-private
`.gui-backend-trace-<unique-id>.log` in the selected workspace (POSIX mode 0600;
on Windows, permissions depend on the workspace's inherited ACL). Capture is
limited to 8 MiB including a limit marker; later output is drained and discarded
so it cannot block the backend. A new-computer one-pass run may start two CLI
processes and produce two files. The original native log retains its independent
upstream rotation policy.

**Logs & Status → View latest private trace** reads only the latest regular trace
file, at most the last 128 KiB / 2000 lines. It is available while monitoring runs,
and Refresh reads newly flushed output. Trace contents are never copied to GUI
activity or included automatically in exported diagnostics. The existing private
backend-log viewer remains separate. Older trace files can be reviewed with a
local text editor. Trace files are retained until you remove them with your file
manager; review/redact before sharing, and turn verbosity back to 0 when done.

A trace file must be created before the chosen CLI process starts. Capture I/O
errors after launch do not interrupt an active backend write/upload; the pipe
continues draining and a generic incomplete-capture warning appears after the
process ends. Raw errors and trace contents are not emitted on the GUI event
channel. Trace files created in the repository root are ignored by Git.

### Native instance-lock policy

**Settings → Edit connection settings → Require successful native instance
locking** maps to the original `[PrimeNet] require_lock` / `--lock` / `--no-lock`
policy. Blank or True is strict (default). False still attempts native locks and
refuses known live-owner errors (`EAGAIN`/`EACCES`); like the original CLI, it can
continue after other native-lock acquisition errors. Opening a lock file and
creating the GUI ownership guard must still succeed. Symbolic-link native lock
paths remain refused. Per-work-file `.lck` synchronization is unchanged.

The atomic GUI guard is mandatory in both policies. It coordinates GUI runners
and configuration saves independently of native lock support. Optional native
locking does not protect against an independent CLI that cannot be detected by
the filesystem's locking mechanism. Verify no independent AutoPrimeNet uses the
workspace before Save/Start/actions. Existing confirmations describe this when
False is selected. The GUI logs when preflight native locking was unverified;
the backend log records any later original CLI lock warnings. This mode is for
filesystems with native-lock problems, not for running concurrent handlers.

The guard is an exclusively created owner-private file containing host, PID and
a random owner token. It is removed on normal context exit only if its original
file identity and owner token still match. It is not automatically removed when
already present, including after an abnormal process exit. If startup reports a
stale `.gui-runner.guard`, inspect it in a text editor and verify that no GUI,
supervisor, CLI child or independent AutoPrimeNet uses the workspace, then remove
only that stale guard with your file manager. A dead recorded PID alone is not
proof that its child has finished draining active work. Never remove a guard
belonging to an active run. Locking behavior on real network/unsupported
filesystems remains part of deferred manual acceptance testing.

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
Original-file preservation remains a development policy, independently of ignores.

## Development and validation

* Test GUI startup, forms, background operations, configuration handling, and
  backend integration on Python 3.15.0, then on selected later releases.
* Reject older interpreters with a clear version message before importing
  supporting GUI modules. The small launcher version check must itself use
  syntax understood by the older interpreters it is intended to diagnose.
* Scope GUI linting and test configuration to the GUI's minimum version.
  The existing repository-wide Ruff and Pylint settings target older versions;
  changing them globally could affect the independent CLI and requires review.
* Preserve the CLI's independence by avoiding imports of GUI code from existing
  CLI entry points.
* Target macOS, Windows, Linux, and FreeBSD where practically testable. Record
  actual runtime/platform results; intended support is not evidence of testing.

The development environment now has Python 3.15.1, working Tcl/Tk 9.1.0 bindings,
and Requests inside `.venv`. A real Tk window smoke check has passed on macOS.
The user confirmed an earlier prototype's manual macOS hide/reopen/Quit test;
that historical check does not validate the current implementation. Consolidated
manual acceptance remains pending and is tracked in
[GUI_ACCEPTANCE.md](GUI_ACCEPTANCE.md).
Release acceptance, Python 3.15.0-floor, and cross-platform validation remain pending;
see [GUI_DEVELOPMENT.md](GUI_DEVELOPMENT.md) for the scope of actual checks.




### Planned manual acceptance testing

Manual acceptance testing remains pending; the implemented feature inventory is
ready for acceptance testing within the documented limits. Automated
checks recorded in GUI_DEVELOPMENT.md are separate evidence and do not imply the
user has tested these workflows. Use disposable workspaces on the available test
machines first. Record OS, Python/Tk versions, computation engine, tray support,
and results for workspace loading, preservation/validation, GPU/mail discovery,
registration previews, lifecycle/quit, and private logs/reports. Live provider or
PrimeNet actions should be exercised deliberately with the intended account and
workspace, with local backups and review of server state. Cross-platform runtime
and live-service acceptance remain pending in GUI_PARITY.md.
