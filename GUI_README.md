# AutoPrimeNet GUI

Use the GUI to manage PrimeNet assignments, start an installed computation program,
and see how far its workers have progressed. **Start computation** opens your
engine in a terminal. **Start monitoring** tells AutoPrimeNet to communicate with
the server. You can run either one on its own.

[Install and launch](#install-and-launch) · [Set up a workspace](#set-up-a-workspace) ·
[Start a worker](#start-a-worker) · [Check progress](#check-progress) ·
[Monitor assignments](#monitor-assignments) · [Run the tests](#running-the-test-suite)

## Install and launch

Run the commands below from the repository root. You'll need a desktop session
and Python **3.15.0 or later** with working Tk bindings. The virtual environment
installs Requests and psutil; it doesn't install Tk or a computation engine.
If you only want the command-line application, follow the [CLI README](README.md).

**macOS, Linux and FreeBSD.** On a Mac using Homebrew, install the matching
interpreter and bindings with `brew install python@3.15 python-tk@3.15`. On Linux
or FreeBSD, install Python, venv support and Tk for that same interpreter using
your distribution's packages or your chosen Python build. Then run:

```sh
python3.15 -m venv .venv
.venv/bin/python -m pip install -r requirements-gui.txt
.venv/bin/python -m pip check
.venv/bin/python -m tkinter
```

Close the small Tk demonstration window, then start the GUI:

```sh
.venv/bin/python -B autoprimenet_gui.py
```

**Windows (PowerShell).** Install Python 3.15 or later with Tcl/Tk selected.
Use the matching version with the Python launcher:

```powershell
py -3.15 -m venv .venv
.\.venv\Scripts\python.exe -m pip install -r requirements-gui.txt
.\.venv\Scripts\python.exe -m pip check
.\.venv\Scripts\python.exe -m tkinter
```

Close the demonstration window, then run:

```powershell
.\.venv\Scripts\python.exe -B autoprimenet_gui.py
```

If the Tk check fails, fix the interpreter or display before going further.
You don't have to activate the environment when you use its Python directly.

## Set up a workspace

A workspace is the directory containing the configuration and work files you
want AutoPrimeNet to manage. It is usually separate from this source checkout.

1. Choose **Browse** and pick the workspace. If your configuration has a name
   other than `prime.ini`, enter it in **Settings** and click **Refresh preview**.
   Previewing reads local files. It doesn't reserve work or start an engine.
2. In **PrimeNet**, enter your GIMPS username or the literal `ANONYMOUS`.
   In **Workers**, select your engine. For multiple workers, set the count,
   click **Apply worker count**, then **Edit selected worker…** for each one.
   Non-PRPLL workers need separate directories when there is more than one.
   PRPLL uses indexed files in one directory; leave its worker directories blank.
3. In **Settings**, match the work and results filenames to the engine. For
   example, the Ubuntu packaged Mlucas 20.1.1 used `worktodo.ini`, while the
   source-built 21.0.2 used `worktodo.txt`. Selecting Mlucas doesn't change the filename.
4. In a dialog, choose **Apply to form** to keep your edits or **Cancel** to
   discard them. Valid edits save about two seconds after you stop typing and
   close the editors. Use **Save settings** to save immediately. Check the status
   at the bottom of the window before starting a server operation.

The next time you open the GUI, it previews the last workspace. It doesn't
restart monitoring or computation. To forget that selection, remove
`AutoPrimeNetGUI/preferences.json` under `~/Library/Application Support` on
macOS, `%APPDATA%` on Windows, or `$XDG_CONFIG_HOME` (normally `~/.config`)
on Linux/FreeBSD. This leaves the workspace itself alone.

### Files and backups

Keep configuration, logs, work, results and proof archives at separate paths.
The launcher uses `autoprimenet-gui-launchers.json`,
`.autoprimenet-gui-launchers.lock`, and `.autoprimenet-gui-launches/`; leave
those names for the GUI. Keep real workspaces outside the checkout so you don't
accidentally commit assignments, credentials or traces.

Saving validates the proposed configuration, backs up an existing file before
replacing it, and preserves unrelated settings and comments. A running backend
can later rewrite the INI in its own format. If another program changes it while
you are editing, keep a copy of any draft values you need, refresh, and reapply
them. The GUI won't merge the two versions. To run monitoring, the INI must be
UTF-8 **without a BOM**. A workspace preview supports up to 128 workers, 1,000
work lines, 2 MiB per file and 1 MiB per backend request.

## Start a worker

If you already run your engine from its own terminal, leave it running and go
straight to [Progress](#check-progress). To start it from the GUI instead:

1. Open **Launchers → Add profile…**. Name the profile, choose the program and
   browse to its executable. On Windows select its `.exe` or `.com` file.
2. Set the engine's working directory to the directory where it normally runs.
   A blank directory uses the workspace. Relative paths start there; a bare
   executable name uses the GUI's PATH.
3. Enter **one exact argument per line**, without shell quotes. Put a path
   containing spaces on a single line. Leave arguments empty if you normally
   start the engine without any. Profiles store arguments as plain text.
4. Choose a terminal and **Save profile**. Select the profile on the Dashboard
   or Launchers tab, click **Start computation…**, and check the executable,
   directory, terminal and arguments before confirming.

For example, if your usual command is `./Mlucas`, browse to that binary, set the
directory where you normally type the command, and leave arguments blank. Configure
worker counts, threads and GPU selection in the engine as you normally would.

| Platform | Terminal choices |
| --- | --- |
| macOS | Terminal. Allow Terminal automation if macOS asks. |
| Windows | PowerShell or Cmd. Auto tries PowerShell 7, Windows PowerShell, then Cmd. |
| Linux/FreeBSD | Auto tries Ptyxis, GNOME Terminal, Konsole, Xfce Terminal, then xterm. You can also select one explicitly. |

Use **Edit selected…**, **Delete selected…**, or **Reload launchers** to maintain
profiles. One workspace can hold up to 128 profiles; loading or selecting one
never starts it. If the launch target changes after review, start the review
again. If startup hasn't been confirmed after 30 seconds, look in the terminal
and refresh Progress **before retrying**. Duplicate detection depends on being
able to inspect the process and its working directory.

**Stop the engine in its terminal**, using that program's normal shutdown
procedure. Quitting the GUI or stopping monitoring leaves computation running.
Closing the terminal itself can interrupt the calculation.

## Check progress

Open **Progress** and click **Refresh progress**, or leave the tab open for
automatic scans. The default interval is 90 seconds. With a workspace loaded,
enter **Refresh seconds** (1–86,400) and click **Save interval** to remember it.
This changes the display refresh, not the engine's checkpoint or PrimeNet schedule.

Select a row for the assignment and file paths. Scroll horizontally for speed,
stage, worker queue, last update and estimated finish. Mlucas, GpuOwl, PRPLL,
PrMers, CUDALucas, mfaktc, mfakto and PrimePath have saved-progress readers.
Prime95/MPrime, CUDAPm1, cofact, gvtf and Mp_p-1_gpu can appear as running
processes without progress statistics.

Progress comes from files the engine has written. **Unavailable** means no
usable measurement; **stale** means the saved data is over 15 minutes old,
which can be normal for a long checkpoint interval. Estimates assume continuous
computation. Later compatible assignments can use the same worker's measured
speed; a stage percentage needn't represent the entire assignment.

The reader checks accessible process directories and configured worker files.
Without a matching workspace it looks for `worktodo.txt` or `worktodo.ini`
(PRPLL: `worktodo-N.txt`). Renamed executables, restricted directories or
checkpoints written elsewhere can prevent discovery. A scan has a 30-second
timeout and limits of 128 matching processes, 128 worker files per group and
1,000 assignments. You don't need monitoring or a PrimeNet connection to use it.

## Monitor assignments

On the Dashboard, choose **Start monitoring…** when you're ready for AutoPrimeNet
to communicate with the server. A normal pass can register the computer, fetch
work, report results and progress, upload proofs and send configured notifications.

* **Polling:** In **Settings → Edit monitoring and output preferences…**, use
  `0` for one pass, or at least 1,800 seconds for continuous monitoring. The poll
  interval cannot exceed the progress check-in interval set in **PrimeNet**.
  Enable file watching to process new results and proofs between polls.
* **Check in now:** **Push Status to PrimeNet Now** requests an early check-in
  from the running scheduler. An active cycle finishes first. With monitoring
  stopped, the button offers a complete single pass, which can also fetch work
  or handle results. It reports the latest saved checkpoint.
* **Stop:** **Stop after active work** waits for active reporting and uploads.
  **Force stop…** can interrupt writes or leave locks behind; inspect the
  workspace before restarting. **File → Quit** also waits for owned work.
* **Verify an operation:** Read the backend log and check the relevant service
  record. A local process exiting successfully doesn't prove that the server
  accepted a result, reservation or proof.

### Register, recover or release assignments

Use **PrimeNet → Register or update computer** to send the saved settings.
**Ping PrimeNet** tests connectivity; the experimental **v6** ping tests that API
version only. Saving settings or running a local preview does neither.

In **Assignments**, you can report pending results, report results and upload
proofs, or pause/resume requests for new work. Pausing new requests leaves
existing reservations and calculations in place. Successful proof uploads may
archive or delete the local proof according to your settings.

To register exponents, register the computer first. Open **Register exponent
batch**, select one worker and a work type, enter its parameters, and choose
**Add row**. Select a queued row to replace or remove it. **Validate and preview
offline** shows the actual work lines. Review them, pause the affected engine,
and type `REGISTER N` to register the validated batch of N rows. This can also
register **other unregistered work already in that worker's file**. A batch
holds 1–100 entries; changing the worker or queue requires a fresh preview.
The form accepts TF, both P−1 variants, ECM, LL, LL double-check, PRP and PRP
double-check. Enter known factors explicitly, comma-separated. A preview
doesn't check whether the server will accept a reservation.

Pause affected engines before using recovery or unreservation. Review the worker
and exponent carefully: unreserving one exponent operates on the **first match**
across configured workers, even if you selected a different row.

| Action | What to confirm |
| --- | --- |
| Recover assignments | Type `RECOVER` to rebuild the active work and certification files. |
| Recover all assignments | Type `RECOVER ALL`. This can include expired assignments or TF1G work from other systems. |
| Unreserve one exponent | Type the displayed phrase, for example `UNRESERVE 127`. |
| Unreserve all | Type `UNRESERVE ALL` to release reservations for the active workers. |

Before these operations and exponent registration, the GUI creates a private
`.gui-assignment-backup-*` directory. Its manifest records which work and
certification files existed and their hashes. Snapshots refuse symlinks and
changing inputs (2 MiB per file, 16 MiB total). They don't include results,
proofs or server state. If an operation partially succeeds, check the log and
current reservations before restoring any files.

## Configure hardware, connections and notifications

**Hardware.** In **PrimeNet → Edit hardware and resource settings…**, enter what
AutoPrimeNet should report: frequency in MHz, cache in KiB, memory in MiB and
proof disk limit in GiB per worker. Stage 2 memory cannot exceed total memory.
Blank entries use inheritance or detection. **Detect GPUs…** lets you review a
local device, choose **Use in hardware dialog**, and apply its values. This
doesn't select the GPU used by the engine.

**Assignment preferences.** Set work preferences per worker and the queue length
in Assignments. In **Advanced → Edit advanced assignment settings…**, set
exponent/factoring limits, conversions, P−1/ECM options or PRPLL certification
policy. Leave fields blank to use inherited settings or backend defaults. For
a particular CLI flag, search **Advanced** and double-click the matching row to
find its control. **Help → Original CLI help** works without a workspace. The
[option reference](GUI_PARITY.md) lists the individual flags and GUI limits.

**Proxy and passwords.** In **Settings → Edit connection settings…**, enter the
proxy type, host and username. For SOCKS, install `requests[socks]` using the
venv's Python. Use **Manage SMTP and proxy passwords…** for passwords. **Keep**
retains the current value or pending edit; **Replace** stages a new password;
**Remove** clears it on save; **Use saved** discards a pending edit. Replacements
require working OpenSSL libcrypto and encryption enabled or inherited. Changing
a username or host doesn't clear its old password. Existing encrypted values
use the backend's hardware binding; don't assume they will work on another machine.

**Email.** Under **Notifications**, enter the sender and SMTP server, optionally
as `hostname:port`. Separate recipients with commas; blank uses the sender.
Choose SSL/TLS or STARTTLS as required by the provider. To keep the configuration
without sending notifications, set **Send configured notifications** to False.

**Discover SMTP provider…** can fill in the sender, host, port, security and
username. Review the proposed server with your provider before applying it:
discovery may send the sender address over HTTP or rely on unsigned DNS. It
uses saved proxy settings. The lookup requests uncompressed replies, allows
1 MiB across all responses and redirects, and times out after 90 seconds.
Enter the settings manually if lookup fails. Discovery doesn't send email;
**Send test email…** is a separate action. Check the recipient's inbox for delivery.

## Logs, locking and the tray

**Logs & Status** shows GUI activity. Choose **Write work status to backend
log…** for the backend's local work report, then **View private backend log…**.
The viewer reads the latest 128 KiB or 2,000 lines. **Export private diagnostics…**
creates a local report with software, hardware and account identifiers. Read and
redact it before sharing.

In **Settings → Edit monitoring and output preferences…**, choose debug level
0 for normal logging or 1 for detail. Levels 2–3 also capture raw HTTP/SMTP
traffic; these files can contain passwords, tokens and message bodies. **View
latest private trace** opens the newest file. Traces are capped at 8 MiB per
process and remain in the workspace until you remove them. Turn tracing off
when you're done. This dialog also controls version checks and CLI console color.

### Native instance-lock policy

Leave **Require successful native instance locking** enabled unless your
filesystem cannot support it. Disabling the requirement still checks for known
owners, but may miss an independent CLI. Never run two assignment handlers on
the same workspace. If `.gui-runner.guard` remains after a crash, first verify
that the GUI, supervisor, CLI and any draining workers have exited. Remove only
the confirmed stale guard. The presence of a native lock file alone doesn't
mean the operating system still holds the lock.

### Optional tray integration

Closing the main window keeps monitoring running. With a working tray or menu
bar item, use **Open AutoPrimeNet GUI** to reopen it. Without one, closing
minimizes to the Dock or taskbar. Use **File → Quit** to exit or start with
`--no-tray` to skip the tray helper.

* **macOS** — run `.venv/bin/python -m pip install -r requirements-gui-tray.txt`.
* **Windows** — run `.\.venv\Scripts\python.exe -m pip install -r requirements-gui-tray.txt` in PowerShell.
* **Linux/FreeBSD:** Install GTK **3**, GLib/GIO introspection, Cairo and the
  matching build dependencies, then install `requirements-gui-tray-gtk.txt` in
  the venv. AppIndicator needs its introspection data and a working desktop tray
  host. The [PyGObject installation guide](https://pygobject.gnome.org/getting_started.html)
  explains the native dependencies. Verify the bindings with
  `.venv/bin/python -c "import gi; gi.require_version('Gtk', '3.0'); from gi.repository import Gtk; print(Gtk.get_major_version())"`.

After enabling the desktop extension or installing missing packages, choose
**Settings → Retry tray integration**. Fedora and Ubuntu GNOME/Wayland tray checks
are recorded in [GUI_TESTING.md](GUI_TESTING.md); other desktops can behave differently.

## Troubleshooting

| Symptom | What to try |
| --- | --- |
| The GUI won't open | Run the Tk demonstration with the venv interpreter from a graphical desktop. |
| Settings won't save | Check the username, worker directories, file permissions and filename conflicts. Read the error before refreshing an unsaved form. |
| Work downloaded but nothing is calculating | Start the computation engine. Monitoring only manages assignments. |
| A launch times out | Inspect its terminal and refresh Progress before trying again. Check the executable path and terminal permissions. |
| Progress is missing | Check the work filename, process permissions and checkpoint interval. Some programs only support process detection. |
| Monitoring won't start | Save or reload the workspace, check UTF-8 encoding, then inspect the log and [lock policy](#native-instance-lock-policy). |

## Running the test suite

Use the same Python environment as the GUI, with `requirements-gui.txt` installed.
Run these commands from the repository root. Tests use temporary workspaces and
simulated service responses; they do not need a real PrimeNet account or send
real results, proofs or email.

On macOS, Linux or FreeBSD:

```sh
.venv/bin/python -B -m unittest discover -s tests -p 'test_gui_*.py' -v
.venv/bin/python -m pip check
```

On Windows PowerShell:

```powershell
.\.venv\Scripts\python.exe -B -m unittest discover -s tests -p 'test_gui_*.py' -v
.\.venv\Scripts\python.exe -m pip check
```

The default run skips desktop-dependent tests. From a logged-in graphical desktop,
enable window, native watcher and applicable tray tests:

```sh
AUTOPRIMENET_GUI_DESKTOP_TESTS=1 .venv/bin/python -B -m unittest discover -s tests -p 'test_gui_*.py' -v
```

Windows PowerShell:

```powershell
$env:AUTOPRIMENET_GUI_DESKTOP_TESTS = '1'
.\.venv\Scripts\python.exe -B -m unittest discover -s tests -p 'test_gui_*.py' -v
Remove-Item Env:AUTOPRIMENET_GUI_DESKTOP_TESTS
```

Install `requirements-gui-tray.txt` to include native macOS/Windows tray tests.
Missing optional packages and platform-specific checks can still produce skips;
record their reasons. Linux/FreeBSD tray-host unit tests simulate the desktop
services, so test actual panel integration manually too.

To run a smaller group, replace the discovery pattern with a filename such as
`test_gui_progress.py` or `test_gui_launcher*.py`. No pytest installation is needed.

[GUI_TESTING.md](GUI_TESTING.md) describes architecture, coverage and recorded
results. [GUI_ACCEPTANCE.md](GUI_ACCEPTANCE.md) provides the manual checklist;
[GUI_PARITY.md](GUI_PARITY.md) maps CLI options to graphical controls and limits.
