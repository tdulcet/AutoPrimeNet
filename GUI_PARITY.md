# GUI / CLI parity inventory

This inventory covers the 96 argparse entries (including inverse flags, aliases and automatic help) in the audited AutoPrimeNet 2.0.2 source. Counts are parser entries, not distinct features, and do not establish complete parity.

Source SHA-256: `05776d74b7b816c52774c30de438e7dcf047127a810daa8ee36335f8b8e7ec12`.

Generated from the same option inventory and coverage metadata used by the GUI reference. The original source is unchanged. See [GUI.md](GUI.md) for behavior/limits and [GUI_DEVELOPMENT.md](GUI_DEVELOPMENT.md) for test evidence.

## Coverage meaning

- **Available**: a graphical control or operation exists within the documented GUI limits. This does not mean its live server behavior or every platform has been validated.
- **Partial**: related graphical functionality exists, but an original workflow distinction remains.
- **CLI only**: use the independent original CLI; no raw-argument GUI substitute is provided.
- **Hidden / CLI only**: hidden experimental upstream behavior is not exposed.
- **Removed upstream**: the original backend rejects this legacy feature.

Current parser-entry coverage: 92 Available, 0 Partial, 2 CLI only, 1 Hidden / CLI only, 1 Removed upstream.

## Remaining workflow gaps

- `--lock` / `--no-lock`: GUI startup always requires its runner lease and the native instance lock. It cannot bypass locking on unsupported filesystems.
- Hidden `--prime95` is not a supported graphical engine. Hidden legacy `--password` is rejected by the original backend, so SMTP/proxy password management does not implement account-password authentication.
- Live registration, assignment changes, email, proof/result operations and v6 ping remain unvalidated. Tests use offline probes or simulated API responses. Python 3.15.0 itself and Windows/Linux/FreeBSD runtime coverage remain pending.

## Interactive workflows and state

| Workflow | Graphical path and limits |
| --- | --- |
| Initial account/program/worker setup | PrimeNet, Workers and Settings forms with optional GPU/SMTP discovery; validate/save offline, then Register or update computer with confirmation |
| Hardware/resources | PrimeNet hardware dialog with explicit values and detected/default inheritance; local GPU discovery and a reviewed GPU picker |
| Notifications | SMTP/recipient/TLS forms, send policy, masked encrypted password replacement, confirmed test email and reviewed provider discovery; no per-event editor |
| Exponent registration | Batch form for the eight original work types, explicit parameters/factors, source-based offline preview, typed confirmation, work snapshots and original registration function; no implicit exponent metadata lookup |
| Recovery and unreservation | Dedicated confirmations, structured exponent input and work/certification snapshots; no automatic reservation rollback or restore |
| Status/logs/diagnostics | Original status report to native log, bounded private log/trace viewer, offline owner-private diagnostic file; no proof of remote acceptance from local exit status |
| Lifecycle | Owned native scheduler with separate polling/check-ins, native file watching, one-pass mode, worker-draining Stop, explicit force, tray/taskbar fallback and asynchronous Quit; no computation-engine process management |

Batch registration supports one configured worker and up to 100 entries per operation, a 48 KiB normalized plan, and bounded integer/factor sizes. It also registers other unregistered work already in the selected worker file, matching upstream behavior. All graphical file/worker/preview/snapshot limits are documented in GUI.md.

## Parser-entry mapping

| CLI flags | Destination | Coverage | Graphical location / limitation |
| --- | --- | --- | --- |
| `--version` | `version` | Available | Advanced → Help → About |
| `-d`, `--debug` | `debug` | Available | Settings → Behavior → Debug verbosity (0–3; 2+: raw trace) |
| `-w`, `--workdir` | `workdir` | Available | Settings → Working directory selector |
| `-D`, `--dir` | `dirs` | Available | Workers → Edit selected worker → Directory |
| `-i`, `--work-file` | `work_file` | Available | Settings → Work filename |
| `-r`, `--results-file` | `results_file` | Available | Settings → Results filename (blank: program default) |
| `-L`, `--logfile` | `logfile` | Available | Settings → Activity log path |
| `-l`, `--config-file` | `localfile` | Available | Settings → Configuration filename |
| `--archive-proofs` | `archive_dir` | Available | Settings → Proof archive directory (optional) |
| `-u`, `--username` | `user_id` | Available | PrimeNet → GIMPS username (or ANONYMOUS) |
| `-p`, `--password` | `password` | Removed upstream | Legacy account-password feature was removed upstream |
| `-T`, `--workpref` | `work_preference` | Available | Workers → Edit selected worker → Preference |
| `--cert-work` | `cert_work` | Available | Advanced → Receive certification work (PRPLL only) |
| `--no-cert-work` | `cert_work` | Available | Advanced → Receive certification work (PRPLL only) |
| `--cert-work-limit` | `cert_cpu_limit` | Available | Advanced → Certification time limit (%) |
| `--min-exp` | `min_exp` | Available | Advanced → Minimum assignment exponent |
| `--max-exp` | `max_exp` | Available | Advanced → Maximum assignment exponent |
| `--min-bit` | `min_bit` | Available | Advanced → Minimum trial-factoring bit level |
| `--max-bit` | `max_bit` | Available | Advanced → Maximum trial-factoring bit level |
| `--force-target-bits` | `force_target_bits` | Available | Advanced → Factor to target bit level (depth first) |
| `-m`, `--mlucas` | `mlucas` | Available | Workers → Computation program |
| `-g`, `--gpuowl` | `gpuowl` | Available | Workers → Computation program |
| `--prpll` | `prpll` | Available | Workers → Computation program |
| `--prmers` | `prmers` | Available | Workers → Computation program |
| `--cudalucas` | `cudalucas` | Available | Workers → Computation program |
| `--mfaktc` | `mfaktc` | Available | Workers → Computation program |
| `--mfakto` | `mfakto` | Available | Workers → Computation program |
| `--primepath` | `primepath` | Available | Workers → Computation program |
| `--prime95` | `prime95` | Hidden / CLI only | Hidden experimental Prime95 mode is not exposed |
| `--num-workers` | `num_workers` | Available | Workers → Apply worker count |
| `-n`, `--num-cache` | `num_cache` | Available | Assignments → Legacy extra assignment cache |
| `-W`, `--days-work` | `days_of_work` | Available | Assignments → Days of work to queue |
| `--force-pminus1` | `tests_saved` | Available | Advanced → P−1 tests saved / force P−1 |
| `--pminus1-threshold` | `pm1_multiplier` | Available | Advanced → P−1 retry threshold multiplier |
| `--force-pminus1-bounds` | `pm1_bounds` | Available | Advanced → Optimal P−1 bounds |
| `--ecm-bounds-multiplier` | `ecm_multiplier` | Available | Advanced → ECM bounds multiplier |
| `--max-ecm-curves` | `max_ecm_curves` | Available | Advanced → Maximum ECM curves |
| `--convert-ll-to-prp` | `convert_ll_to_prp` | Available | Advanced → Convert LL assignments to PRP |
| `--convert-prp-to-ll` | `convert_prp_to_ll` | Available | Advanced → Convert PRP assignments to LL |
| `--no-report-100m` | `no_report_100m` | Available | Advanced → Withhold prime results at ≥100 million digits |
| `--report-100m` | `no_report_100m` | Available | Advanced → Withhold prime results at ≥100 million digits |
| `--checkin` | `hours_between_checkins` | Available | PrimeNet → Progress check-in interval (hours) |
| `-t`, `--timeout` | `timeout` | Available | Settings → Behavior → Polling interval (seconds; 0: once) |
| `-s`, `--status` | `status` | Available | Logs & Status → Write work status to backend log |
| `--report-results` | `results` | Available | Assignments → Report results |
| `--upload-proofs` | `proofs` | Available | Assignments → Report results and upload proofs |
| `--recover` | `recover` | Available | Assignments → Recover assignments |
| `--recover-all` | `recover_all` | Available | Assignments → Recover all assignments |
| `--register-exponents` | `register_exponents` | Available | Assignments → Register exponent batch |
| `--unreserve` | `exponent` | Available | Assignments → Unreserve an exponent |
| `--unreserve-all` | `unreserve_all` | Available | Assignments → Unreserve all assignments |
| `--no-more-work` | `no_more_work` | Available | Assignments → Pause new-work requests |
| `--resume-work` | `resume_work` | Available | Assignments → Resume new-work requests |
| `--ping` | `ping` | Available | PrimeNet → Ping PrimeNet |
| `--v6` | `v6` | Available | PrimeNet → Ping experimental v6 API |
| `--debug-info` | `debug_info` | Available | Logs & Status → Export private diagnostics |
| `--no-version-check` | `version_check` | Available | Settings → Behavior → Check for AutoPrimeNet/engine updates |
| `--version-check` | `version_check` | Available | Settings → Behavior → Check for AutoPrimeNet/engine updates |
| `--version-check-channel` | `version_check_channel` | Available | Settings → Behavior → Preferred update channel (blank: stable) |
| `--no-lock` | `lock` | CLI only | GUI requires locks; disabling locking is unsupported |
| `--lock` | `lock` | CLI only | GUI requires locks; disabling locking is unsupported |
| `--no-watch` | `watch` | Available | Settings → Behavior → Watch results/proof files immediately |
| `--watch` | `watch` | Available | Settings → Behavior → Watch results/proof files immediately |
| `--no-encrypt` | `encrypt` | Available | Settings → Connection → Backend password encryption policy |
| `--encrypt` | `encrypt` | Available | Settings → Connection → Backend password encryption policy |
| `--no-color` | `color` | Available | Settings → Behavior → Native CLI console color |
| `--color` | `color` | Available | Settings → Behavior → Native CLI console color |
| `--setup` | `setup` | Available | PrimeNet → Register or update computer |
| `--proxy-type` | `proxy_type` | Available | Settings → Connection → Proxy type (blank: http) |
| `-x`, `--proxy-server` | `proxy` | Available | Settings → Connection → Proxy server (optional hostname:port) |
| `--proxy-username` | `proxy_username` | Available | Settings → Connection → Proxy username (optional) |
| `--proxy-password` | `proxy_password` | Available | Settings → Manage passwords (encrypted replacement) |
| `-H`, `--computer-name` | `computer_id` | Available | PrimeNet → Computer name (optional) |
| `--processor-model` | `cpu_brand` | Available | PrimeNet → Hardware → Processor model (CPU or GPU) |
| `--processor-features` | `cpu_features` | Available | PrimeNet → Hardware → Processor features |
| `--processor-frequency` | `cpu_speed` | Available | PrimeNet → Hardware → Processor frequency (MHz) |
| `--memory` | `memory` | Available | PrimeNet → Hardware → Total physical memory (MiB) |
| `--max-memory` | `day_night_memory` | Available | PrimeNet → Hardware → Maximum stage 2 memory (MiB) |
| `--max-disk-space` | `worker_disk_space` | Available | PrimeNet → Hardware → Proof residue disk limit (GiB per worker; 0: omit) |
| `--processor-l1-size` | `cpu_l1_cache_size` | Available | PrimeNet → Hardware → L1 data cache (KiB) |
| `--processor-l2-size` | `cpu_l2_cache_size` | Available | PrimeNet → Hardware → L2 cache (KiB) |
| `--processor-l3-size` | `cpu_l3_cache_size` | Available | PrimeNet → Hardware → L3 cache (KiB) |
| `--processor-cores` | `num_cores` | Available | PrimeNet → Hardware → Physical processor cores |
| `--processor-hyperthreads` | `cpu_hyperthreads` | Available | PrimeNet → Hardware → Threads per core (0: unknown) |
| `--hours` | `cpu_hours` | Available | PrimeNet → Expected computation hours per day |
| `--to-email` | `toemails` | Available | Notifications → Recipients (comma-separated; blank: sender) |
| `-f`, `--from-email` | `fromemail` | Available | Notifications → From email address |
| `-S`, `--smtp-server` | `smtp` | Available | Notifications → SMTP server (optional hostname:port) |
| `--tls` | `tls` | Available | Notifications → Connect using SSL/TLS |
| `--no-tls` | `tls` | Available | Notifications → Connect using SSL/TLS |
| `--starttls` | `starttls` | Available | Notifications → Upgrade connection using StartTLS |
| `--no-starttls` | `starttls` | Available | Notifications → Upgrade connection using StartTLS |
| `-U`, `--email-username` | `email_username` | Available | Notifications → SMTP username (optional) |
| `-P`, `--email-password` | `email_password` | Available | Notifications → Manage passwords (encrypted replacement) |
| `--test-email` | `test_email` | Available | Notifications → Send test email |
| `-h`, `--help` | `help` | Available | Advanced → Original CLI help / searchable reference |
