[![Actions Status](https://github.com/tdulcet/AutoPrimeNet/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/tdulcet/AutoPrimeNet/actions/workflows/ci.yml)

# AutoPrimeNet
The PrimeNet automated assignment handler program for GIMPS

Copyright © 2024 Teal Dulcet

Automatically gets and registers assignments, reports assignment progress and results, uploads proof files to and downloads certification starting values from PrimeNet for the Mlucas, GpuOwl, PRPLL, PrMers, CUDALucas, mfaktc and mfakto GIMPS programs. Additionally, it can get assignments and report results to mersenne.ca for exponents above the PrimeNet limit of 1G. Supports both Python 2 and 3 and Windows, macOS and Linux. Requires the [Requests library](https://requests.readthedocs.io/en/latest/), which is included with most Python 3 installations. The program will automatically prompt to install Requests on first run if it is not already installed.

Adapted from the PrimeNet Python script from [Mlucas](https://www.mersenneforum.org/mayer/README.html#download2) by [Loïc Le Loarer](https://github.com/llloic11/primenet) and Ernst W. Mayer, which itself was adapted from primetools by [Mark Rose](https://github.com/MarkRose/primetools) and [teknohog](https://github.com/teknohog/primetools).

AutoPrimeNet (the PrimeNet program) was moved from the [Distributed Computing Scripts](https://github.com/tdulcet/Distributed-Computing-Scripts#primenet) repository.

❤️ Please visit [tealdulcet.com](https://www.tealdulcet.com/) to support this program and my other software development.

## Features

* Interactive setup with a `--setup` option
* Command line interface and configuration file
* Automatically registers the instance with PrimeNet
* PrimeNet/mersenne.org
	* Supports all applicable [PrimeNet v5 API](https://v5.mersenne.org/v5design/v5webAPI_0.97.html) functionality
		* Registers and updates instance
		* Gets and sets program options
		* Gets and recovers assignments
		* Registers assignments
		* Unreserve assignments
		* Reports assignment progress
		* Reports assignment results
		* Ping server
	* Uploads PRP proof files
	* Downloads PRP certification starting values
* mersenne.ca for exponents above PrimeNet limit of 1G (1,000,000,000)
	* Supports all available functionality
		* Gets and recovers assignments
		* Unreserve assignments
		* Reports assignment results
* Supported GIMPS software
	* Full support
		* Mlucas
		* GpuOwl
		* PRPLL
		* PrMers
		* CUDALucas
		* mfaktc
		* mfakto
	* Partial support
		* CUDAPm1
	* Report results only
		* Prime95/MPrime
		* cofact
		* gvtf
* Supported worktypes
	* LL
	* PRP
	* PRP cofactor
	* Trial Factoring (TF)
	* P-1 factoring
	* ECM factoring
	* PRP Certification (CERT)
* Supports multiple workers (CPU Cores or GPUs)
	* Supports setting per worker options, including work preferences
* Can be used anonymously
* Supports submitting results and uploading proof files immediately, without polling the filesystem
* Automatically reports assignment progress
	* Monitor progress on [CPUs page](https://www.mersenne.org/cpus/)
	* Allows getting much smaller [Category 0 and 1 exponents](https://www.mersenne.org/thresholds/)
	* Supports using the save/checkpoint files to determine progress
* Can specify minimum and maximum exponent for assignments
	* Can specify minimum and maximum bit level for assignments
* Automatically registers assignments without an assignment ID (AID)
	* Interactively register specific exponents with a `--register-exponents` option
		* Automatically gets existing parameters from mersenne.ca
	* Supports a `worktodo.add` file
* Supports recovering all assignments
* Supports unreserving specific exponents or all assignments
* Supports automatically updating assignments
	* Force TF assignments to factor to the target bit level
	* Force P-1 factoring before LL/PRP tests
	* Use the optimal P-1 bounds
	* Convert LL assignments to PRP
	* Convert PRP assignments to LL
* Calculates rolling average to improve assignment expected completion dates
* Stop getting new assignments with a `--no-more-work` option
	* Resume getting assignments with a `--resume-work` option
* Logging to both console and a file
	* Optional color output
	* Automatically rotates log file
* Monitors available and used disk space
* Automatic AutoPrimeNet and GIMPS program version check
* Optional e-mail and text message notifications
	* There is an error
		* Failed to get new assignments
		* Assignment results were rejected
		* Failed to report assignment results
		* Failed to upload a proof file
	* GIMPS program has stalled
		* GIMPS program has stalled (not made any progress)
		* GIMPS program has resumed after previously stalling
	* Disk space is low
		* Disk space used is greater than % of configured limit
		* Disk space available is less than % of total
	* GIMPS program found a new Mersenne Prime!
	* There is a new version of the GIMPS program
		* New version of AutoPrimeNet is available
		* New version of the GIMPS program is available
* Automatically detects e-mail configuration when using `--setup` option
* File locking of both work and results files
* Optionally archives PRP proof files after upload
* Saves submitted results to a `results_sent.txt` file
* Automatically detects system information
	* Processor (CPU)
		* CPU model
		* Frequency/Speed
		* Total memory
		* Number of cores/threads
		* L1/L2/L3 cache sizes
	* Graphics Processor (GPU) with Nvidia Management Library (NVML) and OpenCL
		* GPU model
		* Frequency/Speed
		* Total memory
* Optional status report 
	* Expected completion dates for all assignments
	* Probability each assignment is prime
	* Outputs number of and first/last 20 decimal digits
* Verifies each found factor divides number
	* Outputs number of decimal digits and bits
* Optional alert after finding a new Mersenne Prime!
* Supports both Python 2 and 3 
* Supports Windows, macOS and Linux
* 100% Open Source
* Can claim full EFF Awards

## Usage

```
usage: autoprimenet.py [-h] [--version] [-d] [-w WORKDIR] [-D DIRS]
                       [-i WORKTODO_FILE] [-r RESULTS_FILE] [-L LOGFILE]
                       [-l LOCALFILE] [--archive-proofs ARCHIVE_DIR]
                       [-u USER_ID] [-T WORK_PREFERENCE] [--cert-work]
                       [--no-cert-work] [--cert-work-limit CERT_CPU_LIMIT]
                       [--min-exp MIN_EXP] [--max-exp MAX_EXP]
                       [--min-bit MIN_BIT] [--max-bit MAX_BIT]
                       [--force-target-bits]
                       [-m | -g | --prpll | --prmers | --cudalucas | --mfaktc | --mfakto]
                       [--num-workers NUM_WORKERS] [-n NUM_CACHE]
                       [-W DAYS_OF_WORK] [--force-pminus1 TESTS_SAVED]
                       [--pminus1-threshold PM1_MULTIPLIER]
                       [--force-pminus1-bounds {MIN,MID,MAX}]
                       [--ecm-bounds-multiplier ECM_MULTIPLIER]
                       [--convert-ll-to-prp] [--convert-prp-to-ll]
                       [--no-report-100m] [--report-100m]
                       [--checkin HOURS_BETWEEN_CHECKINS] [-t TIMEOUT] [-s]
                       [--report-results] [--upload-proofs] [--recover]
                       [--recover-all] [--register-exponents]
                       [--unreserve EXPONENT] [--unreserve-all]
                       [--no-more-work] [--resume-work] [--ping] [--v6]
                       [--debug-info] [--no-version-check] [--version-check]
                       [--version-check-channel {alpha,beta,stable}]
                       [--no-watch] [--watch] [--no-encrypt] [--encrypt]
                       [--no-color] [--color] [--setup]
                       [--proxy-type {http,https,socks5,socks5h}] [-x PROXY]
                       [--proxy-username PROXY_USERNAME]
                       [--proxy-password PROXY_PASSWORD] [-H COMPUTER_ID]
                       [--cpu-model CPU_BRAND] [--features CPU_FEATURES]
                       [--frequency CPU_SPEED] [--memory MEMORY]
                       [--max-memory DAY_NIGHT_MEMORY]
                       [--max-disk-space WORKER_DISK_SPACE]
                       [--l1 CPU_L1_CACHE_SIZE] [--l2 CPU_L2_CACHE_SIZE]
                       [--l3 CPU_L3_CACHE_SIZE] [--cores NUM_CORES]
                       [--hyperthreads CPU_HYPERTHREADS] [--hours CPU_HOURS]
                       [--to TOEMAILS] [-f FROMEMAIL] [-S SMTP] [--tls]
                       [--no-tls] [--starttls] [--no-starttls]
                       [-U EMAIL_USERNAME] [-P EMAIL_PASSWORD] [--test-email]

This program will automatically get and register assignments, report
assignment progress and results, upload proof files to and download
certification starting values from PrimeNet for the Mlucas, GpuOwl, PRPLL,
PrMers, CUDALucas, mfaktc and mfakto GIMPS programs. It can get assignments
and report results to mersenne.ca for exponents above the PrimeNet limit of
1G. It also saves its configuration to a 'prime.ini' file by default, so it is
only necessary to give most of the arguments once. The first time it is run,
it will register the current
Mlucas/GpuOwl/PRPLL/PrMers/CUDALucas/mfaktc/mfakto instance with PrimeNet (see
the Registering Options below). Then, it will report assignment results and
upload any proof files to PrimeNet immediately. It will get assignments on the
--timeout interval, or only once if --timeout is 0. It will additionally
report the progress on the --checkin interval.

options:
  -h, --help            show this help message and exit
  --version             show program's version number and exit
  -d, --debug           Output detailed information. Provide multiple times
                        for even more verbose output.
  -w WORKDIR, --workdir WORKDIR
                        Working directory with the configuration file from
                        this program, Default: '.' (current directory)
  -D DIRS, --dir DIRS   Directories relative to --workdir with the work and
                        results files from the GIMPS program. Provide once for
                        each worker. This is incompatible with PRPLL.
  -i WORKTODO_FILE, --work-file WORKTODO_FILE
                        Work file filename, Default: 'worktodo.txt'. Not used
                        with PRPLL.
  -r RESULTS_FILE, --results-file RESULTS_FILE
                        Results file filename, Default: 'results.json.txt' for
                        mfaktc/mfakto or 'results.txt' otherwise. Not used
                        with PRPLL.
  -L LOGFILE, --logfile LOGFILE
                        Log file filename, Default: 'autoprimenet.log'
  -l LOCALFILE, --config-file LOCALFILE
                        Local configuration file filename, Default:
                        'prime.ini'
  --archive-proofs ARCHIVE_DIR
                        Directory to archive PRP proof files after upload,
                        Default: None
  -u USER_ID, --username USER_ID
                        GIMPS/PrimeNet User ID. Create a GIMPS/PrimeNet
                        account: https://www.mersenne.org/update/. If you do
                        not want a PrimeNet account, you can use ANONYMOUS.
  -T WORK_PREFERENCE, --workpref WORK_PREFERENCE
                        Work preference, Default: 150. Supported work
                        preferences: 2 (Trial factoring), 4 (P-1 factoring), 5
                        (ECM factoring), 8 (ECM on Mersenne cofactors), 12
                        (Trial factoring GPU), 100 (First time LL tests), 101
                        (Double-check LL tests), 102 (World record LL tests),
                        104 (100M digit LL tests), 106 (Double-check LL tests
                        with zero shift count), 150 (First time PRP tests),
                        151 (Double-check PRP tests), 152 (World record PRP
                        tests), 153 (100M digit PRP tests), 154 (Smallest
                        available first time PRP that needs P-1 factoring),
                        155 (Double-check using PRP with proof), 156 (Double-
                        check using PRP with proof and nonzero shift count),
                        160 (First time PRP on Mersenne cofactors), 161
                        (Double-check PRP on Mersenne cofactors). Provide once
                        to use the same work preference for all workers or
                        once for each worker to use different work
                        preferences. Not all worktypes are supported by all
                        the GIMPS programs.
  --cert-work           Get PRP proof certification work, Default: None.
                        Currently only supported by PRPLL.
  --no-cert-work
  --cert-work-limit CERT_CPU_LIMIT
                        PRP proof certification work limit in percentage of
                        CPU or GPU time, Default: 10%. Requires the --cert-
                        work option.
  --min-exp MIN_EXP     Minimum exponent to get from PrimeNet or TF1G (2 -
                        9,999,999,999). TF1G assignments are supported by
                        setting this flag to 1,000,000,000 or above.
  --max-exp MAX_EXP     Maximum exponent to get from PrimeNet or TF1G (2 -
                        9,999,999,999)
  --min-bit MIN_BIT     Minimum bit level of TF assignments to get from
                        PrimeNet or TF1G
  --max-bit MAX_BIT     Maximum bit level of TF assignments to get from
                        PrimeNet or TF1G
  --force-target-bits   Perform a depth first factor search by forcing TF
                        assignments to factor to the target bit level (as
                        listed on mersenne.ca)
  -m, --mlucas          Get assignments for Mlucas.
  -g, --gpuowl          Get assignments for GpuOwl.
  --prpll               Get assignments for PRPLL. Only PRPLL NTT is PrimeNet
                        server compatible and thus is fully supported.
  --prmers              Get assignments for PrMers. This is experimental and
                        for testing only.
  --cudalucas           Get assignments for CUDALucas.
  --mfaktc              Get assignments for mfaktc.
  --mfakto              Get assignments for mfakto.
  --num-workers NUM_WORKERS
                        Number of workers (CPU Cores/GPUs), Default: 1
  -n NUM_CACHE, --num-cache NUM_CACHE
                        Number of assignments to cache, Default: 0. Deprecated
                        in favor of the --days-work option.
  -W DAYS_OF_WORK, --days-work DAYS_OF_WORK
                        Days of work to queue ((0-180] days), Default: 1 day
                        for mfaktc/mfakto or 3 days otherwise. Increases
                        num_cache when the time left for all assignments is
                        less than this number of days.
  --force-pminus1 TESTS_SAVED
                        Force P-1 factoring before LL/PRP tests and/or change
                        the default PrimeNet PRP and P-1 tests_saved value.
  --pminus1-threshold PM1_MULTIPLIER
                        Retry the P-1 factoring before LL/PRP tests only if
                        the existing P-1 bounds are less than the target
                        bounds (as listed on mersenne.ca) times this
                        threshold/multiplier. Requires the --force-pminus1
                        option.
  --force-pminus1-bounds {MIN,MID,MAX}
                        Force using the 'MIN', 'MID' or 'MAX' optimal P-1
                        bounds (as listed on mersenne.ca) for P-1 tests. For
                        Mlucas and PrMers, this will rewrite Pfactor=
                        assignments to Pminus1=. For GpuOwl, this will use a
                        nonstandard Pfactor= format to add the bounds. Can be
                        used in combination with the --force-pminus1 option.
  --ecm-bounds-multiplier ECM_MULTIPLIER
                        Multiply the PrimeNet server assigned ECM bounds by
                        this multiplier.
  --convert-ll-to-prp   Convert all LL assignments to PRP. This is for use
                        when registering assignments.
  --convert-prp-to-ll   Convert all PRP assignments to LL. This is
                        automatically enabled for first time PRP assignments
                        when the --workpref option is for a first time LL
                        worktype.
  --no-report-100m      Do not report any prime results for exponents greater
                        than or equal to 100 million digits. You must setup
                        another method to notify yourself, such as setting the
                        notification options below.
  --report-100m
  --checkin HOURS_BETWEEN_CHECKINS
                        Hours to wait between sending assignment progress and
                        expected completion dates (1-168 hours), Default: 1
                        hours.
  -t TIMEOUT, --timeout TIMEOUT
                        Seconds to wait between updates, Default: 3600 seconds
                        (1 hour). Use 0 to update once and exit.
  -s, --status          Output a status report and any expected completion
                        dates for all assignments and exit.
  --report-results      Report assignment results and exit. Requires PrimeNet
                        User ID.
  --upload-proofs       Report assignment results, upload all PRP proofs and
                        exit. Requires PrimeNet User ID.
  --recover             Report assignment results, recover all assignments and
                        exit. This will overwrite any existing work files.
  --recover-all         The same as --recover, except for PrimeNet it will
                        additionally recover expired assignments and for
                        mersenne.ca it will recover all assignments for all
                        systems/workers to the first worker. This will
                        overwrite any existing work files.
  --register-exponents  Prompt for all parameters needed to register one or
                        more specific exponents and exit.
  --unreserve EXPONENT  Unreserve the exponent and exit. Use this only if you
                        are sure you will not be finishing this exponent.
  --unreserve-all       Report assignment results, unreserve all assignments
                        and exit.
  --no-more-work        Prevent this program from getting new assignments and
                        exit.
  --resume-work         Resume getting new assignments after having previously
                        run the --no-more-work option and exit.
  --ping                Ping the PrimeNet server, show version information and
                        exit.
  --v6                  Use the experimental PrimeNet v6 API. Currently only
                        works with the --ping option.
  --debug-info          Output debugging information to include in bug reports
                        and exit.
  --no-version-check    Disable the automatic AutoPrimeNet and GIMPS program
                        version check
  --version-check
  --version-check-channel {alpha,beta,stable}
                        Prefer the 'alpha', 'beta' or 'stable' channel/branch
                        when checking for new versions of AutoPrimeNet and the
                        GIMPS program. Not all programs provide alpha or beta
                        releases. Default: 'stable'
  --no-watch            Report assignment results and upload proof files on
                        the --timeout interval instead of immediately. This
                        may be needed if the filesystem is unsupported.
  --watch
  --no-encrypt          Do not encrypt any passwords in the configuration
                        file.
  --encrypt             Encrypt any passwords from the --proxy-password and
                        --email-password options in the configuration file.
                        Uses AES-256-GCM encryption with PBKDF2-HMAC-SHA256
                        key derivation. Requires the OpenSSL library. Does
                        opportunistic encryption by default. Provide this
                        option to enable strict encryption.
  --no-color            Do not use color in output.
  --color
  --setup               Prompt for all the options that are needed to setup
                        this program and exit.

Connection Options:
  Optionally configure a proxy server.

  --proxy-type {http,https,socks5,socks5h}
                        Proxy server type, 'http', 'https', 'socks5' or
                        'socks5h', Default 'http'. SOCKS proxies require the
                        Requests 2.10 or greater and PySocks libraries.
  -x PROXY, --proxy PROXY
                        Proxy server. Optionally include a port with the
                        'hostname:port' syntax.
  --proxy-username PROXY_USERNAME
                        Proxy server username
  --proxy-password PROXY_PASSWORD
                        Proxy server password

Registering Options:
  Sent to PrimeNet/GIMPS when registering. It will automatically send the
  progress, which allows the program to then be monitored on the GIMPS
  website CPUs page (https://www.mersenne.org/cpus/), just like with
  Prime95/MPrime. This also allows the program to get much smaller Category
  0 and 1 exponents, if it meets the other requirements
  (https://www.mersenne.org/thresholds/). AutoPrimeNet should automatically
  detect most of this system information. When using the --setup option and
  a GPU based GIMPS program, it can optionally report the GPU instead of the
  CPU.

  -H COMPUTER_ID, --hostname COMPUTER_ID
                        Optional computer name, Default: 'example'
  --cpu-model CPU_BRAND
                        Processor (CPU) model, Default: 'cpu.unknown'
  --features CPU_FEATURES
                        CPU features, Default: ''
  --frequency CPU_SPEED
                        CPU frequency/speed (MHz), Default: 1000 MHz
  --memory MEMORY       Total physical memory (RAM) (MiB), Default: 1024 MiB
  --max-memory DAY_NIGHT_MEMORY
                        Configured day/night P-1/ECM stage 2 memory (MiB),
                        Default: 921 MiB (90% of physical memory). Required
                        for P-1 assignments.
  --max-disk-space WORKER_DISK_SPACE
                        Configured disk space limit per worker to store the
                        proof interim residues files for PRP tests
                        (GiB/worker), Default: 0.0 GiB/worker. Use 0 to not
                        send.
  --l1 CPU_L1_CACHE_SIZE
                        L1 Data Cache size (KiB), Default: 8 KiB
  --l2 CPU_L2_CACHE_SIZE
                        L2 Cache size (KiB), Default: 512 KiB
  --l3 CPU_L3_CACHE_SIZE
                        L3 Cache size (KiB), Default: 0 KiB
  --cores NUM_CORES     Number of physical CPU cores, Default: 1
  --hyperthreads CPU_HYPERTHREADS
                        Number of CPU threads per core (0 is unknown),
                        Default: 0. Choose 1 for non-hyperthreaded and 2 or
                        more for hyperthreaded.
  --hours CPU_HOURS     Hours per day you expect the GIMPS program will run (1
                        - 24), Default: 24 hours. Used to give better
                        estimated completion dates.

Notification Options:
  Optionally configure this program to automatically send an e-mail/text
  message notification if there is an error, if the GIMPS program has
  stalled, if the available disk space is low, if it found a new Mersenne
  prime or if there is a new version of the GIMPS program. Send text
  messages by using your mobile providers e-mail to SMS or MMS gateway. Use
  the --test-email option to verify the configuration. When using the
  --setup option, it will automatically lookup the configuration.

  --to TOEMAILS         To e-mail address. Use multiple times for multiple
                        To/recipient e-mail addresses. Defaults to the --from
                        value if not provided.
  -f FROMEMAIL, --from FROMEMAIL
                        From e-mail address
  -S SMTP, --smtp SMTP  SMTP server. Optionally include a port with the
                        'hostname:port' syntax. Defaults to port 465 with
                        --tls and port 25 otherwise.
  --tls                 Use a secure connection with SSL/TLS
  --no-tls
  --starttls            Upgrade to a secure connection with StartTLS
  --no-starttls
  -U EMAIL_USERNAME, --email-username EMAIL_USERNAME
                        SMTP server username
  -P EMAIL_PASSWORD, --email-password EMAIL_PASSWORD
                        SMTP server password
  --test-email          Send a test e-mail message and exit
```


## Contributing

Pull requests welcome! Ideas for contributions:

* Support more GIMPS programs.
* Support FreeBSD and Android.
	* ⭐ Help wanted
* Create icon/logo for standalone executables.
* Support setting more of the program options.
* Improve the error handling of PrimeNet API calls.
* Improve the assignment ETA calculation, especially for P-1 and ECM.
* Improve the performance.
* Support reporting interim residues.
* Localize the program and translate the output into other languages (see [here](https://mersenneforum.org/showthread.php?t=27046)).
* Adapt Loïc Le Loarer's [test suite](https://github.com/llloic11/primenet/tree/main/tests).
* Add an optional GUI using [Tk](https://en.wikipedia.org/wiki/Tk_(software)) and the [tkinter library](https://docs.python.org/3/library/tkinter.html).
* Add docstrings to all functions.
* Support submitting P-1 results for Fermat numbers.
* Support configuring the DNS server.

Thanks to [Daniel Connelly](https://github.com/Danc2050) for updating the PrimeNet Python script from Mlucas to eliminate the password requirement by getting assignments using the [PrimeNet API](https://v5.mersenne.org/v5design/v5webAPI_0.97.html) and to support reporting the assignment results and progress for CUDALucas using the PrimeNet API!

Thanks to Isaac Terrell for providing the needed PRP proof files to test the proof file uploading feature.

Thanks to [Tyler Busby](https://github.com/brubsby) for updating AutoPrimeNet to support mfaktc/mfakto and getting assignments and reporting results to mersenne.ca for exponents above the PrimeNet limit of 1G.

