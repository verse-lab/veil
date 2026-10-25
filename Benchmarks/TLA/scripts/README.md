# Upstream source checks

Benchmark files (`.tla`, `.cfg`) cite their upstream file in a comment, as a
GitHub URL pinned to a full commit. These scripts give each such pair a verdict;
see [`check_sources.py`](check_sources.py) for the definitions. The decision is
`code_view()`, `code_lines()` and `verdict()` at its top, and `VERDICT_EXAMPLES`
below them specifies the tricky cases and runs before every comparison.

Run from the repository root (Python 3.9+, standard library only). `--help`
covers skipped files, errors, exit codes and the output directory.

```sh
./Benchmarks/TLA/scripts/check_all_sources.py --output /tmp/tla-all-sources   # every benchmark
python3 Benchmarks/TLA/scripts/check_sources.py                             # only TLAPlusExamples/
python3 Benchmarks/TLA/scripts/check_sources.py --file Benchmarks/TLA/AWS/AWS.tla
```

The check compares text only: it runs neither SANY nor TLC, says nothing about
the Veil translations, and reports layout-only edits that TLC ignores as `CHANGED`.

`German.cfg` and `MultiPaxosUs.cfg` check models that are not in the repository,
because their upstream repositories have no license. To run TLC on them, first
run `python3 Benchmarks/TLA/scripts/fetch_upstream.py`: it downloads the models
next to the configurations and verifies their pinned SHA-256. Git ignores the
downloaded files; `check_all_sources.py` checks them against the same hashes
instead of counting them as benchmark files.

# TLC runs

[`run_tlc.py`](run_tlc.py) runs TLC on `.tla`/`.cfg` pairs, each with every
given worker count, and writes `results.csv` to its output directory (by default
`benchmark-results/tlc`): one row per pair and worker count, with the status,
times, state counts and peak memory. `csv/tlc-<N>-worker.csv` there has the runs
at `N` workers that TLC completed, with or without a violation. A run whose
result is recorded there is skipped, unless it was interrupted, a file TLC read
for it has changed since, or it timed out with a shorter `--timeout`. It needs
Java 11 or later and the packages in [`requirements.txt`](requirements.txt):

```sh
python3 -m pip install -r Benchmarks/TLA/scripts/requirements.txt
python3 Benchmarks/TLA/scripts/run_tlc.py --workers 1 4 8 \
    --pair Benchmarks/TLA/Paxos/Paxos.tla Benchmarks/TLA/Paxos/Paxos.cfg
```

The optional third value of `--pair` names the pair's results; it defaults to
the stem of the `.cfg`. `--dry-run` lists the runs to measure and the results to
reuse; `--help` covers the statuses, the output directory and the options.

[`run_all.py`](run_all.py) runs all the TLA+ benchmarks in one step. It first
downloads the models that `fetch_upstream.py` provides, when they are missing,
then runs `run_tlc.py` on the 20 benchmarks it lists, with 1 to as many workers
as the machine has CPUs; its other arguments go to `run_tlc.py`:

```sh
python3 Benchmarks/TLA/scripts/run_all.py --dry-run   # only list the runs
python3 Benchmarks/TLA/scripts/run_all.py
```

TLC is the build of revision
[`8f4bc8b`](https://github.com/tlaplus/tlaplus/commit/8f4bc8b73ad1202774a6bf70143436f8ba50aab0)
(`TLC2 Version 2026.09.25.163503`) with the
[`202609120237`](https://github.com/tlaplus/CommunityModules/releases/tag/202609120237)
release of the Community Modules. When their jars are missing, the script
downloads them into `jars/tlc-8f4bc8b/` here and checks their SHA-256
(`--fetch-jars` only does that). TLC publishes no jar per revision, and its
rolling `v1.8.0` release has moved on to later builds, so `tla2tools.jar` comes
from version `2026.9.251645` of the TLA+ extension for VS Code on Open VSX,
published with that build, which bundles it. `--tla2tools` and
`--community-modules` run other jars instead, e.g. TLC built from the same
revision, which has another SHA-256 since its manifest records the build time.
Every run has the command line

```sh
java -Xms20G -Xmx20G -XX:+UseParallelGC -XX:+IgnoreUnrecognizedVMOptions \
    -cp tla2tools.jar:CommunityModules-deps.jar -DTLA-Library= tlc2.TLC -tool -modelcheck \
    -coverage 1 -workers N -cleanup -config CFG -metadir STATES SPEC
```

with the heap of `--heap` and a timeout of 36000 seconds by default (`--timeout`).
`STATES`, where TLC keeps its states, is in the run's directory under the output
directory, and is deleted as soon as TLC exits, however the run ends: at most
one run's states take disk space at any time.
