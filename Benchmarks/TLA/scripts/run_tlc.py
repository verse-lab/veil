#!/usr/bin/env python3
"""Run TLC on .tla/.cfg pairs at the given worker counts and summarize the results in a CSV.

Every pair is checked once with each worker count: all pairs, in the order of --pair, with the
first count of --workers, then all with the next one. A run whose result is recorded in --output
is skipped, unless it was interrupted, a file TLC read for it (the .cfg and the modules) has
changed since, or it timed out with a shorter --timeout than the current one; those are
measured again.

TLC is the build of git revision 8f4bc8b (TLC2 Version 2026.09.25.163503), with the
CommunityModules release 202609120237, unless --tla2tools or --community-modules give other
jars. The pinned jars are downloaded into jars/tlc-8f4bc8b next to this script when they are
missing, and checked against their SHA-256; --fetch-jars only does that. Every run has the
command line
  java -Xms<heap> -Xmx<heap> -XX:+UseParallelGC -XX:+IgnoreUnrecognizedVMOptions
       -cp tla2tools.jar:CommunityModules-deps.jar -DTLA-Library= tlc2.TLC -tool -modelcheck
       -coverage 1 -workers <N> -cleanup -config <cfg> -metadir <states> <spec>
in a fresh directory under --output, which also holds the <states> of TLC. Those are deleted as
soon as TLC exits, however the run ends, and at the start of an invocation when an earlier one
was killed (--cleanup-states only does that). TLC writes nothing next to the specs.

--output (default benchmark-results/tlc) holds:
  plan.json                     the Java, heap, jars and machine of every result there; other
                                settings need another --output
  runs/<name>/w<N>/result.json  the result of a pair at N workers; attempts/ keeps the TLC log
                                (tlc.log) and the result of every attempt
  results.csv                   one row per recorded result, rewritten after every run
  csv/tlc-<N>-worker.csv        the results at N workers of the runs TLC completed (ok or
                                violation), in the columns of the earlier per-worker TLC tables
                                after the name of the pair
  summary.json                  the outcome of the requested runs of the last invocation
Paths there, in the TLC logs too, are relative to --output inside it, otherwise relative to the
repository, or starting with ~ in the home directory; no host name is recorded.
Status of a run: ok (complete search, no error), violation (TLC found a deadlock or an
invariant, property or assertion violation), timeout, error, interrupted, or over_budget
(finished just after the timeout). The exit code is 1 when a requested run ended in an error
or ok runs of the same pair found different numbers of distinct states.

Needs Java 11 or later and the packages in requirements.txt. From the repository root:
  python3 -m pip install -r Benchmarks/TLA/scripts/requirements.txt
  python3 Benchmarks/TLA/scripts/run_tlc.py --workers 1 4 8 \\
      --pair Benchmarks/TLA/Paxos/Paxos.tla Benchmarks/TLA/Paxos/Paxos.cfg \\
      --pair Benchmarks/TLA/Raft/MC.tla Benchmarks/TLA/Raft/MC.cfg Raft
  python3 Benchmarks/TLA/scripts/run_tlc.py ... --dry-run     # only list the runs
"""

import argparse
from collections import Counter
import csv
from datetime import datetime, timezone
import fcntl
import hashlib
import http.client
import io
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import subprocess
import sys
import threading
import time
import urllib.request
import zipfile

try:
    import psutil
except ImportError:
    psutil = None


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
HOME = Path.home()
REQUIREMENTS = HERE / "requirements.txt"
JAR_DIR = HERE / "jars/tlc-8f4bc8b"
# The TLA+ extension for VS Code, published right after TLC's nightly build of 8f4bc8b, bundles
# that tla2tools.jar; the rolling GitHub release of TLC that served it has moved on since.
VSIX = "https://open-vsx.org/api/tlaplus/vscode-ide/2026.9.251645/file/tlaplus.vscode-ide-2026.9.251645.vsix"
# The pinned jars: SHA-256, the option giving another one, and sources (URL, member of the archive)
JARS = {
    "tla2tools.jar": (
        "ab4694601923fd5ac06452abbf847c366a5054a3d739552085edd6ed986c29ec", "--tla2tools",
        [(VSIX, "extension/tools/tla2tools.jar")]),
    "CommunityModules-deps.jar": (
        "3d9a282c360e90d55e9bbe99caa2987d508fef1556d652760b4af4455e283733", "--community-modules",
        [("https://github.com/tlaplus/CommunityModules/releases/download/202609120237/CommunityModules-deps.jar",
          None),
         (VSIX, "extension/tools/CommunityModules-deps.jar")]),
}
# Deadlock, safety, liveness and assertion violations (tlc2.output.EC.ExitStatus)
VIOLATION_EXIT_CODES = (11, 12, 13, 14)
# Modules TLC read from files; those read from its jars are followed by their jar URL.
PARSED_FILE = re.compile(r"^Parsing file (.+\.tla)$", re.MULTILINE)
# What is read from TLC's output; the final counts are the last ones it prints.
PATTERNS = {
    "version": re.compile(r"TLC2 Version ([\d.]+)(?: \(rev: (\w+)\))?"),
    "heap_info": re.compile(r"with (\d+)MB heap"),
    "final_states": re.compile(r"(\d+) states generated, (\d+) distinct states found, "
                               r"(\d+) states left on queue"),
    "depth": re.compile(r"depth of the complete state graph search is (\d+)"),
    "finished_time": re.compile(r"Finished in (.+?) at"),
    "error": re.compile(r"Error: (.+)"),
    "invariant_violated": re.compile(r"Invariant (.+) is violated"),
    "property_violated": re.compile(r"Temporal properties were violated"),
    "deadlock": re.compile(r"deadlock reached"),
    "success": re.compile(r"Model checking completed\. No error has been found"),
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode()


def atomic_json(path, value):
    tmp = path.with_suffix(".tmp")
    tmp.write_bytes(encoded(value))
    tmp.replace(path)


def display(path):
    """A path as recorded: relative to the repository inside it, starting with ~ in the home directory."""
    if path.is_relative_to(REPO):
        return str(path.relative_to(REPO))
    if HOME != Path(HOME.anchor) and path.is_relative_to(HOME):
        return str("~" / path.relative_to(HOME))
    return str(path)


def located(name):
    """The path that display() records as name."""
    return REPO / Path(name).expanduser()


def redact(text):
    """text with the absolute paths in the repository and the home directory written as display() does."""
    text = text.replace(f"{REPO}{os.sep}", "")
    return text.replace(f"{HOME}{os.sep}", f"~{os.sep}") if HOME != Path(HOME.anchor) else text


def tlc_command(java, heap, classpath, workers, cfg, metadir, spec):
    return [java, f"-Xms{heap}", f"-Xmx{heap}", "-XX:+UseParallelGC", "-XX:+IgnoreUnrecognizedVMOptions",
            "-cp", classpath, "-DTLA-Library=", "tlc2.TLC", "-tool", "-modelcheck", "-coverage", "1",
            "-workers", str(workers), "-cleanup", "-config", str(cfg), "-metadir", str(metadir), str(spec)]


def parse_output(output):
    result = {
        "tlc_version": None, "tlc_revision": None, "jvm_heap_mb": None, "states_generated": 0,
        "distinct_states": 0, "states_in_queue": 0, "depth": 0, "tlc_reported_time": None,
        "success": False, "error_message": None, "invariant_violated": None, "deadlock": False,
    }
    match = PATTERNS["version"].search(output)
    if match:
        result["tlc_version"], result["tlc_revision"] = match.groups()
    match = PATTERNS["heap_info"].search(output)
    if match:
        result["jvm_heap_mb"] = int(match.group(1))
    for match in PATTERNS["final_states"].finditer(output):
        result["states_generated"], result["distinct_states"], result["states_in_queue"] = map(int, match.groups())
    match = PATTERNS["depth"].search(output)
    if match:
        result["depth"] = int(match.group(1))
    match = PATTERNS["finished_time"].search(output)
    if match:
        result["tlc_reported_time"] = match.group(1)
    if PATTERNS["success"].search(output):
        result["success"] = True
    match = PATTERNS["error"].search(output)
    if match:
        result["error_message"] = match.group(1)
    match = PATTERNS["invariant_violated"].search(output)
    if match:
        result["invariant_violated"] = match.group(1)
        result["error_message"] = f"Invariant {match.group(1)} violated"
    if PATTERNS["property_violated"].search(output):
        result["error_message"] = "Temporal properties violated"
    if PATTERNS["deadlock"].search(output):
        result["deadlock"] = True
        result["error_message"] = "Deadlock reached"
    return result


class MemoryMonitor:
    """Peak resident memory of a process and its descendants, sampled in a background thread."""

    def __init__(self, pid, interval=0.5):
        self.pid = pid
        self.interval = interval
        self.peak_memory_mb = 0.0
        self._stop_event = threading.Event()
        self._thread = None

    def start(self):
        self._thread = threading.Thread(target=self._monitor_loop, daemon=True)
        self._thread.start()

    def stop(self):
        self._stop_event.set()
        if self._thread:
            self._thread.join(timeout=2.0)
        return self.peak_memory_mb

    def _monitor_loop(self):
        try:
            process = psutil.Process(self.pid)
            while not self._stop_event.is_set():
                try:
                    mem = process.memory_info().rss
                    for child in process.children(recursive=True):
                        try:
                            mem += child.memory_info().rss
                        except (psutil.NoSuchProcess, psutil.AccessDenied):
                            pass
                    self.peak_memory_mb = max(self.peak_memory_mb, mem / (1024 * 1024))
                except (psutil.NoSuchProcess, psutil.AccessDenied):
                    break
                self._stop_event.wait(self.interval)
        except Exception as e:
            print(f"Memory monitor error: {e}")


def fetch_jars():
    """The pinned jars in JAR_DIR, downloading those that are missing."""
    JAR_DIR.mkdir(parents=True, exist_ok=True)
    downloads = {}
    for name, (expected, option, sources) in JARS.items():
        path = JAR_DIR / name
        if path.exists():
            if digest(path.read_bytes()) != expected:
                raise ValueError(f"{display(path)} is not the pinned {name}; delete it to download that one")
            continue
        errors = []
        for url, member in sources:
            try:
                if url not in downloads:
                    print(f"Downloading {url}", flush=True)
                    with urllib.request.urlopen(url, timeout=300) as response:
                        downloads[url] = response.read()
                data = zipfile.ZipFile(io.BytesIO(downloads[url])).read(member) if member else downloads[url]
            except (OSError, http.client.HTTPException, zipfile.BadZipFile, KeyError) as exc:
                errors.append(f"{url}: {exc}")
                continue
            if digest(data) != expected:
                errors.append(f"{url}: unexpected SHA-256 {digest(data)}")
                continue
            # Write it whole or not at all
            tmp = path.with_name(f".{name}.tmp")
            tmp.write_bytes(data)
            tmp.replace(path)
            print(f"  {display(path)}: SHA-256 checked", flush=True)
            break
        else:
            raise ValueError(f"Could not download the pinned {name} ({'; '.join(errors)}); give one with {option}")
    return {name: JAR_DIR / name for name in JARS}


def given_jars(args):
    return {"tla2tools.jar": args.tla2tools, "CommunityModules-deps.jar": args.community_modules}


def jar_sha256(args):
    """SHA-256 of the jars TLC runs with: those given, otherwise the pinned ones."""
    return {name: digest(path.read_bytes()) if path else JARS[name][0] for name, path in given_jars(args).items()}


def jar_paths(args):
    """The jars TLC runs with, downloading the pinned ones that are needed and missing."""
    given = given_jars(args)
    pinned = fetch_jars() if None in given.values() else {}
    return {name: path or pinned[name] for name, path in given.items()}


def parse_pairs(values):
    pairs = []
    for value in values:
        if len(value) not in (2, 3):
            raise ValueError(f"--pair takes SPEC CFG [NAME], not: {' '.join(value)}")
        spec, cfg = (Path(v).expanduser().resolve() for v in value[:2])
        if spec.suffix != ".tla" or cfg.suffix != ".cfg" or not spec.is_file() or not cfg.is_file():
            raise ValueError(f"--pair needs an existing .tla and .cfg file: {value[0]} {value[1]}")
        name = value[2] if len(value) == 3 else cfg.stem
        if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.+-]*", name):
            raise ValueError(f"Invalid name {name!r}; give one after the files: --pair SPEC CFG NAME")
        pairs.append({"name": name, "spec_file": display(spec), "config_file": display(cfg)})
    duplicates = [name for name, count in Counter(p["name"] for p in pairs).items() if count > 1]
    if duplicates:
        raise ValueError(f"Several pairs named {', '.join(duplicates)}; name them: --pair SPEC CFG NAME")
    return pairs


def prepare(args, jars_sha256):
    """The settings of every result in --output, checked against its plan.json."""
    java = subprocess.run([args.java, "-version"], capture_output=True, text=True, timeout=10, check=True)
    plan = {
        "command": tlc_command("<java>", "<heap>", "<jars>", "<workers>", "<cfg>", "<states>", "<spec>"),
        "java_cmd": redact(args.java), "java_version": redact((java.stdout + java.stderr).strip()),
        "heap": args.heap, "jar_sha256": jars_sha256,
        "platform": platform.platform(), "cpu_count": os.cpu_count(),
        "memory_bytes": psutil.virtual_memory().total,
    }
    plan_path = args.output / "plan.json"
    previous = json.loads(plan_path.read_text()) if plan_path.exists() else plan
    changed = sorted(key for key in plan.keys() | previous.keys() if plan.get(key) != previous.get(key))
    if changed:
        raise ValueError(f"Settings differ from {display(plan_path)}: {', '.join(changed)}. "
                         "Use a fresh --output directory.")
    return plan


def cleanup_attempt_states(attempt):
    """Delete only the private metadir of an invocation whose JVM has exited."""
    states = attempt / "states"
    if states.is_symlink() or states.resolve() != states:
        raise ValueError(f"Refusing to clean a symlinked state path: {states}")
    if states.exists():
        print(f"  cleaning states: {display(states)}", flush=True)
        shutil.rmtree(states)
        return True
    return False


def cleanup_output_states(output):
    """Called under the output lock; also reject orphaned TLC processes."""
    for process in psutil.process_iter(["pid", "cmdline"]):
        cmd = process.info["cmdline"] or []
        if "tlc2.TLC" in cmd and "-metadir" in cmd:
            metadir = Path(cmd[cmd.index("-metadir") + 1]).resolve()
            if metadir.is_relative_to(output):
                raise ValueError(f"TLC PID {process.pid} still uses {display(metadir)}; stop it before cleanup")
    attempts = []
    for states in sorted(output.glob("runs/*/w*/attempts/*/states")):
        parts = states.relative_to(output).parts
        if (len(parts) != 6 or not re.fullmatch(r"w[1-9][0-9]*", parts[2])
                or not parts[4].isdigit() or not (states.parent / "tlc.log").is_file()
                or states.resolve() != states):
            raise ValueError(f"Unrecognized state directory: {states}")
        attempts.append(states.parent)
    for attempt in attempts:
        cleanup_attempt_states(attempt)
    print(f"Cleaned {len(attempts)} state directories; logs and results retained.", flush=True)


def kill_process_group(process):
    # Each invocation owns its session; never kill unrelated Java processes.
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    process.wait()


def run_process(command, cwd, log_path, timeout, monitor_class=MemoryMonitor):
    """No pipe read can delay timeout. Keep even partial/error output on disk."""
    start = time.monotonic()
    timed_out = False
    interrupted = False
    with log_path.open("w") as log:
        process = subprocess.Popen(command, cwd=cwd, stdout=log, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        monitor = monitor_class(process.pid)
        try:
            monitor.start()
            try:
                process.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                kill_process_group(process)
            except KeyboardInterrupt:
                interrupted = True
                kill_process_group(process)
        finally:
            if process.poll() is None:
                kill_process_group(process)
            elapsed = time.monotonic() - start
            peak = monitor.stop()
    return process.returncode, elapsed, timed_out, interrupted, peak


def classify(record, limit):
    if record["interrupted"]:
        return "interrupted"
    if record["timeout"]:
        return "timeout"
    if record["exit_code"] in VIOLATION_EXIT_CODES:
        return "violation"
    if (record["exit_code"] != 0 or not record["success"] or record["error_message"]
            or record["states_in_queue"] != 0 or record["distinct_states"] <= 0):
        return "error"
    if record["wall_time_seconds"] > limit:
        return "over_budget"
    return "ok"


def read_result(path):
    return json.loads(path.read_text()) if path.exists() else None


def rerun_reason(record, pair, timeout, plan_hash):
    """Why a run is measured, or None when its recorded result is reused."""
    if record is None:
        return "no result yet"
    if (record["spec_file"], record["config_file"]) != (pair["spec_file"], pair["config_file"]):
        raise ValueError(f"The name {pair['name']} is taken in --output by {record['spec_file']} "
                         f"{record['config_file']}; name this pair differently: --pair SPEC CFG NAME")
    if record["plan_sha256"] != plan_hash:
        raise ValueError(f"{pair['name']} workers={record['workers']} has other settings than plan.json; "
                         "use a fresh --output directory")
    if record["status"] == "interrupted":
        return "interrupted"
    changed = [name for name, sha in record["inputs"].items()
               if not located(name).is_file() or digest(located(name).read_bytes()) != sha]
    if changed:
        return f"changed since: {', '.join(changed)}"
    if record["status"] in ("timeout", "over_budget") and record["timeout_seconds"] < timeout:
        return f"{record['status']} with --timeout {record['timeout_seconds']:g}"
    return None


def schedule(args, plan, pairs):
    """Every requested run, with its recorded result and why it is measured (None: reused)."""
    plan_hash = digest(encoded(plan))
    runs = []
    for workers in args.workers:
        for pair in pairs:
            record = read_result(args.output / "runs" / pair["name"] / f"w{workers}/result.json")
            runs.append((pair, workers, record, rerun_reason(record, pair, args.timeout, plan_hash)))
    return runs


def print_schedule(runs):
    measured = sum(1 for run in runs if run[3])
    print(f"Requested runs: {len(runs)}; to measure: {measured}; recorded results reused: {len(runs) - measured}",
          flush=True)
    for pair, workers, record, reason in runs:
        if reason:
            print(f"  measure {pair['name']} workers={workers}: {reason}")
        else:
            print(f"  reuse   {pair['name']} workers={workers}: {record['status']}, "
                  f"{record['wall_time_seconds']:.3f}s, {record['distinct_states']} distinct states")
    sys.stdout.flush()


def measure(pair, workers, args, plan, classpath):
    run_dir = args.output / "runs" / pair["name"] / f"w{workers}"
    run_dir.mkdir(parents=True, exist_ok=True)
    # Preserve logs/results of interrupted attempts, but discard scratch states.
    attempts = run_dir / "attempts"
    attempts.mkdir(exist_ok=True)
    attempt = attempts / f"{time.time_ns()}"
    attempt.mkdir()
    spec, cfg = located(pair["spec_file"]), located(pair["config_file"])
    # Hashed before TLC reads them; it finds the other modules in the directory of the spec.
    hashes = {path: digest(path.read_bytes()) for path in [cfg, *spec.parent.glob("*.tla")]}
    command = tlc_command(args.java, args.heap, classpath, workers, cfg, attempt / "states", spec)
    log_path = attempt / "tlc.log"
    print(f"{pair['name']} workers={workers} timeout={args.timeout:g}s", flush=True)
    start_time = datetime.now(timezone.utc).isoformat()
    try:
        # The attempt is the working directory, so that the JVM writes nothing next to the spec.
        code, elapsed, timed_out, interrupted, peak = run_process(command, attempt, log_path, args.timeout)
    finally:
        # run_process has reaped the JVM, including on timeout/interruption. TLC deletes its
        # states itself only after a successful run; deleting the rest is not charged to the
        # model-checking wall time.
        cleanup_attempt_states(attempt)
    output = log_path.read_text(errors="replace")
    read = [cfg, spec, *(Path(m).resolve() for m in PARSED_FILE.findall(output))]
    log_path.with_suffix(".tmp").write_text(redact(output))
    log_path.with_suffix(".tmp").replace(log_path)
    record = {**pair, **parse_output(output), "workers": workers,
              "heap_size": args.heap, "timeout_seconds": args.timeout, "exit_code": code,
              "wall_time_seconds": elapsed, "peak_memory_mb": peak, "timeout": timed_out,
              "interrupted": interrupted, "start_time": start_time,
              "end_time": datetime.now(timezone.utc).isoformat(),
              "log": str(log_path.relative_to(args.output)),
              "command": tlc_command(redact(args.java), args.heap, redact(classpath), workers, display(cfg),
                                     (attempt / "states").relative_to(args.output), display(spec)),
              "inputs": {display(p): hashes.get(p) or digest(p.read_bytes()) for p in read if p.is_file()},
              "plan_sha256": digest(encoded(plan))}
    record["status"] = classify(record, args.timeout)
    atomic_json(attempt / "result.json", record)
    atomic_json(run_dir / "result.json", record)
    print(f"  {record['status']}: {elapsed:.3f}s, {record['distinct_states']} distinct states", flush=True)
    if interrupted:
        raise KeyboardInterrupt
    return record


CSV_FIELDS = ["name", "spec_file", "config_file", "workers", "status",
              "wall_time_seconds", "tlc_reported_time", "states_generated", "distinct_states",
              "states_in_queue", "depth", "peak_memory_mb", "heap_size", "timeout_seconds",
              "exit_code", "success", "timeout", "error_message", "log"]
# The columns of the earlier tlc-<N>-worker.csv tables, after the name of the pair
TABLE_FIELDS = ["name", "spec_file", "config_file", "workers", "heap_size", "wall_time_seconds",
                "tlc_reported_time", "states_generated", "distinct_states", "depth", "peak_memory_mb",
                "success", "timeout", "error_message"]


def all_results(output):
    """Every result recorded in --output, including those of earlier invocations."""
    records = [json.loads(path.read_text()) for path in output.glob("runs/*/w*/result.json")]
    return sorted(records, key=lambda r: (r["name"], r["workers"]))


def write_csv(path, records, fields=CSV_FIELDS):
    with path.with_suffix(".tmp").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(records)
    path.with_suffix(".tmp").replace(path)


def write_tables(output):
    """results.csv, and csv/tlc-<N>-worker.csv with the runs at N workers that TLC completed."""
    results = all_results(output)
    write_csv(output / "results.csv", results)
    (output / "csv").mkdir(exist_ok=True)
    for workers in sorted({r["workers"] for r in results}):
        write_csv(output / f"csv/tlc-{workers}-worker.csv",
                  [r for r in results if r["workers"] == workers and r["status"] in ("ok", "violation")],
                  TABLE_FIELDS)
    return results


def run_all(args, plan, classpath, pairs):
    runs = schedule(args, plan, pairs)
    print_schedule(runs)
    records = []
    for pair, workers, record, reason in runs:
        if reason:
            record = measure(pair, workers, args, plan, classpath)
            write_tables(args.output)
        records.append(record)
    results = write_tables(args.output)
    distinct = {}
    for record in results:
        if record["status"] == "ok":
            distinct.setdefault(record["name"], {})[record["workers"]] = record["distinct_states"]
    mismatches = {name: counts for name, counts in distinct.items() if len(set(counts.values())) > 1}
    summary = {"runs": len(runs), "measured": sum(1 for run in runs if run[3]),
               "statuses": dict(Counter(r["status"] for r in records)),
               "distinct_state_mismatches": mismatches}
    atomic_json(args.output / "summary.json", summary)
    print(json.dumps(summary, indent=2), flush=True)
    print(f"Results: {display(args.output / 'results.csv')}, and per worker count in "
          f"{display(args.output / 'csv')}", flush=True)
    # Timeouts and violations are results; checker errors and inconsistent state counts are not.
    return int(any(r["status"] == "error" for r in records) or bool(mismatches))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--pair", nargs="+", action="append", default=[], metavar=("SPEC CFG", "NAME"),
                        help="A .tla file and the .cfg to check it with (repeatable); NAME, by default the "
                             "stem of CFG, names its results")
    parser.add_argument("--workers", type=int, nargs="+", default=[], help="TLC worker counts; each pair runs with each")
    parser.add_argument("--output", type=Path, default=REPO / "benchmark-results/tlc",
                        help="Results directory (default: benchmark-results/tlc in the repository)")
    parser.add_argument("--tla2tools", type=Path, help="tla2tools.jar to run instead of the pinned one")
    parser.add_argument("--community-modules", type=Path,
                        help="CommunityModules-deps.jar to run instead of the pinned one")
    parser.add_argument("--java", default="java", help="Java command (default: java)")
    parser.add_argument("--heap", default="20G", help="Fixed Xms/Xmx for every measurement (default: 20G)")
    parser.add_argument("--timeout", type=float, default=36000, help="Per-run timeout in seconds (default: 36000)")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--dry-run", action="store_true", help="Only list the runs to measure and the results to reuse")
    mode.add_argument("--cleanup-states", action="store_true", help="Only remove this output's TLC state directories; preserve logs and results")
    mode.add_argument("--fetch-jars", action="store_true", help=f"Only download the pinned jars into {display(JAR_DIR)}")
    args = parser.parse_args()
    args.output = args.output.expanduser().resolve()
    for option in ("tla2tools", "community_modules"):
        path = getattr(args, option)
        if path is not None:
            setattr(args, option, path.expanduser().resolve())
            if not getattr(args, option).is_file():
                parser.error(f"--{option.replace('_', '-')}: no such file: {path}")
    if not (args.cleanup_states or args.fetch_jars or (args.pair and args.workers)):
        parser.error("Require at least one --pair and --workers")
    if psutil is None and not args.fetch_jars:
        parser.error(f"psutil is missing; install the requirements: python3 -m pip install -r {display(REQUIREMENTS)}")
    if any(w <= 0 for w in args.workers) or len(set(args.workers)) != len(args.workers):
        parser.error("--workers must contain distinct positive integers")
    if not 0 < args.timeout < float("inf") or not re.fullmatch(r"[1-9][0-9]*[MmGg]", args.heap):
        parser.error("Require a finite positive timeout and a positive M/G heap")
    try:
        pairs = parse_pairs(args.pair)
    except ValueError as exc:
        parser.error(str(exc))

    def terminate(signum, frame):
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, terminate)
    try:
        if args.fetch_jars:
            fetch_jars()
            print(f"The pinned jars are in {display(JAR_DIR)}.")
            return 0
        if not args.cleanup_states:
            jars_sha256 = jar_sha256(args)
            for name, path in given_jars(args).items():
                if path and jars_sha256[name] != JARS[name][0]:
                    print(f"Note: {display(path)} is not the pinned {name}; plan.json records its SHA-256.",
                          file=sys.stderr)
        if args.dry_run:
            print_schedule(schedule(args, prepare(args, jars_sha256), pairs))
            return 0
        args.output.mkdir(parents=True, exist_ok=True)
        with (args.output / ".lock").open("a") as lock:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                raise ValueError(f"Another process owns {display(args.output)}") from None
            if args.cleanup_states:
                cleanup_output_states(args.output)
                return 0
            plan = prepare(args, jars_sha256)
            classpath = os.pathsep.join(map(str, jar_paths(args).values()))
            atomic_json(args.output / "plan.json", plan)
            cleanup_output_states(args.output)
            return run_all(args, plan, classpath, pairs)
    except KeyboardInterrupt:
        print("Interrupted; finished results are retained. Repeat the same command to resume.", file=sys.stderr)
        return 130
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
