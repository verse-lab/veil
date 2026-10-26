#!/usr/bin/env python3
"""Build and time Veil model checkers on Linux or macOS.

Run from the checkout root; it runs `lake build Veil` first. Each spec is built without
running it, then benchmarked at the requested thread counts (1 = sequential, >1 = parallel).
A warm-up prepares native dependencies; measured builds discard cached build folders.

Results go to OUT/results.json, with logs in OUT/build and OUT/runs. At the end,
scripts/bench-model-check-report.py prints summaries and writes CSVs; it can be rerun on OUT
at any time. Timings separate build phases from search; elaboration time includes Lean
startup, imports and other commands in the file.

A checker that needs most of the machine's memory slows down when other programs' memory is in
the way: the kernel compresses or swaps out part of the checker's memory, and accessing it then
costs system time. Each run records how much memory was free when it started and, on macOS, its
peak footprint, which counts that memory too, unlike the maximum resident set size; the report
lists the runs whose footprint exceeds their RSS by 1 GB or more. By default nothing is done
about other programs' memory. On request, before each run: --free-memory GB holds that much
incompressible data for a moment, which pushes the file cache and idle programs' pages out of
memory (no root needed); --cooldown then pauses; and --min-free waits, for at most 5 minutes,
until enough memory is free.

Use --resume to continue a run (with its thread counts and repetitions, unless --threads or
--repeat give others), --rerun to run some of its specs, or their runs at some thread counts,
again, --bin-dir to keep binaries, and --clean-binaries to remove retained build artifacts
after confirmation. See --help for all options.

Examples:
  python3 scripts/bench-model-check.py Examples/TLA --threads 1,4,8 --repeat 3 --name tla
  python3 scripts/bench-model-check.py Examples/TLA --only EWD840 --dry-run
"""
from __future__ import annotations

import argparse
import ctypes
import fcntl
import hashlib
import json
import os
import pathlib
import platform
import re
import select
import shutil
import signal
import subprocess
import sys
import threading
import time

HERE = pathlib.Path(__file__).resolve().parent
REPORT_SCRIPT = HERE / "bench-model-check-report.py"
MB = 1024 * 1024
# The report `veil.modelChecker.buildOnly` logs for every `#model_check`: a JSON object with the
# binary's path (Veil's copy in .lake/model_checkers), its build folder and the phases of its build
# in milliseconds.
BUILD_ONLY_RE = re.compile(r"VEIL_BUILD_ONLY (\{.*\})")
MODEL_CHECK_RE = re.compile(r"(?m)^\s*#model_check\b|\bin\s+#model_check\b")
# Veil leaves its build folders and its copies of the binaries alone, and this script deletes them
# itself: by default, a build deletes those of earlier checks, e.g. of the same file.
LEAN_OPTIONS = ["-Dveil.modelChecker.buildOnly=true", "-Dveil.modelChecker.maxStoredBuilds=0",
                "-Dveil.modelChecker.maxStoredCheckers=0"]
# Written into --bin-dir; --clean-binaries only empties directories that carry it.
BIN_DIR_MARKER = ".bench-model-check-bin-dir"
# --free-memory holds at most this percentage of the machine's memory, and skips the later runs of a
# spec whose runs so far all peaked below FREE_MEMORY_MIN_MB.
FREE_MEMORY_MAX_PERCENT = 67
FREE_MEMORY_MIN_MB = 4096
# --min-free waits at most this many seconds, then runs anyway.
MIN_FREE_MAX_WAIT = 300
# Run as `python -c HOLD_MEMORY <bytes>` for --free-memory: random data, so that the compressor
# cannot shrink it, then every page written twice more, so that its pages stay active and the
# kernel makes room by evicting the file cache and other programs' pages instead. The memory goes
# back to the system when the process exits.
HOLD_MEMORY = """
import os, sys
n = int(sys.argv[1])
block = os.urandom(1 << 20)
buf = bytearray(n)
for i in range(0, n, len(block)):
    buf[i:i + len(block)] = block[:n - i]
for _ in range(2):
    for i in range(0, n, 4096):
        buf[i] ^= 1
"""


# --------------------------------------------------------------------------- processes

def kill_group(pid: int):
    """SIGKILL the process group `pid` leads (the process and whatever it spawned)."""
    try:
        os.killpg(pid, signal.SIGKILL)
    except ProcessLookupError:
        pass


class RusageInfoV4(ctypes.Structure):
    """`struct rusage_info_v4` of macOS's <sys/resource.h>: a UUID, then 35 counters, of which
    `ri_lifetime_max_phys_footprint` is the 29th."""
    _fields_ = [("uuid", ctypes.c_uint8 * 16), ("counters", ctypes.c_uint64 * 35)]


def wait_for_exit(pid: int):
    """Block until the child `pid` exits, without reaping it (macOS, kqueue), so that its usage can
    still be read. Returns at once if it has exited already."""
    kq = select.kqueue()
    try:
        kq.control([select.kevent(pid, select.KQ_FILTER_PROC, select.KQ_EV_ADD | select.KQ_EV_ONESHOT,
                                  select.KQ_NOTE_EXIT)], 1, None)
    finally:
        kq.close()


def peak_footprint_mb(pid: int):
    """The peak physical footprint in MB of the exited, not yet reaped child `pid` (macOS): unlike
    the maximum resident set size, it counts the memory that the kernel compressed or swapped out.
    None if it cannot be read."""
    try:
        proc_pid_rusage = ctypes.CDLL(None).proc_pid_rusage
    except (OSError, AttributeError):
        return None
    proc_pid_rusage.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.POINTER(RusageInfoV4)]
    info = RusageInfoV4()
    if proc_pid_rusage(pid, 4, ctypes.byref(info)) != 0:   # RUSAGE_INFO_V4
        return None
    return info.counters[28] / MB


def run_process(cmd, *, cwd, stdout_path, stderr_path=None, timeout=None):
    """Run `cmd` in its own process group, with stdin open (a checker binary exits as soon as its
    stdin reaches EOF), and wait for it with `wait4`, so that the measurements cover the process
    together with the children it waited for (for `lake lean`: `lean`, the C compiler, the linker).
    stderr goes to `stderr_path`, or to `stdout_path` when none is given. On timeout the whole
    group is killed. Returns a dict with the exit code, the wall, user and system seconds, the
    maximum resident set size in MB, the peak footprint in MB of the process itself (macOS; not of
    its children) and whether the run timed out."""
    t0 = time.perf_counter()
    with open(stdout_path, "wb") as fo:
        fe = open(stderr_path, "wb") if stderr_path else None
        try:
            proc = subprocess.Popen([str(c) for c in cmd], cwd=cwd, stdin=subprocess.PIPE, stdout=fo,
                                    stderr=fe if fe else subprocess.STDOUT, start_new_session=True)
        finally:
            if fe:
                fe.close()
        expired = threading.Event()

        def expire():
            expired.set()
            kill_group(proc.pid)

        timer = threading.Timer(timeout, expire) if timeout else None
        if timer:
            timer.start()
        footprint = None
        try:
            if sys.platform == "darwin":
                wait_for_exit(proc.pid)
                footprint = peak_footprint_mb(proc.pid)
            _, status, usage = os.wait4(proc.pid, 0)
        except BaseException:
            kill_group(proc.pid)
            raise
        finally:
            if timer:
                timer.cancel()
        wall = time.perf_counter() - t0
        if os.WIFEXITED(status):
            code = os.WEXITSTATUS(status)
        else:
            code = -os.WTERMSIG(status)
        proc.returncode = code       # already reaped by wait4
        if proc.stdin:
            proc.stdin.close()
    # ru_maxrss is in bytes on macOS and in kilobytes elsewhere.
    maxrss_mb = usage.ru_maxrss / MB if sys.platform == "darwin" else usage.ru_maxrss / 1024
    return {"exit_code": code, "timeout": expired.is_set(), "wall_seconds": round(wall, 3),
            "user_seconds": round(usage.ru_utime, 3), "system_seconds": round(usage.ru_stime, 3),
            "cpu_seconds": round(usage.ru_utime + usage.ru_stime, 3), "max_rss_mb": round(maxrss_mb, 1),
            "peak_footprint_mb": round(footprint, 1) if footprint is not None else None}


def command_output(cmd, cwd=None) -> str:
    try:
        return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True).stdout.strip()
    except OSError:
        return ""


# --------------------------------------------------------------------------- helpers

def sha1_of(text: str) -> str:
    return hashlib.sha1(text.encode()).hexdigest()[:12]


def sha1_file(path: pathlib.Path) -> str:
    h = hashlib.sha1()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()[:12]


def save_json(path: pathlib.Path, data):
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(data, indent=1))
    tmp.replace(path)


def parse_threads(text: str, option: str = "--threads"):
    threads = []
    for part in text.split(","):
        part = part.strip()
        if not part:
            continue
        if not part.isdigit() or int(part) < 1:
            sys.exit(f"{option}: expected positive integers separated by commas, got {text!r}")
        if int(part) not in threads:
            threads.append(int(part))
    if not threads:
        sys.exit(f"{option}: no thread count given")
    return threads


def thread_argv(threads: int, threshold: int, sub_steps: int):
    """Arguments of `ModelCheckerMain`: none for the sequential search, else
    `numSubTasks thresholdToParallel numSubSteps`."""
    return [] if threads == 1 else [str(threads), str(threshold), str(sub_steps)]


def first_error(text: str, limit: int = 2000) -> str:
    """The first Lean error of a log with some context, or its tail."""
    lines = text.splitlines()
    starts = [i for i, line in enumerate(lines) if ": error:" in line or line.startswith("error:")]
    if not starts:
        return text[-limit:].strip()
    return "\n".join(lines[starts[0]:starts[0] + 20])[:limit]


def checkout_info(root: pathlib.Path) -> dict:
    def git(*args):
        return command_output(["git", "-C", str(root), *args])
    packages = {}
    manifest = root / "lake-manifest.json"
    if manifest.exists():
        try:
            packages = {p.get("name"): p.get("rev") for p in json.loads(manifest.read_text()).get("packages", [])}
        except (ValueError, AttributeError):
            pass
    toolchain = root / "lean-toolchain"
    return {"dir": str(root), "head": git("rev-parse", "HEAD"), "branch": git("rev-parse", "--abbrev-ref", "HEAD"),
            "subject": git("log", "-1", "--format=%s"), "status": git("status", "--short", "--untracked-files=no"),
            "toolchain": toolchain.read_text().strip() if toolchain.exists() else None, "packages": packages}


def host_info() -> dict:
    memory, cpu = None, None
    if platform.system() == "Darwin":
        text = command_output(["sysctl", "-n", "hw.memsize"])
        memory = int(text) if text.isdigit() else None
        cpu = command_output(["sysctl", "-n", "machdep.cpu.brand_string"]) or None
    elif pathlib.Path("/proc/meminfo").exists():
        match = re.search(r"MemTotal:\s+(\d+) kB", pathlib.Path("/proc/meminfo").read_text())
        memory = int(match.group(1)) * 1024 if match else None
        match = re.search(r"model name\s*:\s*(.+)", pathlib.Path("/proc/cpuinfo").read_text(errors="replace"))
        cpu = match.group(1).strip() if match else None
    return {"host": platform.node(), "platform": platform.platform(), "machine": platform.machine(),
            "cpu": cpu or platform.processor() or None, "cpus": os.cpu_count(), "memory_bytes": memory,
            "python": platform.python_version()}


def model_check_entries(base: pathlib.Path, source: pathlib.Path):
    """The entries of `base` that Veil named after a `#model_check` of `source` inside a module,
    `<stem>_model_check_<hash>`; not those of `#model_check X …` for a module `X`,
    `<stem>_model_check_build_<hash>`, which this script does not build."""
    if not base.is_dir():
        return []
    name = re.compile(re.escape(source.stem) + r"_model_check_\d+")
    return [p for p in base.iterdir() if name.fullmatch(p.name)]


def build_folders(root: pathlib.Path, source: pathlib.Path):
    """Veil's build folders of `source`: `.lake/model_checker_builds/<stem>_model_check_<hash>`."""
    return [p for p in model_check_entries(root / ".lake" / "model_checker_builds", source) if p.is_dir()]


def checker_copies(root: pathlib.Path, source: pathlib.Path):
    """Veil's copies of the binaries of `source`, named after their build folders:
    `.lake/model_checkers/<stem>_model_check_<hash>`."""
    return [p for p in model_check_entries(root / ".lake" / "model_checkers", source) if p.is_file()]


def drop_builds(root: pathlib.Path, source: pathlib.Path):
    """Delete Veil's build folders of `source` and its copies of their binaries."""
    for folder in build_folders(root, source):
        shutil.rmtree(folder, ignore_errors=True)
    for copy in checker_copies(root, source):
        copy.unlink(missing_ok=True)


# --------------------------------------------------------------------------- cleaning

def tree_size(path: pathlib.Path) -> int:
    if path.is_file():
        return path.stat().st_size
    return sum(f.stat().st_size for f in path.rglob("*") if f.is_file())


def try_lock(path: pathlib.Path):
    """An exclusive, non-blocking lock on `path` (created if needed), or None if it is held."""
    fd = os.open(path, os.O_WRONLY | os.O_CREAT, 0o644)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        os.close(fd)
        return None
    return fd


def clean_binaries(root: pathlib.Path, bin_dir, assume_yes: bool):
    """Delete the binaries in `bin_dir` (a directory this script populated), every build folder
    in .lake/model_checker_builds that no running check uses and the copies that
    `veil.modelChecker.buildOnly` made in .lake/model_checkers, after listing them and asking. As
    Veil's own pruning does, this holds the build lock and skips folders whose use lock is held."""
    targets = []
    if bin_dir:
        if not bin_dir.is_dir():
            sys.exit(f"{bin_dir} is not a directory")
        if not (bin_dir / BIN_DIR_MARKER).exists():
            sys.exit(f"{bin_dir} was not populated by this script (no {BIN_DIR_MARKER} file in it); not touching it")
        targets += [(p, tree_size(p)) for p in sorted(bin_dir.iterdir()) if p.is_file() and p.name != BIN_DIR_MARKER]
    base = root / ".lake" / "model_checker_builds"
    build_lock = None
    if base.is_dir():
        build_lock = try_lock(base / "build.lock")
        if build_lock is None:
            sys.exit(f"a model-checker build is running ({base / 'build.lock'} is held); try again later")
        for folder in sorted(p for p in base.iterdir() if p.is_dir()):
            use_lock = try_lock(folder / "use.lock")
            if use_lock is None:
                print(f"skipping {folder}: a running check uses it", flush=True)
                continue
            os.close(use_lock)
            targets.append((folder, tree_size(folder)))
    copies = root / ".lake" / "model_checkers"
    if copies.is_dir():
        # Named after their build folders. Those of `#model_check X …`, `<stem>_model_check_build_<hash>`,
        # are the editor's.
        targets += [(p, tree_size(p)) for p in sorted(copies.iterdir())
                    if p.is_file() and re.fullmatch(r".+_model_check_\d+", p.name)]
    try:
        if not targets:
            print("nothing to delete")
            return
        total = 0
        for path, size in targets:
            total += size
            print(f"{size / MB:10.1f} MB  {path}")
        print(f"{total / MB:10.1f} MB  in {len(targets)} items")
        if not assume_yes:
            if not sys.stdin.isatty():
                sys.exit("nothing deleted: confirmation needed, but stdin is not a terminal (pass --yes to skip it)")
            if input(f"Delete these {len(targets)} items? [y/N] ").strip().lower() not in ("y", "yes"):
                print("nothing deleted")
                return
        for path, _ in targets:
            if path.is_dir():
                shutil.rmtree(path, ignore_errors=True)
            else:
                path.unlink()
        print(f"deleted {len(targets)} items ({total / MB:.1f} MB)")
    finally:
        if build_lock is not None:
            os.close(build_lock)


# --------------------------------------------------------------------------- specs

def collect_specs(root: pathlib.Path, paths, only):
    """(name, path relative to `root`) of the selected specs, in order. A spec is named after its
    file; files with the same name are told apart by their path."""
    files = []
    for arg in paths:
        path = pathlib.Path(arg)
        if path.is_dir():
            found = sorted(p for p in path.rglob("*.lean")
                           if not any(part.startswith(".") for part in p.relative_to(path).parts))
            if not found:
                print(f"warning: no .lean files under {path}", flush=True)
            files += found
        elif path.is_file() and path.suffix == ".lean":
            files.append(path)
        else:
            sys.exit(f"{arg}: not a directory or a .lean file")
    seen, specs = set(), []
    for path in files:
        resolved = path.resolve()
        if resolved in seen:
            continue
        seen.add(resolved)
        try:
            rel = resolved.relative_to(root)
        except ValueError:
            sys.exit(f"{path} is outside the Veil checkout {root}")
        specs.append(rel)
    stems = {}
    for rel in specs:
        stems.setdefault(rel.stem, []).append(rel)
    named = []
    for rel in specs:
        name = rel.stem if len(stems[rel.stem]) == 1 else rel.with_suffix("").as_posix().replace("/", ".")
        named.append((name, rel))
    if only:
        wanted = set(only)
        missing = wanted - {name for name, _ in named}
        if missing:
            sys.exit(f"--only: no such spec among the selected files: {sorted(missing)}")
        named = [(name, rel) for name, rel in named if name in wanted]
    return named


def check_root(root: pathlib.Path):
    lakefile = root / "lakefile.lean"
    if not lakefile.exists() or "veilModelCheckBuild" not in lakefile.read_text(errors="replace"):
        sys.exit(f"{root} is not a Veil checkout (no lakefile.lean with the veilModelCheckBuild script); "
                 "run this script from the root of the checkout")
    if shutil.which("lake") is None:
        sys.exit("`lake` is not on PATH (install Lean with elan, or add ~/.elan/bin to PATH)")


# --------------------------------------------------------------------------- build

def build_spec(root: pathlib.Path, out: pathlib.Path, name: str, rel: pathlib.Path, timeout) -> list:
    """Elaborate `rel` with `veil.modelChecker.buildOnly`. Returns one entry per `#model_check`
    of the file (named `name`, `name@2`, ...); its `status` is `ok` when the file elaborated and
    the command reported a binary."""
    source = root / rel
    text = source.read_text(errors="replace")
    base = {"source": rel.as_posix(), "spec_sha1": sha1_of(text), "runs": [], "complete": False,
            "date": time.strftime("%Y-%m-%d %H:%M:%S")}
    first = text.lstrip().split("\n", 1)[0].strip()
    if not MODEL_CHECK_RE.search(text):
        return [{**base, "name": name, "status": "no_model_check",
                 "error_message": "the file has no #model_check command"}]
    if first != "module":
        return [{**base, "name": name, "status": "not_module",
                 "error_message": "compiled checks need Lean's module system: the file must start with `module`"}]
    drop_builds(root, source)    # never reuse a cached build
    log = out / "build" / f"{name}.log"
    # `lake lean` (not `lake env lean`): it runs `lean` with the workspace's module setup, which
    # loads the native libraries that commands such as `#check_invariants` need (cvc5).
    measured = run_process(["lake", "lean", rel.as_posix(), "--", *LEAN_OPTIONS], cwd=root, stdout_path=log,
                           timeout=timeout)
    output = log.read_text(errors="replace")
    reports = []
    for match in BUILD_ONLY_RE.finditer(output):
        try:
            reports.append(json.loads(match.group(1)))
        except ValueError:
            pass
    build = {"log": log.relative_to(out).as_posix(), "total_seconds": measured["wall_seconds"],
             "exit_code": measured["exit_code"], "timeout": measured["timeout"],
             "cpu_seconds": measured["cpu_seconds"], "max_rss_mb": measured["max_rss_mb"]}
    if measured["timeout"]:
        return [{**base, "name": name, "status": "build_timeout", "build": build,
                 "error_message": f"elaboration and build did not finish within {timeout}s"}]
    if measured["exit_code"] != 0:
        return [{**base, "name": name, "status": "build_failed", "build": build,
                 "error_message": first_error(output) or f"lean exited with code {measured['exit_code']}"}]
    if not reports:
        return [{**base, "name": name, "status": "no_model_check", "build": build,
                 "error_message": "no #model_check reported a binary (is it commented out, or inside #guard_msgs?)"}]
    compile_ms = sum(r.get("extract_ms", 0) + r.get("emit_c_ms", 0) + r.get("cc_link_ms", 0) for r in reports)
    entries = []
    for i, report in enumerate(reports, 1):
        binary = pathlib.Path(report["binary"])
        build_folder = pathlib.Path(report["build_folder"])
        entry_name = name if i == 1 else f"{name}@{i}"
        extract_s = report.get("extract_ms", 0) / 1000
        emit_c_s = report.get("emit_c_ms", 0) / 1000
        cc_link_s = report.get("cc_link_ms", 0) / 1000
        entry_build: dict = {
            **build, "extract_seconds": extract_s, "emit_c_seconds": emit_c_s, "cc_link_seconds": cc_link_s,
            "compile_seconds": round(extract_s + emit_c_s + cc_link_s, 3), "c_bytes": report.get("c_bytes"),
            # Elaboration of the spec itself: everything the process did outside the phases of its
            # `#model_check` builds (shared by the entries of one file).
            "elab_seconds": round(measured["wall_seconds"] - compile_ms / 1000, 3),
            # The folder is named after the emitted C and the imported modules, so its name
            # identifies the program that was built.
            "build_folder": str(build_folder), "build_id": build_folder.name, "built_binary": str(binary)}
        if binary.exists():
            entry_build["binary_bytes"] = binary.stat().st_size
            entries.append({**base, "name": entry_name, "status": "ok", "build": entry_build, "error_message": ""})
        else:
            entries.append({**base, "name": entry_name, "status": "build_failed", "build": entry_build,
                            "error_message": f"the reported binary {binary} does not exist"})
    return entries


def lake_build(root: pathlib.Path, out: pathlib.Path, timeout):
    print("lake build Veil ...", flush=True)
    log = out / "build" / "lake-build-Veil.log"
    measured = run_process(["lake", "build", "Veil"], cwd=root, stdout_path=log, timeout=timeout)
    if measured["exit_code"] != 0:
        sys.exit(f"`lake build Veil` failed (exit code {measured['exit_code']}"
                 f"{', timeout' if measured['timeout'] else ''}); see {log}")
    print(f"  done in {measured['wall_seconds']:.1f}s", flush=True)


def warmup_build(root: pathlib.Path, out: pathlib.Path, specs, timeout):
    """Build the smallest spec once, to compile the native code of the imported modules."""
    _, rel = min(specs, key=lambda s: (root / s[1]).stat().st_size)
    print(f"warm-up build ({rel.as_posix()}) ...", flush=True)
    entries = build_spec(root, out, "_warmup", rel, timeout)
    drop_builds(root, root / rel)
    entry = entries[0]
    if entry["status"] == "ok":
        print(f"  done in {entry['build']['total_seconds']:.1f}s", flush=True)
    else:
        print(f"  {entry['status']}: {entry['error_message'].splitlines()[0] if entry['error_message'] else ''}"
              f" (see {out / 'build' / '_warmup.log'})", flush=True)


# --------------------------------------------------------------------------- memory

def free_memory_percent():
    """Free memory in percent of the machine's: `memory_pressure`'s free percentage on macOS,
    MemAvailable on Linux; None if unknown."""
    if platform.system() == "Darwin":
        match = re.search(r"free percentage:\s*(\d+)%", command_output(["memory_pressure", "-Q"]))
        return int(match.group(1)) if match else None
    meminfo = pathlib.Path("/proc/meminfo")
    if meminfo.exists():
        text = meminfo.read_text()
        total = re.search(r"MemTotal:\s+(\d+) kB", text)
        available = re.search(r"MemAvailable:\s+(\d+) kB", text)
        if total and available:
            return round(100 * int(available.group(1)) / int(total.group(1)))
    return None


def needs_free_memory(runs) -> bool:
    """Whether --free-memory applies before the next run of a spec that has these runs: unless
    they all peaked below FREE_MEMORY_MIN_MB, as a small spec's first run shows."""
    return not runs or max(r.get("max_rss_mb") or 0 for r in runs) >= FREE_MEMORY_MIN_MB


def free_memory(gb: float) -> bool:
    """Hold `gb` GB of incompressible data for a moment (HOLD_MEMORY, in a process of its own),
    which pushes the file cache and idle programs' pages out of memory. Returns whether it did."""
    t0 = time.perf_counter()
    code = subprocess.run([sys.executable, "-c", HOLD_MEMORY, str(int(gb * 2**30))]).returncode
    if code:
        print(f"  warning: holding {gb:g} GB failed (exit code {code})", flush=True)
    else:
        print(f"  held {gb:g} GB for {time.perf_counter() - t0:.1f}s to free memory", flush=True)
    return code == 0


def wait_for_memory(min_free: int) -> float:
    """Wait until at least `min_free` percent of the memory is free (free_memory_percent), checking
    every 5 seconds for at most MIN_FREE_MAX_WAIT seconds. Returns the seconds waited."""
    t0 = time.perf_counter()
    free = free_memory_percent()
    while free is not None and free < min_free:
        left = MIN_FREE_MAX_WAIT - (time.perf_counter() - t0)
        if left <= 0:
            break
        time.sleep(min(5, left))
        free = free_memory_percent()
    waited = time.perf_counter() - t0
    if free is not None and free < min_free:
        print(f"  {free}% of memory free after waiting {waited:.0f}s for {min_free}%; running anyway", flush=True)
    elif waited >= 1:
        print(f"  waited {waited:.0f}s for {min_free}% of memory to be free", flush=True)
    return waited


def page_in(binary: pathlib.Path):
    """Launch `binary` with stdin closed: the checker exits at once, so this costs no search, but
    its pages are read in, and on macOS the first launch of a new binary is checked, before it is
    timed."""
    subprocess.run([str(binary)], stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


# --------------------------------------------------------------------------- run

def tail_text(path: pathlib.Path, max_bytes: int = 4 * MB) -> str:
    with open(path, "rb") as f:
        f.seek(0, os.SEEK_END)
        size = f.tell()
        f.seek(max(0, size - max_bytes))
        return f.read().decode(errors="replace")


def parse_checker_output(stdout_path: pathlib.Path, stderr_path: pathlib.Path):
    """The result JSON the binary prints on stdout, and the counters of the last progress line it
    printed on stderr (`Veil.ModelChecker.Concrete.Progress`, with `ModelCheckProgress` details)."""
    final = None
    text = stdout_path.read_text(errors="replace") if stdout_path.exists() else ""
    try:
        final = json.loads(text)
    except ValueError:
        for line in reversed(text.strip().splitlines()):
            try:
                final = json.loads(line)
                break
            except ValueError:
                continue
    progress = None
    for line in reversed(tail_text(stderr_path).splitlines() if stderr_path.exists() else []):
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            p = json.loads(line)
        except ValueError:
            continue
        details = p.get("details") if isinstance(p, dict) else None
        metrics = details.get("modelCheck") if isinstance(details, dict) else None
        if isinstance(metrics, dict) and isinstance(metrics.get("metrics"), dict):
            metrics = metrics["metrics"]
        if isinstance(metrics, dict):
            progress = {"checker_elapsed_ms": p.get("elapsedMs"), "diameter": metrics.get("diameter"),
                        "states_generated": metrics.get("statesFound"), "distinct_states": metrics.get("distinctStates")}
            break
    return final, progress


def summarize_result(final) -> dict:
    """Verdict fields of a checker result (`Veil.ModelChecker.ModelCheckingResult`)."""
    if not isinstance(final, dict):
        return {"result": None, "termination": None, "violation": None, "explored_states": None}
    reason = final.get("termination_reason")
    termination = None
    if isinstance(reason, dict):
        termination = reason.get("kind")
        condition = reason.get("condition")
        if isinstance(condition, dict) and condition.get("kind"):
            termination = f"{termination}:{condition['kind']}"
    violation = None
    if isinstance(final.get("violation"), dict):
        v = final["violation"]
        violation = v.get("kind")
        if v.get("violates"):
            violation += f" ({', '.join(map(str, v['violates']))})"
    return {"result": final.get("result"), "termination": termination, "violation": violation,
            "explored_states": final.get("explored_states")}


def prepare_run(binary: pathlib.Path, runs, free_memory_gb: float, cooldown: float, min_free: int) -> dict:
    """What precedes a run of `binary`, given the spec's runs so far: holding `free_memory_gb`
    (--free-memory) where needs_free_memory says so, pausing `cooldown` seconds, waiting for
    `min_free` percent of free memory (--min-free), and page_in. Returns the fields that the run
    records about it."""
    held = free_memory_gb if free_memory_gb and needs_free_memory(runs) else 0
    if held and not free_memory(held):
        held = 0
    time.sleep(cooldown)
    waited = wait_for_memory(min_free) if min_free else 0
    page_in(binary)
    return {"memory_held_gb": held, "memory_wait_seconds": round(waited, 1),
            "memory_free_percent": free_memory_percent()}


def run_binary(binary: pathlib.Path, argv, run_dir: pathlib.Path, threads: int, rep: int, timeout) -> dict:
    stdout_path, stderr_path = run_dir / f"t{threads}-r{rep}.stdout", run_dir / f"t{threads}-r{rep}.stderr"
    measured = run_process([binary, *argv], cwd=run_dir, stdout_path=stdout_path, stderr_path=stderr_path,
                           timeout=timeout)
    final, progress = parse_checker_output(stdout_path, stderr_path)
    summary = summarize_result(final)
    error = ""
    if measured["timeout"]:
        error = f"timeout after {timeout}s"
    elif measured["exit_code"] != 0:
        error = f"exit code {measured['exit_code']}: " + tail_text(stderr_path, 2000).strip()[-500:]
    elif not isinstance(final, dict):
        error = "no result JSON on stdout: " + stdout_path.read_text(errors="replace")[-300:].strip()
    elif "error" in final:
        error = str(final["error"])[:500]
    elif summary["result"] == "cancelled":
        error = "the checker reported `cancelled`"
    return {"threads": threads, "rep": rep, "argv": argv, "date": time.strftime("%Y-%m-%d %H:%M:%S"),
            **measured, "success": not error, "error_message": error, **summary,
            **(progress or {"checker_elapsed_ms": None, "diameter": None, "states_generated": None,
                            "distinct_states": None}),
            "stdout": stdout_path.relative_to(run_dir.parent.parent).as_posix(),
            "stderr": stderr_path.relative_to(run_dir.parent.parent).as_posix()}


def reusable_build(root: pathlib.Path, rel: pathlib.Path, previous, specs: dict):
    """When a `--resume` session finds a spec built but not complete: its entry, provided its
    binary is still there, unchanged, and the spec did not change; the runs then continue with
    that binary instead of rebuilding it. A file with several checks is rebuilt as a whole."""
    if not previous or previous.get("status") != "ok":
        return None
    if f"{previous.get('name')}@2" in specs:
        return None
    if previous.get("spec_sha1") != sha1_of((root / rel).read_text(errors="replace")):
        return None
    b = previous.get("build", {})
    binary = pathlib.Path(b.get("binary") or "")
    if not b.get("binary") or not binary.is_file() or sha1_file(binary) != b.get("binary_sha1"):
        return None
    return previous


def runs_missing(entry: dict, threads_list, repeat: int) -> bool:
    """Whether a spec of an earlier session still has runs to do at these settings. A thread
    count at which a run timed out is done."""
    if entry.get("status") != "ok":
        return False
    recorded = {(r["threads"], r["rep"]) for r in entry.get("runs", [])}
    timed_out = {r["threads"] for r in entry.get("runs", []) if r.get("timeout")}
    return any((t, k) not in recorded for t in threads_list if t not in timed_out for k in range(1, repeat + 1))


def carried_runs(entry: dict, old, session_head, head) -> list:
    """The runs an earlier session recorded for a spec that was just rebuilt, when they were of
    the same program: same spec, same emitted C and imports (the build folder's name) and the
    same Veil commit as when the session started."""
    if not old or old.get("status") != "ok" or not old.get("runs"):
        return []
    if old.get("spec_sha1") != entry["spec_sha1"] or old.get("build", {}).get("build_id") != entry["build"].get("build_id"):
        return []
    if not head or head != session_head:
        return []
    return old["runs"]


def parse_rerun(items, threads_list, names):
    """--rerun's SPEC and SPEC:T1,T2 as {spec: thread counts}, SPEC alone standing for all of
    `threads_list`, and the specs given alone, which are built again. `names` are the selected
    specs."""
    rerun, rebuild = {}, set()
    for item in items or []:
        name, sep, text = item.partition(":")
        if name not in names:
            sys.exit(f"--rerun: {item}: {name!r} is not one of the selected specs")
        threads = parse_threads(text, "--rerun") if sep else threads_list
        missing = [t for t in threads if t not in threads_list]
        if missing:
            sys.exit(f"--rerun: {item}: thread counts {missing} are not among --threads {threads_list}")
        if not sep:
            rebuild.add(name)
        rerun[name] = rerun.get(name, set()) | set(threads)
    return rerun, rebuild


def set_aside_runs(out: pathlib.Path, specs: dict, rerun: dict, repeat: int):
    """For --rerun: move the recorded runs that it makes again (at its thread counts, repetitions 1
    to `repeat`) from the runs of each spec, and of the other checks of its file (`name@2`, ...),
    to their replaced_runs, and their logs to runs/<check>/replaced-<time>/, so that the session
    runs them again."""
    date, stamp = time.strftime("%Y-%m-%d %H:%M:%S"), time.strftime("%Y%m%d-%H%M%S")
    for name, threads in rerun.items():
        for check, entry in specs.items():
            if check != name and not re.fullmatch(re.escape(name) + r"@\d+", check):
                continue
            keep, replaced = [], []
            for r in entry.get("runs", []):
                (replaced if r["threads"] in threads and r["rep"] <= repeat else keep).append(r)
            folder = out / "runs" / check / f"replaced-{stamp}"
            for r in replaced:
                r["replaced_on"] = date
                for key in ("stdout", "stderr"):
                    log = out / r[key] if r.get(key) else None
                    if log and log.is_file():
                        folder.mkdir(parents=True, exist_ok=True)
                        log.replace(folder / log.name)
                        r[key] = (folder / log.name).relative_to(out).as_posix()
                    else:
                        r[key] = None
            entry["runs"] = keep
            entry["replaced_runs"] = entry.get("replaced_runs", []) + replaced
            entry["complete"] = False
            print(f"--rerun {check}: setting aside its {len(replaced)} recorded run(s) at t={sorted(threads)}"
                  + (f" (logs moved to {folder.relative_to(out)})" if replaced else ""), flush=True)


def describe_run(r: dict) -> str:
    status = "TIMEOUT " if r["timeout"] else ("" if r["success"] else "FAILED ")
    counts = (f"{r['distinct_states']} distinct, {r['states_generated']} generated, diameter {r['diameter']}"
              if r.get("distinct_states") is not None else "no progress counts")
    footprint = f", footprint {r['peak_footprint_mb']:.0f} MB" if r.get("peak_footprint_mb") is not None else ""
    text = (f"{status}wall {r['wall_seconds']:.2f}s, CPU {r['cpu_seconds']:.2f}s, RSS {r['max_rss_mb']:.0f} MB"
            f"{footprint}, {counts}, {r['result'] or '-'}")
    if r["error_message"]:
        text += f": {r['error_message'][:200]}"
    return text


# --------------------------------------------------------------------------- main

def parse_args():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("paths", nargs="*", help="directories (searched recursively) or .lean files, relative to the checkout")
    ap.add_argument("--name", help="name of the run, recorded in the results (default: the output directory's name)")
    ap.add_argument("--out", default=None,
                    help="output directory (default: benchmark-results/<name>, or benchmark-results/<date> without --name)")
    ap.add_argument("--only", nargs="+", metavar="SPEC", help="only these specs (file names without .lean)")
    ap.add_argument("--threads", default=None,
                    help="comma-separated thread counts (default 1, or the session's with --resume)")
    ap.add_argument("--threshold", type=int, default=20,
                    help="thresholdToParallel of the parallel search, for more than one thread (default 20)")
    ap.add_argument("--sub-steps", type=int, default=1, help="numSubSteps of the parallel search (default 1)")
    ap.add_argument("-r", "--repeat", type=int, default=None,
                    help="runs per spec and thread count (default 1, or the session's with --resume)")
    ap.add_argument("--free-memory", type=float, default=0, metavar="GB",
                    help="before a run, hold this much incompressible data for a moment, which pushes the file cache "
                         f"and idle programs' pages out of memory; at most {FREE_MEMORY_MAX_PERCENT}%% of the "
                         "machine's memory, and not before the later runs of a spec that peaked below "
                         f"{FREE_MEMORY_MIN_MB // 1024} GB (default 0, none)")
    ap.add_argument("--cooldown", type=float, default=0, metavar="SECONDS",
                    help="pause before a run, after --free-memory (default 0)")
    ap.add_argument("--min-free", type=int, default=0, metavar="PERCENT",
                    help="before a run, after --cooldown, wait until at least this much of the memory is free "
                         "(memory_pressure's free percentage on macOS, MemAvailable on Linux), for at most "
                         f"{MIN_FREE_MAX_WAIT} seconds, then run anyway (default 0, no wait)")
    ap.add_argument("--bin-dir", help="copy every binary here, under the spec's name, and time that copy")
    ap.add_argument("--keep-build-folders", action="store_true",
                    help="keep the build folders in .lake/model_checker_builds, and Veil's copies of their "
                         "binaries in .lake/model_checkers, after the runs")
    ap.add_argument("--build-timeout", type=int, default=1800, help="per file, seconds; 0 = none (default 1800)")
    ap.add_argument("--run-timeout", type=int, default=3600, help="per run, seconds; 0 = none (default 3600)")
    ap.add_argument("--lake-timeout", type=int, default=7200, help="for `lake build Veil`, seconds (default 7200)")
    ap.add_argument("--skip-lake-build", action="store_true", help="do not run `lake build Veil` first")
    ap.add_argument("--no-warmup", action="store_true", help="skip the warm-up build")
    ap.add_argument("--resume", action="store_true",
                    help="continue an interrupted session in --out, doing only the runs it misses (including those "
                         "that a larger --repeat or new --threads add); a spec that is rebuilt keeps its earlier "
                         "runs if its program did not change (same spec, emitted C, imports and Veil commit)")
    ap.add_argument("--rerun", nargs="+", metavar="SPEC[:THREADS]",
                    help="run these again in the session in --out (implies --resume): SPEC, all its runs, after "
                         "building it again; SPEC:T1,T2, its runs at those thread counts. The runs they replace are "
                         "kept in results.json as replaced_runs, with their logs in runs/<spec>/replaced-<time>/")
    ap.add_argument("--dry-run", action="store_true", help="list the selected specs and exit")
    ap.add_argument("--clean-binaries", action="store_true",
                    help="delete the kept binaries (in --bin-dir, the build folders in .lake/model_checker_builds "
                         "and the copies of `veil.modelChecker.buildOnly` in .lake/model_checkers) after listing "
                         "them and asking for confirmation, then exit")
    ap.add_argument("--yes", action="store_true", help="with --clean-binaries: do not ask for confirmation")
    args = ap.parse_args()
    if not args.paths and not args.clean_binaries:
        ap.error("paths are required (directories or .lean files)")
    if args.repeat is not None and args.repeat < 1:
        ap.error("--repeat must be at least 1")
    if args.threshold < 0 or args.sub_steps < 1:
        ap.error("--threshold must be non-negative and --sub-steps at least 1")
    if args.free_memory < 0 or args.cooldown < 0:
        ap.error("--free-memory and --cooldown must be non-negative")
    if not 0 <= args.min_free <= 100:
        ap.error("--min-free must be a percentage, from 0 to 100")
    if args.threads is not None:
        args.threads = parse_threads(args.threads)
    return args


def main():
    args = parse_args()
    root = pathlib.Path.cwd()
    check_root(root)
    if args.clean_binaries:
        clean_binaries(root, pathlib.Path(args.bin_dir).resolve() if args.bin_dir else None, args.yes)
        return
    specs = collect_specs(root, args.paths, args.only)
    if not specs:
        sys.exit("no specs selected")
    if args.dry_run:
        for name, rel in specs:
            print(f"{name:30s} {rel.as_posix()}")
        print(f"{len(specs)} specs; threads {args.threads or [1]}, threshold {args.threshold}, "
              f"{args.repeat or 1} run(s) each")
        return
    out = pathlib.Path(args.out or f"benchmark-results/{args.name or time.strftime('%Y%m%d-%H%M%S')}").resolve()
    name = args.name or out.name
    results_path = out / "results.json"
    if args.rerun:
        if not results_path.exists():
            sys.exit(f"--rerun: there is no session in {out} to run again (no results.json)")
        args.resume = True
    if results_path.exists() and not args.resume:
        sys.exit(f"{results_path} exists; use --resume to continue that session, or another --out")
    results = json.loads(results_path.read_text()) if results_path.exists() else {"specs": {}}
    # Unless given, a resumed session keeps its thread counts and repetitions
    session = results.get("meta") if args.resume else None
    if args.threads is None:
        args.threads = list(session.get("threads") or [1]) if session else [1]
    if args.repeat is None:
        args.repeat = (session.get("repeat") or 1) if session else 1
    rerun, rebuild = parse_rerun(args.rerun, args.threads, {spec for spec, _ in specs})
    for d in ("build", "runs"):
        (out / d).mkdir(parents=True, exist_ok=True)
    bin_dir = pathlib.Path(args.bin_dir).resolve() if args.bin_dir else None
    if bin_dir:
        bin_dir.mkdir(parents=True, exist_ok=True)
        (bin_dir / BIN_DIR_MARKER).write_text("Binaries copied by scripts/bench-model-check.py; "
                                              "`--clean-binaries --bin-dir <this directory>` deletes them.\n")
    host = host_info()
    if args.free_memory and host["memory_bytes"]:
        most = round(FREE_MEMORY_MAX_PERCENT / 100 * host["memory_bytes"] / 2**30, 1)
        if args.free_memory > most:
            print(f"note: --free-memory {args.free_memory:g} is more than {FREE_MEMORY_MAX_PERCENT}% of this "
                  f"machine's memory; holding {most:g} GB", flush=True)
            args.free_memory = most
    meta = {"name": name, "command": sys.argv, "date": time.strftime("%Y-%m-%d %H:%M:%S"), "out": str(out),
            "threads": args.threads, "threshold": args.threshold, "sub_steps": args.sub_steps,
            "repeat": args.repeat, "run_timeout": args.run_timeout, "build_timeout": args.build_timeout,
            "bin_dir": str(bin_dir) if bin_dir else None, "free_memory_gb": args.free_memory,
            "cooldown_seconds": args.cooldown, "min_free_percent": args.min_free,
            "lean_options": LEAN_OPTIONS, "veil": checkout_info(root), **host}
    if meta["veil"]["status"]:
        print(f"note: the checkout has uncommitted changes:\n{meta['veil']['status']}", flush=True)
    if args.resume and results.get("meta"):
        # A resumed session keeps the settings it was started with; only record the resume.
        previous = results["meta"]
        for key in ("threshold", "sub_steps", "run_timeout"):
            if previous.get(key) != meta[key]:
                print(f"warning: --resume with a different {key} ({meta[key]}) than the session's "
                      f"({previous.get(key)}); the runs recorded earlier were made with the session's", flush=True)
        # More thread counts or repetitions extend the session: the missing runs are added.
        old_threads, old_repeat = list(previous.get("threads") or []), previous.get("repeat") or 0
        new_threads = old_threads + [t for t in args.threads if t not in old_threads]
        if new_threads != old_threads or args.repeat > old_repeat:
            print(f"extending the session: threads {old_threads} -> {new_threads}, "
                  f"repeat {old_repeat} -> {max(old_repeat, args.repeat)}", flush=True)
        previous["threads"], previous["repeat"] = new_threads, max(old_repeat, args.repeat)
        if previous.get("veil", {}).get("head") != meta["veil"]["head"]:
            print(f"warning: the checkout is at {meta['veil']['head'][:8]}, the session was started at "
                  f"{(previous.get('veil', {}).get('head') or '?')[:8]}", flush=True)
        previous.setdefault("resumed", []).append(
            {"command": sys.argv, "date": meta["date"],
             **{key: meta[key] for key in ("free_memory_gb", "cooldown_seconds", "min_free_percent")}})
    else:
        results["meta"] = meta
    save_json(results_path, results)
    print(f"run {results['meta'].get('name')}: output in {out}", flush=True)
    if args.resume:
        print(f"resuming with threads {args.threads}, {args.repeat} run(s) per spec and thread count", flush=True)
    if rerun:
        set_aside_runs(out, results["specs"], rerun, args.repeat)
        save_json(results_path, results)
    free = free_memory_percent()
    if args.min_free and free is not None and free < args.min_free:
        print(f"note: {free}% of memory is free, less than --min-free {args.min_free}: close memory-hungry "
              f"programs, or runs may wait up to {MIN_FREE_MAX_WAIT}s each", flush=True)

    def done(name):
        entry = results["specs"].get(name)
        return bool(entry and entry.get("complete") and not runs_missing(entry, args.threads, args.repeat))
    todo = [(name, rel) for name, rel in specs if not (args.resume and done(name))]
    if args.resume and len(todo) < len(specs):
        print(f"resuming: {len(specs) - len(todo)} of {len(specs)} specs already complete", flush=True)
    if not args.skip_lake_build:
        lake_build(root, out, args.lake_timeout or None)
    if todo and not args.no_warmup:
        warmup_build(root, out, specs, args.build_timeout or None)

    session_head = results["meta"].get("veil", {}).get("head")
    for i, (name, rel) in enumerate(todo, 1):
        reused = (reusable_build(root, rel, results["specs"].get(name), results["specs"])
                  if args.resume and name not in rebuild else None)
        earlier = {}
        if reused:
            entries = [reused]
            print(f"[{i}/{len(todo)}] {name} ({rel.as_posix()}): built in the earlier session, "
                  f"{len(reused['runs'])} run(s) recorded; continuing with its binary", flush=True)
        else:
            print(f"[{i}/{len(todo)}] {name} ({rel.as_posix()}): building"
                  + (" again (--rerun)" if name in rebuild else "") + " ...", flush=True)
            entries = build_spec(root, out, name, rel, args.build_timeout or None)
            if args.resume:
                earlier = {e["name"]: results["specs"].get(e["name"]) for e in entries}
            for entry in entries:
                # The runs that --rerun replaced stay with the spec
                if (earlier.get(entry["name"]) or {}).get("replaced_runs"):
                    entry["replaced_runs"] = earlier[entry["name"]]["replaced_runs"]
                results["specs"][entry["name"]] = entry
            save_json(results_path, results)
        for entry in entries:
            if entry["status"] != "ok":
                entry["complete"] = True
                save_json(results_path, results)
                message = entry["error_message"].splitlines()[0] if entry["error_message"] else ""
                print(f"  {entry['status']}: {message}" + (f" (see {out / entry['build']['log']})" if "build" in entry else ""),
                      flush=True)
                continue
            b = entry["build"]
            if reused:
                binary = pathlib.Path(b["binary"])
            else:
                print(f"  built in {b['total_seconds']:.1f}s: elaboration {b['elab_seconds']:.1f}s, compilation "
                      f"{b['compile_seconds']:.1f}s (extract {b['extract_seconds']:.1f}s, emit C {b['emit_c_seconds']:.1f}s, "
                      f"cc+link {b['cc_link_seconds']:.1f}s), RSS {b['max_rss_mb']:.0f} MB", flush=True)
                binary = pathlib.Path(b["built_binary"])
                if bin_dir:
                    binary = bin_dir / entry["name"]
                    shutil.copy2(b["built_binary"], binary)
                b["binary"] = str(binary)
                b["binary_sha1"] = sha1_file(binary)
                entry["runs"] = carried_runs(entry, earlier.get(entry["name"]), session_head, meta["veil"]["head"])
                if entry["runs"]:
                    print(f"  the same program as in the earlier session: keeping its {len(entry['runs'])} recorded run(s)",
                          flush=True)
                save_json(results_path, results)
            run_dir = out / "runs" / entry["name"]
            run_dir.mkdir(parents=True, exist_ok=True)
            recorded = {(r["threads"], r["rep"]) for r in entry["runs"]}
            timed_out = {r["threads"] for r in entry["runs"] if r.get("timeout")}
            for threads in args.threads:
                argv = thread_argv(threads, args.threshold, args.sub_steps)
                if threads in timed_out:
                    print(f"  t={threads}: timed out in the earlier session; not repeated", flush=True)
                    continue
                for rep in range(1, args.repeat + 1):
                    if (threads, rep) in recorded:
                        continue
                    memory = prepare_run(binary, entry["runs"], args.free_memory, args.cooldown, args.min_free)
                    free = memory["memory_free_percent"]
                    print(f"  t={threads} run {rep}/{args.repeat}: {' '.join([binary.name, *argv])}"
                          + (f" ({free}% of memory free)" if free is not None else "") + " ...", flush=True)
                    r = run_binary(binary, argv, run_dir, threads, rep, args.run_timeout or None)
                    r.update(memory)
                    entry["runs"].append(r)
                    save_json(results_path, results)
                    print(f"    {describe_run(r)}", flush=True)
                    if r["timeout"]:
                        break   # a timeout is the data point for this thread count; do not repeat it
            entry["complete"] = True
            save_json(results_path, results)
        # The binaries of the file have been timed (or copied): drop Veil's build folders and its
        # copies of the binaries.
        if not args.keep_build_folders:
            for entry in entries:
                b = entry.get("build", {})
                if b.get("build_folder"):
                    shutil.rmtree(b["build_folder"], ignore_errors=True)
                if b.get("built_binary"):
                    pathlib.Path(b["built_binary"]).unlink(missing_ok=True)

    print(flush=True)
    if REPORT_SCRIPT.exists():
        subprocess.run([sys.executable, str(REPORT_SCRIPT), str(out)])
    else:
        print(f"results in {results_path} ({REPORT_SCRIPT.name} not found next to this script)")


if __name__ == "__main__":
    main()
