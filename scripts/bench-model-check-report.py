#!/usr/bin/env python3
"""Summarize a results directory written by scripts/bench-model-check.py.

Reads OUT/results.json and prints compilation and model checking tables, aggregated
over successful runs (median by default). It also writes:

  OUT/summary.csv                         one row per spec and thread count, including build failures;
  OUT/csv/veil-results-rev-<rev>-<N>.csv    one file per thread count N.

It can run while the benchmark is still in progress, on what results.json holds so far.

usage: python3 scripts/bench-model-check-report.py OUT [--agg median|mean] [--rev REV]
"""
from __future__ import annotations

import argparse
import csv
import json
import pathlib
import statistics
import sys

MB = 1024 * 1024
SUMMARY_FIELDS = [
    "run", "spec", "source", "status", "threads", "runs", "runs_ok", "wall_seconds", "cpu_seconds", "user_seconds",
    "system_seconds", "max_rss_mb", "checker_elapsed_ms", "result", "distinct_states", "states_generated", "diameter",
    "build_total_seconds", "elab_seconds", "compile_seconds", "extract_seconds", "emit_c_seconds", "cc_link_seconds",
    "build_max_rss_mb", "c_bytes", "binary_bytes", "error_message",
]
# Columns of the per-thread CSVs.
RUN_CSV_FIELDS = [
    "name", "compilation_time_seconds", "wall_time_seconds", "cpu_time_seconds", "user_time_seconds",
    "system_time_seconds", "checker_elapsed_ms", "states_generated", "distinct_states", "depth", "max_rss_mb",
    "success", "error_message",
]


def agg(values, how: str):
    """Median (or mean) of the values that are not None, rounded; '' when there are none."""
    vals = [v for v in values if v is not None]
    if not vals:
        return ""
    return round(statistics.median(vals) if how == "median" else statistics.mean(vals), 3)


def same(values):
    """The common value of the values that are not None, or '' when they differ or are absent."""
    vals = [v for v in values if v is not None]
    return vals[0] if vals and all(v == vals[0] for v in vals) else ""


def fmt(value, spec="{:.1f}", width=0):
    text = "-" if value in (None, "") else spec.format(value)
    return f"{text:>{width}s}" if width else text


def run_groups(entry: dict) -> dict:
    """The entry's runs by thread count, in the order they were run."""
    groups = {}
    for r in entry.get("runs", []):
        groups.setdefault(r["threads"], []).append(r)
    return groups


def aggregate_runs(runs, how: str) -> dict:
    """One summary of the runs at one thread count."""
    ok = [r for r in runs if r.get("success")]
    col = lambda key: [r.get(key) for r in ok]
    counts = {(r.get("distinct_states"), r.get("states_generated"), r.get("diameter")) for r in ok}
    verdicts = sorted({r.get("result") for r in ok if r.get("result")})
    return {
        "runs": len(runs), "runs_ok": len(ok), "timed_out": any(r.get("timeout") for r in runs),
        "wall_seconds": agg(col("wall_seconds"), how), "cpu_seconds": agg(col("cpu_seconds"), how),
        "user_seconds": agg(col("user_seconds"), how), "system_seconds": agg(col("system_seconds"), how),
        "max_rss_mb": agg(col("max_rss_mb"), how), "checker_elapsed_ms": agg(col("checker_elapsed_ms"), how),
        "distinct_states": same(col("distinct_states")), "states_generated": same(col("states_generated")),
        "diameter": same(col("diameter")), "counts_differ": len(counts) > 1,
        "result": ", ".join(verdicts), "max_wall_seconds": max((r.get("wall_seconds") or 0) for r in runs) if runs else "",
        "error_message": next((r.get("error_message") for r in runs if r.get("error_message")), ""),
    }


def build_columns(entry: dict) -> dict:
    b = entry.get("build", {})
    return {
        "build_total_seconds": b.get("total_seconds", ""), "elab_seconds": b.get("elab_seconds", ""),
        "compile_seconds": b.get("compile_seconds", ""), "extract_seconds": b.get("extract_seconds", ""),
        "emit_c_seconds": b.get("emit_c_seconds", ""), "cc_link_seconds": b.get("cc_link_seconds", ""),
        "build_max_rss_mb": b.get("max_rss_mb", ""), "c_bytes": b.get("c_bytes", ""),
        "binary_bytes": b.get("binary_bytes", ""),
    }


def print_header(results: dict, run: str):
    meta = results.get("meta", {})
    veil = meta.get("veil", {})
    print(f"run {run}: Veil @ {(veil.get('head') or '?')[:8]}"
          + ("  [uncommitted changes]" if veil.get("status") else ""))
    print(f"system {meta.get('cpu') or meta.get('machine')}, {meta.get('cpus')} CPUs, "
          f"{fmt((meta.get('memory_bytes') or 0) / MB / 1024 if meta.get('memory_bytes') else None, '{:.0f}')} GB, "
          f"{meta.get('platform')}; {meta.get('date')}")
    print(f"threads {meta.get('threads')}, thresholdToParallel {meta.get('threshold')}, numSubSteps {meta.get('sub_steps')}, "
          f"{meta.get('repeat')} run(s) per spec and thread count, run timeout {meta.get('run_timeout')}s")


def print_compilation(specs: dict):
    print("\ncompilation, wall seconds: total = elaboration (Lean start-up, imports and the spec itself) + compilation "
          "(extraction of the executable definitions + emitting C + compiling and linking the C); RSS of the process tree")
    print(f"{'spec':28s}{'total':>8s}{'elab':>8s}{'compile':>9s}{'extract':>9s}{'emit C':>8s}{'cc+link':>9s}{'C MB':>7s}{'RSS MB':>8s}")
    for name, entry in specs.items():
        b = entry.get("build", {})
        if entry.get("status") != "ok":
            message = (entry.get("error_message") or "").splitlines()
            print(f"{name:28s}{fmt(b.get('total_seconds'), width=8)}  {entry.get('status')}"
                  + (f": {message[0][:90]}" if message else ""))
            continue
        print(f"{name:28s}{fmt(b.get('total_seconds'), width=8)}{fmt(b.get('elab_seconds'), width=8)}"
              f"{fmt(b.get('compile_seconds'), width=9)}{fmt(b.get('extract_seconds'), width=9)}"
              f"{fmt(b.get('emit_c_seconds'), width=8)}{fmt(b.get('cc_link_seconds'), width=9)}"
              f"{fmt(b['c_bytes'] / MB if b.get('c_bytes') else None, '{:.2f}', 7)}{fmt(b.get('max_rss_mb'), '{:.0f}', 8)}")


def print_runs(specs: dict, how: str):
    print(f"\nmodel checking: {how} over the successful runs; wall and CPU in seconds, RSS in MB; "
          "'>' = timed out, 'runs' = successful/all")
    print(f"{'spec':28s}{'thr':>4s}{'runs':>6s}{'wall':>10s}{'cpu':>10s}{'RSS MB':>8s}{'distinct':>12s}{'generated':>12s}"
          f"{'diam':>6s}  result")
    for name, entry in specs.items():
        if entry.get("status") != "ok":
            continue
        groups = run_groups(entry)
        if not groups:
            print(f"{name:28s}  (no runs yet)")
        for threads, runs in groups.items():
            a = aggregate_runs(runs, how)
            if a["runs_ok"]:
                cells = (f"{fmt(a['wall_seconds'], '{:.2f}', 10)}{fmt(a['cpu_seconds'], '{:.2f}', 10)}"
                         f"{fmt(a['max_rss_mb'], '{:.0f}', 8)}{fmt(a['distinct_states'], '{}', 12)}"
                         f"{fmt(a['states_generated'], '{}', 12)}{fmt(a['diameter'], '{}', 6)}  {a['result']}")
                if a["counts_differ"]:
                    cells += "  STATE COUNTS DIFFER BETWEEN RUNS"
            elif a["timed_out"]:
                cells = f"{'>' + format(a['max_wall_seconds'], '.0f'):>10s}  timed out"
            else:
                cells = f"{'FAILED':>10s}  {a['error_message'][:80]}"
            print(f"{name:28s}{threads:>4d}{a['runs_ok']:>3d}/{a['runs']:<2d}{cells}")


def summary_rows(specs: dict, how: str, run: str):
    rows = []
    for name, entry in specs.items():
        base = {"run": run, "spec": name, "source": entry.get("source", ""), "status": entry.get("status", ""),
                **build_columns(entry)}
        groups = run_groups(entry)
        if entry.get("status") != "ok" or not groups:
            rows.append({**base, "error_message": (entry.get("error_message") or "").replace("\n", " ")[:500]})
            continue
        for threads, runs in groups.items():
            a = aggregate_runs(runs, how)
            rows.append({**base, "threads": threads, "runs": a["runs"], "runs_ok": a["runs_ok"],
                         "wall_seconds": a["wall_seconds"], "cpu_seconds": a["cpu_seconds"],
                         "user_seconds": a["user_seconds"], "system_seconds": a["system_seconds"],
                         "max_rss_mb": a["max_rss_mb"], "checker_elapsed_ms": a["checker_elapsed_ms"],
                         "result": a["result"], "distinct_states": a["distinct_states"],
                         "states_generated": a["states_generated"], "diameter": a["diameter"],
                         "error_message": ("state counts differ between runs; " if a["counts_differ"] else "")
                         + a["error_message"].replace("\n", " ")[:500]})
    return rows


def thread_rows(specs: dict, threads: int, how: str):
    """Rows of one per-thread CSV: the specs that built, at one thread count."""
    rows = []
    for name, entry in specs.items():
        if entry.get("status") != "ok":
            continue
        runs = run_groups(entry).get(threads)
        if not runs:
            continue
        a = aggregate_runs(runs, how)
        elapsed = a["checker_elapsed_ms"]
        rows.append({
            "name": name, "compilation_time_seconds": entry.get("build", {}).get("total_seconds", ""),
            "wall_time_seconds": a["wall_seconds"], "cpu_time_seconds": a["cpu_seconds"],
            "user_time_seconds": a["user_seconds"], "system_time_seconds": a["system_seconds"],
            "checker_elapsed_ms": int(round(elapsed)) if elapsed != "" else "",
            "states_generated": a["states_generated"], "distinct_states": a["distinct_states"],
            "depth": a["diameter"], "max_rss_mb": a["max_rss_mb"],
            "success": "TRUE" if a["runs_ok"] == a["runs"] else "FALSE",
            "error_message": a["error_message"].replace("\n", " ")[:500],
        })
    return rows


def write_csv(path: pathlib.Path, fields, rows):
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("out", help="the --out directory of bench-model-check.py")
    ap.add_argument("--agg", choices=["median", "mean"], default="median", help="aggregation over runs (default median)")
    ap.add_argument("--rev", help="revision in the names of the per-thread CSVs (default: the checkout's commit)")
    args = ap.parse_args()
    out = pathlib.Path(args.out).resolve()
    results_path = out / "results.json"
    if not results_path.exists():
        sys.exit("results.json not found in the output directory")
    results = json.loads(results_path.read_text())
    specs = results.get("specs", {})
    run = results.get("meta", {}).get("name") or out.name
    print_header(results, run)
    print_compilation(specs)
    print_runs(specs, args.agg)

    write_csv(out / "summary.csv", SUMMARY_FIELDS, summary_rows(specs, args.agg, run))
    rev = args.rev or ((results.get("meta", {}).get("veil", {}).get("head") or "unknown")[:8])
    thread_counts = sorted({r["threads"] for e in specs.values() for r in e.get("runs", [])})
    for threads in thread_counts:
        write_csv(out / "csv" / f"veil-results-rev-{rev}-{threads}.csv", RUN_CSV_FIELDS,
                  thread_rows(specs, threads, args.agg))
    print("\nCSV (relative to the output directory): summary.csv"
          + (f" and csv/veil-results-rev-{rev}-{{N}}.csv for N in {thread_counts}" if thread_counts else ""))


if __name__ == "__main__":
    main()
