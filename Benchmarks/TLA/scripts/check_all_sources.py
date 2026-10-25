#!/usr/bin/env python3
"""Check upstream sources across Benchmarks/TLA and summarize each benchmark.

Run directly, from any directory:
    ./Benchmarks/TLA/scripts/check_all_sources.py --output /tmp/tla-all-sources

Uses check_sources.py's comparisons, where the verdicts are defined, and
requires only Python 3.9+.
Files without an upstream file URL or with a different upstream file type are
listed as skipped. Unpinned revisions and read/download failures are errors.
Models downloaded by fetch_upstream.py are not benchmark files; they are only
compared with the SHA-256 pinned there.
Exit 0 means comparisons completed without errors, even when sources differ;
skipped files remain unchecked. This does not run TLC or establish equivalence.
"""

import argparse
from collections import Counter
import json
from pathlib import Path
import tempfile

import check_sources
import fetch_upstream


ROOT = Path(__file__).resolve().parents[1]


def benchmark(path):
    """Benchmark name for an absolute path or a repository-relative report path."""
    parts = (check_sources.REPO / path).relative_to(ROOT).parts
    if parts[0] == "TLAPlusExamples":
        return parts[1] if len(parts) > 2 else Path(path).stem
    if len(parts) > 1:
        return parts[0]
    name = Path(path).stem
    return name[2:] if name.startswith("MC") and (ROOT / (name[2:] + ".cfg")).is_file() else name


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--output", type=Path, help="Evidence directory (default: a new temporary directory)")
    args = parser.parse_args()
    output = (args.output or Path(tempfile.mkdtemp(prefix="tla-all-sources-"))).resolve()
    pinned = {ROOT / name: sha for name, _, sha, _ in fetch_upstream.FILES}
    paths = sorted(path for path in ROOT.rglob("*")
                   if path.is_file() and path.suffix in (".tla", ".cfg") and output not in path.parents
                   and path not in pinned)
    selected, skipped, errors = [], [], []
    for path in paths:
        try:
            refs = check_sources.SOURCE_URL.findall(path.read_text(encoding="utf-8"))
            if not refs:
                reason = "No upstream file URL recorded"
            elif not any(Path(source).suffix == path.suffix for _, _, source in refs):
                reason = "Upstream reference has a different file type"
            else:
                selected.append(path)
                continue
            skipped.append({"local": check_sources.report_path(path), "reason": reason})
        except (OSError, ValueError) as error:
            errors.append({"local": check_sources.report_path(path), "error": str(error)})

    report = check_sources.check_files(selected, output)
    report["errors"].extend(errors)
    report["skipped"].extend(skipped)
    report["downloaded"] = {check_sources.report_path(path): fetch_upstream.sha256(path.read_bytes()) == sha
                            for path, sha in pinned.items() if path.is_file()}
    columns = ("files", "pairs", "identical", "comments", "changed", "skipped", "errors")
    summary = {name: dict.fromkeys(columns, 0) for name in sorted({benchmark(path) for path in paths})}
    for path in paths:
        summary[benchmark(path)]["files"] += 1
    for result in report["results"]:
        row = summary[benchmark(result["local"])]
        row["pairs"] += 1
        category = {"BYTE_IDENTICAL": "identical", "COMMENTS_OR_SPACING_ONLY": "comments"}.get(result["status"], "changed")
        row[category] += 1
    for category in ("skipped", "errors"):
        for item in report[category]:
            summary[benchmark(item["local"])][category] += 1
    report["summary"] = summary
    (output / "report.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    totals = Counter()
    lines = [f"Self-test: {report['self_test']}\n", f"{'Benchmark':25} " + " ".join(f"{label:>8}" for label in
             ("Files", "Pairs", "Exact", "Comments", "Changed", "Skipped", "Errors"))]
    for name, row in summary.items():
        totals.update(row)
        lines.append(f"{name:25} " + " ".join(f"{row[key]:8}" for key in columns))
    lines.append(f"{'TOTAL':25} " + " ".join(f"{totals[key]:8}" for key in columns))
    lines.append("\nPairs count upstream comparisons; Exact/Comments/Changed partition those pairs.")
    for category, field in (("skipped", "reason"), ("errors", "error")):
        lines.append(f"\n{category.upper()}:")
        lines.extend(f"  {item['local']}: {item[field]}" for item in report[category])
    if report["downloaded"]:
        lines.append("\nDOWNLOADED BY fetch_upstream.py (not counted above):")
        lines.extend(f"  {name}: {'matches' if ok else 'DIFFERS from'} the pinned SHA-256"
                     for name, ok in report["downloaded"].items())
    lines.append("\nExit 0 means comparisons completed; skipped files remain unchecked. No semantic equivalence claim.")
    lines.append("Verdict definitions: Benchmarks/TLA/scripts/check_sources.py")
    (output / "summary.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n" + "\n".join(lines) + f"\nEvidence: {output}")
    return 1 if report["errors"] or not report["results"] or not all(report["downloaded"].values()) else 0


if __name__ == "__main__":
    raise SystemExit(main())
