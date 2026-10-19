#!/usr/bin/env python3
"""Compare finalized benchmark queries with archived solver-replay inputs."""
import argparse
import csv
import hashlib
import json
from pathlib import Path

from make_solver_checks import MODELS
from summarize import canonical_commands


def compare(benchmark_queries, solver_queries, depths):
    rows = []
    for name, _, _ in MODELS:
        for depth in depths:
            for mode, benchmark_mode in [('old', 'current'), ('early', 'early')]:
                benchmark = benchmark_queries / f'{name}_{benchmark_mode}_{depth}_1.smt2'
                archived = solver_queries / f'{name}_{mode}_{depth}.smt2'
                row = dict(model=name, depth=depth, mode=mode,
                           finalized_query=str(benchmark), archived_query=str(archived),
                           finalized_exists=benchmark.exists(), archived_exists=archived.exists())
                if benchmark.exists() and archived.exists():
                    a, b = benchmark.read_text(), archived.read_text()
                    row.update(
                        identical_bytes=a == b,
                        same_commands_ignoring_order=sorted(a.splitlines()) == sorted(b.splitlines()),
                        same_commands_after_implication_currying=canonical_commands(a) == canonical_commands(b),
                        finalized_sha256=hashlib.sha256(a.encode()).hexdigest(),
                        archived_sha256=hashlib.sha256(b.encode()).hexdigest())
                rows.append(row)
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--benchmark-query-dir', type=Path, required=True)
    parser.add_argument('--solver-query-dir', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True,
                        help='output filename stem; writes .json and .csv')
    parser.add_argument('--depths', type=int, nargs='+', default=[4, 8])
    args = parser.parse_args()
    rows = compare(args.benchmark_query_dir.resolve(), args.solver_query_dir.resolve(), args.depths)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.with_suffix('.json').write_text(json.dumps(rows, indent=2) + '\n')
    fields = list(dict.fromkeys(key for row in rows for key in row))
    with args.output.with_suffix('.csv').open('w') as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)
    print(json.dumps(dict(
        requested=len(rows),
        available=sum('identical_bytes' in row for row in rows),
        same_after_currying=sum(row.get('same_commands_after_implication_currying', False) for row in rows))))


if __name__ == '__main__':
    main()
