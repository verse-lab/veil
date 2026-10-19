#!/usr/bin/env python3
"""Check each model's deepest emitted early query with a separate short solver cap."""
import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import time

from make_solver_checks import MODELS
from run_solver_checks import REPLAY_TEMPLATE


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--queries', type=Path, required=True)
    parser.add_argument('--extra-queries', type=Path, nargs='*', default=[],
                        help='additional query directories, e.g. supplementary measurements')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--solver-timeout', type=int, default=2)
    args = parser.parse_args()
    repo, queries, output = args.repo.resolve(), args.queries.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    plugin = repo / '.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so'
    if not plugin.exists():
        parser.error(f'missing native cvc5 plugin: {plugin}')
    rows, labels = [], []
    for name, _, assertion in MODELS:
        matches = []
        for directory in [queries, *map(Path.resolve, args.extra_queries)]:
            for path in directory.glob(f'{name}_early_*_1.smt2'):
                match = re.fullmatch(re.escape(name) + r'_early_(\d+)_1\.smt2', path.name)
                if match:
                    matches.append((int(match[1]), path))
        row = dict(model=name, mode='early', assertion=assertion,
                   solver_timeout_seconds=args.solver_timeout, status='no_emitted_query')
        if matches:
            depth, source = max(matches)
            label = f'{name}_early_{depth}'
            target = output / f'{label}.smt2'
            shutil.copyfile(source, target)
            labels.append(label)
            row.update(depth=depth, label=label, source=str(source), query=str(target),
                       query_sha256=hashlib.sha256(target.read_bytes()).hexdigest(),
                       status='not_run')
        rows.append(row)
    source = REPLAY_TEMPLATE.replace('__ROOT__', json.dumps(str(output)))
    source = source.replace('__LABELS__', '#[' + ', '.join(map(json.dumps, labels)) + ']')
    source = source.replace('__TIMEOUT__', str(args.solver_timeout))
    lean_file = output / 'ReplayDeepest.lean'
    lean_file.write_text(source)
    start = time.monotonic()
    with (output / 'ReplayDeepest.log').open('w') as log:
        process = subprocess.Popen(['lake', 'env', 'lean', '--plugin=' + str(plugin), str(lean_file)],
                                   cwd=repo, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            exit_status = process.wait(timeout=30 + len(labels) * (args.solver_timeout + 2))
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            exit_status = 'process_timeout'
    log = (output / 'ReplayDeepest.log').read_text()
    for row in rows:
        if 'label' not in row:
            continue
        match = re.search(r'^REPLAY_RESULT ' + re.escape(row['label']) +
                          r' status=(\S+) solver_ms=(\d+) bytes=(\d+)', log, re.M)
        if match:
            row.update(status=match[1], solver_ms=int(match[2]), query_bytes=int(match[3]),
                       solver_accepted_query=not match[1].startswith('error:'))
    (output / 'deepest-results.json').write_text(json.dumps(rows, indent=2) + '\n')
    fields = list(dict.fromkeys(key for row in rows for key in row))
    with (output / 'deepest-results.csv').open('w') as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)
    execution = dict(status=exit_status, wall_seconds=time.monotonic() - start, queries=len(labels))
    (output / 'execution.json').write_text(json.dumps(execution, indent=2) + '\n')
    print(json.dumps(execution))
    for row in rows:
        print(json.dumps({key: row[key] for key in ['model', 'depth', 'status', 'solver_ms'] if key in row}))


if __name__ == '__main__':
    main()
