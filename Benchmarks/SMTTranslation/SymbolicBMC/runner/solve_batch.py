#!/usr/bin/env python3
"""Solve ready symbolic BMC queries sequentially, amortizing Lean/plugin startup.

Each query has its own run_cmd, event file and checkpoint. Solver durations are
Smt.solve durations, not shares of the batch process wall time. No proof or
counterexample reconstruction is performed. A watchdog kills the full process
group for a stuck cell, checkpoints that timeout, and restarts remaining cells.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time

from run import REPLAY, atomic_json, events, export, sha


def verdict(row):
    if row['status'] == 'unsat_preprocessing':
        return 'unsat'
    return row['solver_status'] if row['solver_status'] in ['sat', 'unsat'] else None


def check_pair(row, out):
    current = verdict(row)
    if current is None:
        return
    other_variant = 'early' if row['variant'] == 'old' else 'old'
    key = row['cell_id'].replace('__' + row['variant'] + '__', '__' + other_variant + '__')
    path = out / 'cells' / (key + '.json')
    if path.exists():
        other = json.loads(path.read_text())['row']
        previous = verdict(other)
        if previous and previous != current:
            raise RuntimeError(f'Contradictory definite verdicts: {row["cell_id"]}={current}, '
                               f'{other["cell_id"]}={previous}; STOP for investigation')


def apply_result(cell, raw, batch_id, log_path, event_path, cap):
    row = cell['row']
    result = next((e for e in reversed(raw) if e.get('event') == 'solver'
                   and e.get('status') != 'begin'), None)
    if result is None:
        return False
    status, detail = result['status'], result.get('detail', '')
    if status == 'unknown' and ('timeout' in detail.lower() or 'time limit' in detail.lower()):
        status = 'timeout'
    row.update(solver_status=status, solver_ms=result['elapsed_ms'], solver_exit=None,
               solver_timeout=None, solver_process_wall_ms=None, solver_log=str(log_path),
               completed_total_ms=None)
    row['status'] = status if status in ['sat', 'unsat'] else 'solver_' + status
    if status in ['sat', 'unsat']:
        row['completed_total_ms'] = row['query_total_ms'] + row['solver_ms']
        row.update(failure_phase=None, failure_kind=None, failure_message=None)
    else:
        row.update(failure_phase='solver', failure_kind='solver_' + status,
                   failure_message=detail[:8000])
    cell['solver_events'] = raw
    cell['solver_execution'] = dict(batch_id=batch_id, event_path=str(event_path),
                                   batch_log=str(log_path), solver_timeout_seconds=cap,
                                   process_wall_attribution='See solver-batches metadata; not apportioned per cell')
    return True


def apply_failure(cell, raw, batch_id, log_path, event_path, message, timeout):
    row = cell['row']
    status = 'process_timeout' if timeout else 'error'
    row.update(status='solver_' + status, solver_status=status, solver_ms=None,
               solver_exit=None, solver_timeout='solver_timeout' if timeout else None,
               solver_process_wall_ms=None, solver_log=str(log_path), completed_total_ms=None,
               failure_phase='solver', failure_kind='wall_timeout' if timeout else 'solver_error',
               failure_message=message[:8000])
    cell['solver_events'] = raw
    cell['solver_execution'] = dict(batch_id=batch_id, event_path=str(event_path),
                                   batch_log=str(log_path), process_watchdog_timeout=timeout)


def source_for(cells, out, timeout):
    fragments = ['import Veil\nset_option Elab.async false\n']
    for path, cell in cells:
        row = cell['row']
        event_path = out / 'events' / (row['cell_id'] + '.solver.jsonl')
        body = 'open Lean Elab Command in' + REPLAY.split('open Lean Elab Command in', 1)[1]
        body = body.replace('__EVENT_PATH__', json.dumps(str(event_path)))
        body = body.replace('__QUERY_PATH__', json.dumps(row['query_path']))
        body = body.replace('__TIMEOUT__', str(timeout))
        fragments.append(body)
    return '\n'.join(fragments)


def run_batch(cells, args, repo, out, plugin, batch_number):
    batch_id = f'solver-batch-{batch_number:04d}'
    source_path = out / 'solver-sources' / (batch_id + '.lean')
    log_path = out / 'logs' / (batch_id + '.log')
    metadata_path = out / 'solver-batches' / (batch_id + '.json')
    source_path.write_text(source_for(cells, out, args.solver_timeout))
    event_paths = []
    for _, cell in cells:
        event = out / 'events' / (cell['row']['cell_id'] + '.solver.jsonl')
        event.unlink(missing_ok=True)
        event_paths.append(event)
    command = ['lake', 'env', 'lean', '-D', 'Elab.async=false',
               '--plugin=' + str(plugin), str(source_path)]
    start = time.monotonic()
    current = 0
    active_start = None
    gap_start = start
    timed_out = None
    completed = set()
    metadata = dict(batch_id=batch_id, cells=[c['row']['cell_id'] for _, c in cells],
                    source=str(source_path), source_sha256=sha(source_path), log=str(log_path),
                    command=command, solver_timeout_seconds=args.solver_timeout,
                    query_watchdog_seconds=args.solver_timeout + 5,
                    setup_watchdog_seconds=args.setup_timeout,
                    attribution='solver_ms is measured inside Smt.solve; batch wall time is separate')
    atomic_json(metadata_path, metadata)

    def checkpoint(index):
        path, cell = cells[index]
        atomic_json(path, cell)
        completed.add(index)
        row = cell['row']
        print(f'SOLVER_END {row["cell_id"]} {row["status"]} solver_ms={row["solver_ms"]}', flush=True)
        check_pair(row, out)

    with log_path.open('w') as log:
        process = subprocess.Popen(command, cwd=repo, stdout=log, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        try:
            while process.poll() is None:
                while current < len(cells):
                    raw = events(event_paths[current])
                    if apply_result(cells[current][1], raw, batch_id, log_path,
                                    event_paths[current], args.solver_timeout):
                        checkpoint(current)
                        current += 1
                        active_start = None
                        gap_start = time.monotonic()
                        continue
                    if active_start is None and any(e.get('status') == 'begin' for e in raw):
                        active_start = time.monotonic()
                        print(f'SOLVER_BEGIN {cells[current][1]["row"]["cell_id"]}', flush=True)
                    break
                if current == len(cells):
                    # Normal Lean shutdown also gets a finite bound.
                    if time.monotonic() - gap_start > args.setup_timeout:
                        os.killpg(process.pid, signal.SIGKILL)
                        process.wait()
                    else:
                        time.sleep(0.05)
                    continue
                now = time.monotonic()
                if active_start is not None and now-active_start > args.solver_timeout+5:
                    timed_out = current
                    metadata['watchdog'] = 'query'
                elif active_start is None and now-gap_start > args.setup_timeout:
                    timed_out = current
                    metadata['watchdog'] = 'setup_or_between_queries'
                if timed_out is not None:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                    break
                time.sleep(0.05)
        finally:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            metadata.update(exit_code=process.returncode,
                            batch_wall_ms=round((time.monotonic()-start)*1000),
                            completed_cells=[cells[i][1]['row']['cell_id'] for i in sorted(completed)])
            if timed_out is not None:
                metadata['watchdog_cell'] = cells[timed_out][1]['row']['cell_id']
            atomic_json(metadata_path, metadata)

    # A batch can finish between polls, or Lean can continue past a failed run_cmd.
    for index, (_, cell) in enumerate(cells):
        if index in completed:
            continue
        raw = events(event_paths[index])
        if apply_result(cell, raw, batch_id, log_path, event_paths[index], args.solver_timeout):
            checkpoint(index)
        elif index == timed_out or any(e.get('status') == 'begin' for e in raw):
            message = ('Per-query process watchdog exceeded' if index == timed_out else
                       'Lean run_cmd ended without a terminal solver event; inspect batch log')
            apply_failure(cell, raw, batch_id, log_path, event_paths[index], message,
                          timeout=index == timed_out)
            checkpoint(index)
    metadata['completed_cells'] = [cells[i][1]['row']['cell_id'] for i in sorted(completed)]
    atomic_json(metadata_path, metadata)
    export(out)
    if not completed:
        raise RuntimeError(f'{batch_id} produced no solver result or begin event; inspect {log_path}')
    return [entry for i, entry in enumerate(cells) if i not in completed]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--solver-timeout', type=int, default=10)
    parser.add_argument('--setup-timeout', type=float, default=60)
    parser.add_argument('--retry-failed', action='store_true')
    parser.add_argument('--generate-only', action='store_true')
    args = parser.parse_args()
    repo, out = args.repo.resolve(), args.out.resolve()
    plugin = repo / '.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so'
    if not plugin.exists():
        parser.error(f'missing native solver plugin: {plugin}')
    for directory in ['solver-sources', 'solver-batches', 'events', 'logs']:
        (out / directory).mkdir(parents=True, exist_ok=True)
    requested = out / 'requested-cells.json'
    paths = ([out / 'cells' / (key + '.json') for key in json.loads(requested.read_text())]
             if requested.exists() else [])
    known = set(paths)
    paths += [p for p in sorted((out / 'cells').glob('*.json')) if p not in known]
    pending = []
    for path in paths:
        cell = json.loads(path.read_text())
        row = cell['row']
        if row['translation_status'] != 'complete' or verdict(row):
            continue
        if row['status'] != 'query_ready' and not args.retry_failed:
            continue
        query = Path(row['query_path'])
        if not query.exists() or sha(query) != row['query_sha256']:
            raise RuntimeError(f'Query missing or changed for {row["cell_id"]}')
        check_pair(row, out)
        pending.append((path, cell))
    invocation = dict(repo=str(repo), ready_cells=len(pending), script_sha256=sha(__file__),
                      solver_timeout_seconds=args.solver_timeout,
                      solver_configuration='Veil trusted default options, finite-model-find=true, nl-ext-tplanes=true, enum-inst-interleave=true',
                      proof_status='No reconstructed proof or measurement theorem',
                      measurement='Sequential Smt.solve calls, shared import/process setup, per-cell atomic checkpoints; no process wall-time apportionment')
    atomic_json(out / 'solver-batch-invocation.json', invocation)
    if args.generate_only:
        (out / 'solver-sources' / 'batch-preview.lean').write_text(source_for(pending, out, args.solver_timeout))
        print(json.dumps(invocation))
        return
    existing = [int(p.stem.rsplit('-', 1)[1]) for p in (out / 'solver-batches').glob('solver-batch-*.json')]
    batch_number = max(existing, default=0)+1
    try:
        while pending:
            pending = run_batch(pending, args, repo, out, plugin, batch_number)
            batch_number += 1
    finally:
        export(out)


if __name__ == '__main__':
    main()
