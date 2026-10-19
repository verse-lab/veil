#!/usr/bin/env python3
"""Audit finalized benchmark provenance and timing boundaries (read-only)."""
import argparse
import csv
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path

csv.field_size_limit(sys.maxsize)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--results', required=True, type=Path)
    ap.add_argument('--manifest', required=True, type=Path)
    ap.add_argument('--output', required=True, type=Path)
    ap.add_argument('--portable-only', action='store_true',
                    help='Require artifacts inside --results, ignoring original absolute paths')
    args = ap.parse_args()
    models = json.loads(args.manifest.read_text())
    manifest = {m['model']: m for m in models}
    rows = list(csv.DictReader((args.results / 'runs.csv').open()))
    expected = {(m, d, v) for m in manifest for d in [1, 2, 4, 8, 16, 32]
                for v in ['old', 'early']}
    found = Counter((r['model'], int(r['depth']), r['variant']) for r in rows)
    errors = []
    if set(found) != expected or any(n != 1 for n in found.values()):
        errors.append('Requested grid is missing, duplicated, or has extra cells')
    query_count = 0
    hashes = {}
    by_pair = {}

    def locate(recorded):
        path = Path(recorded)
        if not args.portable_only and path.exists():
            return path
        # Namespace-repair checkpoints can retain their original staging root.
        # The delivered primary tree keeps every artifact's directory/basename.
        for directory in ('queries', 'batch-sources', 'sources'):
            candidate = args.results / directory / path.name
            if candidate.is_file():
                return candidate
        # Preserve the path relative to the results directory after relocation.
        if 'results' in path.parts:
            index = len(path.parts) - 1 - path.parts[::-1].index('results')
            return args.results.joinpath(*path.parts[index + 1:])
        return args.results / '__missing_artifact__' / path.name if args.portable_only else path

    def sha(path):
        if path not in hashes:
            hashes[path] = hashlib.sha256(path.read_bytes()).hexdigest()
        return hashes[path]

    def fail(row, message):
        errors.append(f'{row["cell_id"]}: {message}')

    for row in rows:
        if row['status'] in {'not_started', 'query_ready', 'pending', ''}:
            fail(row, 'nonterminal status')
        checkpoint = args.results / 'cells' / (row['cell_id'] + '.json')
        if not checkpoint.exists():
            fail(row, 'missing checkpoint')
            continue
        cell = json.loads(checkpoint.read_text())
        if cell['original_sha256'] != manifest[row['model']]['source_sha256']:
            fail(row, 'original source differs from frozen inventory')
        for key, value in cell['row'].items():
            recorded = '' if value is None else str(value)
            if isinstance(value, bool):
                recorded = str(value)
            if key in row and row[key] != recorded:
                fail(row, f'CSV/checkpoint mismatch in {key}')
        events = cell.get('events', [])
        if any(e.get('event') == 'pipeline' for e in events) and not any(e.get('event') == 'query_elaboration' and e.get('status') == 'begin' for e in events):
            fail(row, 'missing query-begin marker; wall watchdog was ineffective')
        source = locate(row['source_path'])
        if not source.exists() or sha(source) != cell['source_sha256']:
            fail(row, 'generated source missing or checksum mismatch')
        command = cell.get('batch_execution', {}).get('command', [])
        if not any('--plugin=' in s and 'cvc5' in s for s in command):
            fail(row, 'translation launcher did not load native cvc5 plugin')
        if row['translation_status'] == 'complete':
            query_count += 1
            path = locate(row['query_path'])
            if not path.exists() or sha(path) != row['query_sha256']:
                fail(row, 'query missing or checksum mismatch')
            elif path.stat().st_size != int(row['query_bytes']):
                fail(row, 'query byte count differs')
            keys = ['preprocessing_ms', 'smt_preprocessing_ms',
                    'translation_ms', 'serialization_ms']
            if any(row[k] == '' for k in keys):
                fail(row, 'complete query lacks stage totals')
            elif sum(int(row[k]) for k in keys) != int(row['query_total_ms']):
                fail(row, 'query total does not equal completed stage sum')
        elif row['query_total_ms']:
            fail(row, 'uncompleted query has a completed query timing')
        if row['solver_status'] in {'sat', 'unsat'}:
            if row['translation_status'] != 'complete':
                fail(row, 'solver verdict without emitted query')
            if int(row['completed_total_ms']) != int(row['query_total_ms']) + int(row['solver_ms']):
                fail(row, 'completed total is inconsistent')
            verdict = row['solver_status']
        elif row['status'] == 'unsat_preprocessing':
            verdict = 'unsat'
        else:
            verdict = None
            if row['completed_total_ms']:
                fail(row, 'nondefinite query marked with completed total')
        by_pair.setdefault((row['model'], row['depth']), {})[row['variant']] = verdict
    for pair, variants in by_pair.items():
        definite = {v for v in variants.values() if v is not None}
        if len(definite) > 1:
            errors.append(f'{pair}: contradictory definite answers')
    result = {'passed': not errors, 'requested_cells': len(expected),
              'recorded_cells': len(rows), 'emitted_queries_checked': query_count,
              'source_and_query_files_hashed': len(hashes), 'errors': errors}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))
    raise SystemExit(bool(errors))


if __name__ == '__main__':
    main()
