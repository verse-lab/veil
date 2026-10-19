#!/usr/bin/env python3
"""Summarize generated-query outcomes and sequential solver replays."""
from pathlib import Path
import argparse, csv, json, re

COLUMNS = ['model', 'depth', 'mode', 'status', 'initial_status', 'isolated_solver_ms',
           'nonisolated_solver_ms', 'smt_prep_ms', 'query_bytes',
           'smt_commands_equal_ignoring_order', 'smt_commands_equal_after_uncurrying', 'assertion', 'source']

def canonical_commands(text):
    """Parse SMT commands and normalize (a ∧ b) → c to a → b → c."""
    tokens = re.findall(r'\|[^|]*\||"(?:[^"]|"")*"|[()]|[^\s()]+', text)
    stack, commands = [], []
    for token in tokens:
        if token == '(':
            stack.append([])
        elif token == ')':
            node = stack.pop()
            if stack:
                stack[-1].append(node)
            else:
                commands.append(node)
        else:
            stack[-1].append(token)
    if stack:
        raise ValueError('unbalanced SMT parentheses')
    def normalize(node):
        if not isinstance(node, list):
            return node
        node = [normalize(x) for x in node]
        if (len(node) == 3 and node[0] == '=>' and isinstance(node[1], list)
                and len(node[1]) >= 2 and node[1][0] == 'and'):
            result = node[2]
            for antecedent in reversed(node[1][1:]):
                result = ['=>', antecedent, result]
            return result
        return node
    return sorted(json.dumps(normalize(c), ensure_ascii=False) for c in commands)


def summarize(output, depths=(4, 8)):
    models = json.loads((output / 'models.json').read_text())
    replay = '\n'.join(p.read_text() for p in sorted(output.glob('Replay*.log')))
    rows = []
    for name, source, assertion in models:
        log_path = output / (name + '.log')
        log = log_path.read_text() if log_path.exists() else ''
        for depth in depths:
            paths = [output / f'{name}_{mode}_{depth}.smt2' for mode in ['old', 'early']]
            same = None
            normalized_same = None
            if all(q.exists() for q in paths):
                same = sorted(paths[0].read_text().splitlines()) == sorted(paths[1].read_text().splitlines())
                normalized_same = canonical_commands(paths[0].read_text()) == canonical_commands(paths[1].read_text())
            for mode in ['old', 'early']:
                label = f'{name}_{mode}_{depth}'
                match = re.search(r'^SOLVER_RESULT ' + label + r' status=(\S+) solver_ms=(\d+) smt_prep_ms=(\d+) bytes=(\d+)', log, re.M)
                isolated = re.search(r'^REPLAY_RESULT ' + label + r' status=(\S+) solver_ms=(\d+) bytes=(\d+)', replay, re.M)
                row = dict(model=name, source=source, assertion=assertion, depth=depth, mode=mode,
                           smt_commands_equal_ignoring_order=same, smt_commands_equal_after_uncurrying=normalized_same)
                if match:
                    row.update(status=match[1], initial_status=match[1], nonisolated_solver_ms=int(match[2]),
                               smt_prep_ms=int(match[3]), query_bytes=int(match[4]))
                else:
                    row['status'] = 'preprocessing_failed_or_incomplete'
                if isolated:
                    row.update(status=isolated[1], isolated_solver_ms=int(isolated[2]))
                    if 'query_bytes' not in row:
                        row['query_bytes'] = int(isolated[3])
                rows.append(row)
    (output / 'solver-results.json').write_text(json.dumps(rows, indent=2) + '\n')
    with (output / 'solver-results.csv').open('w') as f:
        writer = csv.DictWriter(f, fieldnames=COLUMNS)
        writer.writeheader()
        writer.writerows(rows)
    return rows

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--depths', nargs='+', type=int, default=[4, 8])
    args = parser.parse_args()
    print(json.dumps(summarize(args.output.resolve(), args.depths), indent=2))
