#!/usr/bin/env python3
"""Reproduce issue #123's preprocessing scaling on the existing Ring model.

Run from the repository root after building Veil:
  python3 Benchmarks/SMTTranslation/ring_stages.py
  python3 Benchmarks/SMTTranslation/ring_stages.py --modes early local --depths 32 64

Generated Lean files and full logs are retained under .veil.tmp/issue123/ring.
These are preprocessing measurements, not verification results: the probes
deliberately end with `sorry`, and never call the SMT solver. Model generation
and Lean startup are outside the reported stage timings. Heartbeat/recursion
limits are relaxed to isolate the unchanged default simp step budget.
The target_nodes metric excludes the local context: local mode has target
False and stores its actual constraints in hypotheses.

current: existing veil_bmc order (trusted-SMT default).
early: introduce outer universal variables before the existing order.
local: also assume the trace conjunction, split its conjuncts, and simplify
       individual hypotheses without splitting disjunctions into proof goals.
"""

import argparse
from pathlib import Path
import subprocess


HEADER = '''module
public import Veil
public meta import Lean.Util.NumObjs
open Lean Elab Tactic Meta Veil

elab "bench_stage " label:str t:tactic : tactic => do
  let start ← IO.monoMsNow
  try
    evalTactic t
    let elapsed := (← IO.monoMsNow) - start
    let goals ← getGoals
    let mut nodes := 0
    for g in goals do
      nodes := nodes + (← (← g.getType).numObjs)
    IO.println s!"STAGE {label.getString} ms={elapsed} goals={goals.length} target_nodes={nodes}"
  catch ex =>
    IO.println s!"FAILED {label.getString} ms={(← IO.monoMsNow) - start}: {← ex.toMessageData.toString}"
    throw ex
'''

CURRENT = '''
  bench_stage "nextSimp" (veil_simp +instances only [nextSimp])
  bench_stage "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
  bench_stage "intros" veil_intros
  bench_stage "destruct" veil_destruct
  bench_stage "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  bench_stage "smtSimp" (veil_simp +instances only [smtSimp])
  bench_stage "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
'''

LOCAL = '''
  bench_stage "intros" veil_intros
  bench_stage "trace_hyp" (unhygienic intro htrace)
  bench_stage "split_conj" (veil_destruct only [And])
  bench_stage "nextSimp_local" (veil_simp +instances only [nextSimp] at *)
  bench_stage "hoist_local" (veil_simp +instances only [↓ existsQuantifierSimpGuarded] at *)
  bench_stage "destruct" veil_destruct
  bench_stage "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain] at *)
  bench_stage "smtSimp" (veil_simp +instances only [smtSimp] at *)
  bench_stage "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain] at *)
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--depths', nargs='+', type=int, default=[4, 8, 16, 32])
    parser.add_argument('--modes', nargs='+', choices=['current', 'early', 'local'],
                        default=['current', 'early', 'local'])
    parser.add_argument('--timeout', type=int, default=120)
    args = parser.parse_args()
    if any(depth < 2 for depth in args.depths):
        parser.error('depths must be at least 2')

    repo = Path(__file__).resolve().parents[2]
    out = repo / '.veil.tmp/issue123/ring'
    out.mkdir(parents=True, exist_ok=True)
    model = (repo / 'Examples/Ivy/Ring.lean').read_text()
    model = model.split('veil module Ring', 1)[1]
    model = model.split('set_option veil.smt.trust false', 1)[0]
    for mode in args.modes:
        for depth in args.depths:
            stages = CURRENT
            if mode == 'early':
                stages = '  bench_stage "early_intros" veil_intros\n' + CURRENT
            elif mode == 'local':
                stages = LOCAL
            source = HEADER + 'veil module Ring\n' + model + f'''
#gen_spec
set_option maxHeartbeats 0
set_option maxRecDepth 10000
unsat trace [preprocessing_probe] {{
  any {depth} actions
  assert (∃ l, leader l)
}} by
{stages}
  sorry
end Ring
'''
            path = out / f'{mode}_{depth}.lean'
            path.write_text(source)
            print(f'{mode} depth={depth}', flush=True)
            try:
                result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=repo,
                                        capture_output=True, text=True, timeout=args.timeout)
                output = result.stdout + result.stderr
                status = f'exit={result.returncode}'
            except subprocess.TimeoutExpired as error:
                output = (error.stdout or b'') + (error.stderr or b'')
                if isinstance(output, bytes):
                    output = output.decode(errors='replace')
                status = f'timeout={args.timeout}s'
            path.with_suffix('.log').write_text(output + '\n' + status + '\n')
            for line in output.splitlines():
                if line.startswith(('STAGE ', 'FAILED ')) or 'error:' in line:
                    print('  ' + line, flush=True)
            print('  ' + status, flush=True)


if __name__ == '__main__':
    main()
