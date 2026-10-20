#!/usr/bin/env python3
from pathlib import Path
import argparse,collections,csv,hashlib,itertools,json,statistics
ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);root=ap.parse_args().root.resolve()
rows=list(csv.DictReader((root/'solver-controls/replays.csv').open()));primary={r['cell_id']:r for r in csv.DictReader((root/'results/runs.csv').open())}
assert len(rows)==66 and len({(r['repeat'],r['cell_id']) for r in rows})==66
assert all(r['query_sha256']==primary[r['cell_id']]['query_sha256'] for r in rows)
cs=[json.loads(p.read_text()) for p in (root/'step-profile/results/cells').glob('*.json')]
assert len(cs)==36 and len({(c['row']['model'],c['row']['depth'],c['row']['variant']) for c in cs})==36
assert collections.Counter(c['row']['status'] for c in cs)=={'profile_complete':31,'translation_failed':5}
for c in cs:
 if c['row']['status']=='profile_complete':
  for phase in ['nextSimp','hoist']:assert any(e['event']=='simp_work' and e['phase']==phase and e['steps']>0 and e['calls']>0 for e in c['events'])
summary=[]
key=lambda r:(r['model'],int(r['depth']),r['variant'])
for (m,d,v),group in itertools.groupby(sorted(rows,key=key),key=key):
 rs=list(group);assert len(rs)==3
 good=[int(r['solver_ms']) for r in rs if r['solver_status'] in ['sat','unsat']]
 summary.append(dict(model=m,depth=d,variant=v,statuses=dict(collections.Counter(r['solver_status'] for r in rs)),completed_median_ms=statistics.median(good) if good else None))
assert len(summary)==22 and sum(sum(r['statuses'].values()) for r in summary)==66
extended=list(csv.DictReader((root/'solver-controls/extended-30s/runs.csv').open()));assert len(extended)==6
assert all(r['query_sha256']==primary[r['cell_id']]['query_sha256'] for r in extended)
assert all(r['solver_status'] in ['sat','unsat'] for r in extended)
for a in extended:
 b=next(x for x in extended if x['model']==a['model'] and x['variant']!=a['variant']);assert a['solver_status']==b['solver_status']
probe=list(csv.DictReader((root/'solver-order-probe/runs.csv').open()));assert len(probe)==4
assert all(r['matches_original_local'] for r in json.loads((root/'solver-order-probe/equivalence.json').read_text()))
for r in probe:
 assert hashlib.sha256((root/'solver-order-probe/queries'/Path(r['query_path']).name).read_bytes()).hexdigest()==r['query_sha256']
result={'passed':True,'repeated_queries':66,'step_profile_cells':36,'profile_complete':31,'paired_replay_query_hashes':'match primary','extended_queries':6,'order_probes':4,'repeated_summary':summary}
(root/'diagnostic-validation.json').write_text(json.dumps(result,indent=2)+'\n')
lines=['Separate native solver diagnostics','==================================','',
 'The primary 588-cell comparison is unchanged. After it finished, twelve',
 'model/depth cases were selected deterministically: two newly emitted queries,',
 'four pairs with a definite-result change, and six pairs whose observed solver',
 'times differed by at least 5x with the slower call at least 500 ms. Each selected',
 'emitted query was replayed three times in a fresh native solver; pair order',
 'alternates between repeats. These 66 calls use the same emitted query hashes',
 'and 10-second checkSat / 15-second wrapper limits. No other Lean, graph-rendering',
 'or solver jobs ran concurrently. This is a targeted diagnostic, not a repeated',
 'sample of the whole corpus or a confidence interval.','',
 'Repeated results (three calls per row):',
 'Model / depth / variant | outcomes | median definite-call time (seconds)']
for r in summary:
 statuses=', '.join(f'{s.upper()} {n}/3' for s,n in sorted(r['statuses'].items()))
 t='—' if r['completed_median_ms'] is None else f'{r["completed_median_ms"]/1000:.3f}'
 lines.append(f'{r["model"]} / {r["depth"]} / {r["variant"]} | {statuses} | {t}')
lines += ['', 'Medians include only definite calls, never timeout durations; mixed outcomes',
 'must be read together with their success counts. The primary measurements are',
 'not included in these three-repeat medians. Near-threshold results fluctuate:',
 'Ivy TwoPhaseCommit local finishes in one repeat at 9.747 s, and times out in two.',
 'The repeated Traffic slowdown shows that even preserved definite outcomes can',
 'cost much more solver time. There are no contradictory definite answers.','',
 'Separate 30-second checks of the three primary regressions:',
 'Model / variant | result | native seconds']
for r in extended:lines.append(f'{r["model"]} / {r["variant"]} | {r["solver_status"].upper()} | {int(r["solver_ms"])/1000:.3f}')
lines += ['', 'All three local queries return the same answer as their baselines at this',
 'larger cap. This shows that cvc5 can handle these particular encodings with',
 'more time; it does not erase their regressions under the fixed primary cap.','',
 'Controlled ordering/grouping experiment: Ivy TwoPhaseCommit depth 8',
 'The original early/local scripts contain the same multiset of 129 declarations',
 'but 3 versus 13 assertions. Four local-derived scripts were generated:',
 '  1. Move all local declarations before assertions, retaining their order.',
 '  2. Use the baseline declaration order, retaining local assertion grouping.',
 '  3. Use local declaration order and conjoin every assertion into one.',
 '  4. Use baseline declaration order and conjoin every assertion into one.',
 'The scope-aware formula audit independently verifies each script against the',
 'original local script before native replay. The exact texts/hashes are kept.']
for r in probe:lines.append(f'  {r["model"]}: {r["solver_status"]} ({int(r["solver_ms"])/1000:.3f} s)')
lines += ['', 'All four reach the 10-second solver limit. These limited reorganizations do',
 'not restore the baseline result. They neither isolate a particular heuristic',
 'as the cause nor rule out a better encoding; finer formula structure, witness',
 'names and preprocessing/search decisions may matter. Do not claim declaration',
 'sorting or assertion merging alone is a validated fix. A follow-up should',
 'profile solver preprocessing and quantifier instantiation, then benchmark any',
 'encoding policy across the corpus before making it the default. Keeping a',
 'user-selectable early-introduction strategy during rollout would be prudent.',
 'No such policy/option is implemented in this change.','',
 'Evidence: solver-controls/selection.json, replays.csv, repeat-*/events and',
 'solver source files; solver-controls/extended-30s; solver-order-probe/queries,',
 'equivalence.json and runs.csv. Diagnostic timings are separate from primary',
 'outcome matrices and main per-model curves.']
(root/'SOLVER_BEHAVIOR.txt').write_text('\n'.join(lines)+'\n')
print(json.dumps(result,indent=2))
