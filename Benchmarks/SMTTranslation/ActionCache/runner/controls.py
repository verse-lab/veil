#!/usr/bin/env python3
"""Separate native replay controls after the primary benchmark (never pooled)."""
from pathlib import Path
import json,subprocess,sys,copy
import run
H=Path(__file__).resolve().parent;ROOT=Path('/home/george/src/veil-issue-123');primary=H/'results';out=H/'controls';out.mkdir(exist_ok=True)
cells=[json.loads(p.read_text()) for p in (primary/'cells').glob('*.json')];idx={(c['row']['model'],c['row']['depth'],c['row']['variant']):c for c in cells}
def definite(c):return c['row']['solver_status'] in ['sat','unsat']
selected=[]
for key,c in sorted(idx.items()):
 if key[2]!='local':continue
 other=idx[key[0],key[1],'cached']
 if all(x['row']['translation_status']=='complete' and x['row']['solver_status']!='error' for x in [c,other]):
  if definite(c)!=definite(other):selected.append((c,other,'primary definite/timeout difference'))
  elif all(definite(x) for x in [c,other]):
   a,b=c['row']['solver_ms'],other['row']['solver_ms']
   if a>=200 and b>=max(a*3,1000):selected.append((c,other,'primary solver slowdown >=3x and >=1s'))
selection=[{'model':a['row']['model'],'depth':a['row']['depth'],'reason':why} for a,b,why in selected]
(out/'selection.json').write_text(json.dumps(selection,indent=2)+'\n')
def stage(name,items,cap):
 target=out/name;(target/'cells').mkdir(parents=True,exist_ok=True);requested=[]
 for orig,rep,why in items:
  c=copy.deepcopy(orig);r=c['row'];original=r['cell_id'];r['cell_id']=original+f'__repeat{rep}_t{cap}'
  c['primary_cell_id']=original;c['control_reason']=why
  r.update(status='query_ready',solver_status=None,solver_ms=None,solver_log=None,completed_total_ms=None,failure_phase=None,failure_kind=None,failure_message=None)
  file=target/'cells'/(r['cell_id']+'.json')
  if not file.exists():run.atomic_json(file,c)
  requested.append(r['cell_id'])
 run.atomic_json(target/'requested-cells.json',requested)
 with (target/'execution.log').open('w') as log:
  result=subprocess.run([sys.executable,str(H/'solve_batch.py'),'--repo',str(ROOT),'--out',str(target),'--solver-timeout',str(cap)],stdout=log,stderr=subprocess.STDOUT)
 if result.returncode:raise SystemExit(f'controls failed: {target}')
 return [json.loads(p.read_text()) for p in (target/'cells').glob('*.json')]
items=[]
for a,b,why in selected:
 for rep in [1,2]:
  for c in ([a,b] if rep==1 else [b,a]):items.append((c,rep,why))
# Recheck newly emitted definite answers as well as changed paired outcomes.
new_definite=[]
for (model,depth,variant),c in sorted(idx.items()):
 if variant=='cached' and definite(c) and idx[model,depth,'local']['row']['translation_status']!='complete':
  new_definite.append(c['row']['cell_id'])
  for rep in [1,2]:items.append((c,rep,'newly emitted definite query'))
(out/'new-definite-selection.json').write_text(json.dumps(new_definite,indent=2)+'\n')
repeats=stage('repeat10',items,10) if items else []
long=[]
for a,b,why in selected:
 for c in [a,b]:
  if not definite(c):long.append((c,1,'30s follow-up of '+why))
# New Blockchain depth32 previously hit the frontend budget; check native30s as a separate limit.
c=idx['Ivy_Blockchain',32,'cached']
if c['row']['translation_status']=='complete' and c['row']['solver_status']=='timeout' and not any(x[0]['row']['cell_id']==c['row']['cell_id'] for x in long):long.append((c,1,'new Blockchain32 query, native30s follow-up'))
extended=stage('extended30',long,30) if long else []
for c in repeats+extended:
 r=c['row']
 if r['solver_status'] in ['sat','unsat']:
  for v in ['local','cached']:
   known=idx[r['model'],r['depth'],v]['row']['solver_status']
   if known in ['sat','unsat'] and known!=r['solver_status']:
    raise RuntimeError('Contradictory definite control answer: '+r['cell_id'])
summary={'selected_pairs':selection,'new_definite_queries':new_definite,'repeat10':[{'primary_cell_id':c['primary_cell_id'],'cell_id':c['row']['cell_id'],'status':c['row']['status'],'solver_ms':c['row']['solver_ms']} for c in repeats],'extended30':[{'primary_cell_id':c['primary_cell_id'],'status':c['row']['status'],'solver_ms':c['row']['solver_ms']} for c in extended]}
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
