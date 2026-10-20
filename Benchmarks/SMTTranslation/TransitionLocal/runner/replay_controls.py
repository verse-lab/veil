#!/usr/bin/env python3
"""Separate repeated native replays for paired feasibility changes; never alter primary data."""
from pathlib import Path
import argparse,csv,copy,hashlib,json,subprocess,sys
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=root);ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--repeats',type=int,default=3);args=ap.parse_args();root=args.root.resolve()
if not (root/'completed.json').exists():raise SystemExit('Primary sweep must finish first')
rows=list(csv.DictReader((root/'results/runs.csv').open()))
idx={(r['model'],r['depth'],r['variant']):r for r in rows}
selected=[]
for a in rows:
 if a['variant']!='early':continue
 b=idx[a['model'],a['depth'],'local']
 da=a['solver_status'] in ['sat','unsat'];db=b['solver_status'] in ['sat','unsat']
 if da!=db and a['translation_status']==b['translation_status']=='complete':selected.append((a,b,'paired_definite_change'))
 elif a['translation_status']!='complete' and b['translation_status']=='complete':selected.append((None,b,'new_query'))
 elif da and db and min(int(a['solver_ms']),int(b['solver_ms']))>0 and max(int(a['solver_ms']),int(b['solver_ms']))>=500 and max(int(a['solver_ms']),int(b['solver_ms']))/min(int(a['solver_ms']),int(b['solver_ms']))>=5:selected.append((a,b,'paired_solver_time_ratio_at_least_5'))
out=root/'solver-controls';out.mkdir(exist_ok=True)
(out/'selection.json').write_text(json.dumps([{'model':b['model'],'depth':int(b['depth']),'reason':why,'primary_early':a['solver_status'] if a else None,'primary_local':b['solver_status']} for a,b,why in selected],indent=2)+'\n')
print('SELECTED',len(selected),flush=True)
all_results=[]
for repeat in range(1,args.repeats+1):
 dest=out/f'repeat-{repeat}';(dest/'cells').mkdir(parents=True,exist_ok=True)
 ids=[]
 for a,b,_ in selected:
  pair=[r for r in [a,b] if r]
  if repeat%2==0:pair.reverse()
  for row in pair:
   key=row['cell_id'];ids.append(key)
   cell=json.loads((root/'results/cells'/(key+'.json')).read_text())
   r=cell['row'];q=Path(r['query_path'])
   if hashlib.sha256(q.read_bytes()).hexdigest()!=r['query_sha256']:raise SystemExit('query hash changed')
   for k in ['solver_status','solver_ms','solver_exit','solver_timeout','solver_process_wall_ms','solver_log','completed_total_ms','failure_phase','failure_kind','failure_message']:r[k]=None
   r['status']='query_ready'
   cell.pop('solver_events',None);cell.pop('solver_execution',None)
   (dest/'cells'/(key+'.json')).write_text(json.dumps(cell,indent=2)+'\n')
 (dest/'requested-cells.json').write_text(json.dumps(ids)+'\n')
 command=[sys.executable,str(Path(__file__).resolve().parent/'solve_batch.py'),'--repo',str(args.repo),'--out',str(dest)]
 with (dest/'orchestration.log').open('w') as f:subprocess.run(command,stdout=f,stderr=subprocess.STDOUT,check=True)
 for p in sorted((dest/'cells').glob('*.json')):
  r=json.loads(p.read_text())['row']
  all_results.append({k:r.get(k) for k in ['cell_id','model','depth','variant','solver_status','solver_ms','query_sha256']}|{'repeat':repeat})
 print('DONE REPEAT',repeat,flush=True)
if all_results:
 with (out/'replays.csv').open('w') as f:
  w=csv.DictWriter(f,fieldnames=list(all_results[0]));w.writeheader();w.writerows(all_results)
(out/'summary.json').write_text(json.dumps({'repeats':args.repeats,'selected_pairs_or_new_queries':len(selected),'replays':len(all_results),'rows':all_results},indent=2)+'\n')
