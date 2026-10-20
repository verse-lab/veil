#!/usr/bin/env python3
"""Separate 30-second native checks for primary paired solver-result regressions."""
from pathlib import Path
import argparse,csv,hashlib,json,subprocess,sys
ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--timeout',type=int,default=30);args=ap.parse_args();root=args.root.resolve()
if not (root/'completed.json').exists():raise SystemExit('Primary sweep must finish first')
rows=list(csv.DictReader((root/'results/runs.csv').open()));idx={(r['model'],r['depth'],r['variant']):r for r in rows}
selected=[]
for a in rows:
 if a['variant']!='early':continue
 b=idx[a['model'],a['depth'],'local']
 if a['solver_status'] in ['sat','unsat'] and b['solver_status'] not in ['sat','unsat'] and b['translation_status']=='complete':selected.extend([a,b])
out=root/'solver-controls'/f'extended-{args.timeout}s';out.mkdir(exist_ok=False);(out/'cells').mkdir()
ids=[]
for r in selected:
 key=r['cell_id'];ids.append(key);cell=json.loads((root/'results/cells'/(key+'.json')).read_text());row=cell['row']
 if hashlib.sha256(Path(row['query_path']).read_bytes()).hexdigest()!=row['query_sha256']:raise SystemExit('Changed query')
 for k in ['solver_status','solver_ms','solver_exit','solver_timeout','solver_process_wall_ms','solver_log','completed_total_ms','failure_phase','failure_kind','failure_message']:row[k]=None
 row['status']='query_ready';cell.pop('solver_events',None);cell.pop('solver_execution',None)
 (out/'cells'/(key+'.json')).write_text(json.dumps(cell,indent=2)+'\n')
(out/'requested-cells.json').write_text(json.dumps(ids)+'\n')
with (out/'orchestration.log').open('w') as f:subprocess.run([sys.executable,str(Path(__file__).resolve().parent/'solve_batch.py'),'--repo',str(args.repo),'--out',str(out),'--solver-timeout',str(args.timeout)],stdout=f,stderr=subprocess.STDOUT,check=True)
print((out/'runs.csv').read_text())
