#!/usr/bin/env python3
import csv,json,statistics,sys
from collections import Counter
from pathlib import Path
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
root=ap.parse_args().root.resolve()
sys.path.insert(0,str(root/'report-tools'))
import pipeline_work
rows=list(csv.DictReader((root/'results/runs.csv').open()))
index={(r['model'],int(r['depth']),r['variant']):r for r in rows}
pipeline_work.enrich(root/'results',index)
summary={}
for v in ['early','local']:
 rs=[r for r in rows if r['variant']==v]
 summary[v]={'cells':len(rs),'statuses':dict(Counter(r['status'] for r in rs)),
  'emitted':sum(r['translation_status']=='complete' for r in rs),
  'emitted_by_depth':{d:sum(r['translation_status']=='complete' and int(r['depth'])==d for r in rs) for d in [1,2,4,8,16,32]},
  'files_emitting':len({r['model'] for r in rs if r['translation_status']=='complete'}),
  'definite_solver':sum(r['solver_status'] in ['sat','unsat'] for r in rs),
  'files_definite_solver':len({r['model'] for r in rs if r['solver_status'] in ['sat','unsat']}),
  'simp_step_cells':[(r['model'],int(r['depth']),r['failure_phase']) for r in rs if r['failure_kind']=='simp_steps'],
  'failure_counts':[{'phase':p,'kind':k,'count':n} for (p,k),n in sorted(Counter((r['failure_phase'],r['failure_kind']) for r in rs if r['translation_status'] in ['failed','timeout']).items())]}
gains=[];losses=[];verdict_gains=[];verdict_losses=[];matched=[]
for (m,d,v),a in index.items():
 if v!='early':continue
 b=index[m,d,'local']
 if b['translation_status']=='complete' and a['translation_status']!='complete':gains.append([m,d,a['failure_phase'],a['failure_kind'],b['solver_status']])
 if a['translation_status']=='complete' and b['translation_status']!='complete':losses.append([m,d,b['failure_phase'],b['failure_kind']])
 da=a['solver_status'] in ['sat','unsat'];db=b['solver_status'] in ['sat','unsat']
 if db and not da:verdict_gains.append([m,d,a['status'],b['solver_status'],b['solver_ms']])
 if da and not db:verdict_losses.append([m,d,a['solver_status'],a['solver_ms'],b['status']])
 if a.get('pipeline_wall_ms') and b.get('pipeline_wall_ms'):matched.append(a['pipeline_wall_ms']/b['pipeline_wall_ms'])
summary.update(query_gains=gains,query_losses=losses,definite_solver_gains=verdict_gains,definite_solver_losses=verdict_losses,
 matched_pipeline_wall={'pairs':len(matched),'median_ratio':statistics.median(matched) if matched else None,'minimum_ratio':min(matched) if matched else None,'maximum_ratio':max(matched) if matched else None,'faster_local':sum(x>1 for x in matched),'slower_local':sum(x<1 for x in matched)})
(root/'result-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
