#!/usr/bin/env python3
import csv,json,statistics
from pathlib import Path
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
root=ap.parse_args().root.resolve()
out=root/'step-profile';results=out/'results'
rows=[]
for path in sorted((results/'cells').glob('*.json')):
 cell=json.loads(path.read_text());r=cell['row'];events=cell.get('events',[])
 for phase in ['nextSimp','hoist']:
  event=next((e for e in events if e['event']=='simp_work' and e['phase']==phase and e['status']=='complete'),None)
  stage=next((e for e in events if e['event']=='stage' and e['phase']==phase and e['status']=='complete'),None)
  rows.append(dict(model=r['model'],depth=r['depth'],variant=r['variant'],phase=phase,complete=bool(event and stage),steps=event['steps'] if event and stage else '',calls=event['calls'] if event and stage else '',phase_heartbeats=stage.get('heartbeats','') if stage else '',profile_status=r['status']))
with (out/'simp-work.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
index={(r['model'],r['depth'],r['variant'],r['phase']):r for r in rows}
pairs=[]
for r in rows:
 if r['variant']!='early':continue
 b=index[r['model'],r['depth'],'local',r['phase']]
 if not (r['complete'] and b['complete']):continue
 pairs.append(dict(model=r['model'],depth=r['depth'],phase=r['phase'],early_steps=r['steps'],local_steps=b['steps'],step_ratio=r['steps']/b['steps'] if b['steps'] else '',early_calls=r['calls'],local_calls=b['calls']))
with (out/'matched-simp-work.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(pairs[0]));w.writeheader();w.writerows(pairs)
summary={p:dict(pairs=len(xs:=[r for r in pairs if r['phase']==p]),median_early_over_local=statistics.median([r['step_ratio'] for r in xs if isinstance(r['step_ratio'],(int,float))])) for p in ['nextSimp','hoist']}
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
models=sorted({r['model'] for r in rows})
fig,axes=plt.subplots(len(models),2,figsize=(12,3.2*len(models)),squeeze=False)
for i,model in enumerate(models):
 for j,phase in enumerate(['nextSimp','hoist']):
  ax=axes[i,j]
  for v,color in [('early','#C65336'),('local','#176F91')]:
   points=sorted([(r['depth'],r['steps']) for r in rows if r['model']==model and r['phase']==phase and r['variant']==v and r['complete'] and r['steps']>0])
   if points:ax.plot([x[0] for x in points],[x[1] for x in points],'-o',color=color,label=v)
  ax.set_title(model+' · '+phase+(' (guard only; no HO witness)' if model=='Ivy_Ring' and phase=='hoist' else ''),fontsize=10);ax.set_xscale('log',base=2);ax.set_yscale('log');ax.set_xticks([1,2,4,8,16,32],labels=[1,2,4,8,16,32]);ax.set_xlabel('Exact actions');ax.set_ylabel('Sum of completed simp-run counters');ax.grid(alpha=.25);ax.legend(frameon=False,fontsize=8)
fig.suptitle('Normalization work, including inner and outer simp runs',x=.04,ha='left',fontsize=16,y=.995)
fig.text(.04,.965,'Separate tracing experiment. Failed/incomplete phases are omitted. Per-call caps reset; no per-transition heartbeat reset.',fontsize=9)
fig.tight_layout(rect=[0,0,1,.94])
for ext in ['png','svg']:fig.savefig(out/('simp-work.'+ext),dpi=160,bbox_inches='tight')
print(json.dumps(summary))
