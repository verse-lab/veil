"""Full-pipeline wall times and summed completed-phase allocation counters."""
import csv,json,math,statistics
from pathlib import Path

VEIL={'early_intros','split_trace','nextSimp','hoist','prepare_hints','intros','destruct','dsimp1','smtSimp','dsimp2','check_hints'}

def enrich(results,indexed):
 for row in indexed.values():
  path=results/'cells'/(row.get('cell_id','')+'.json')
  if not path.exists():continue
  events=json.loads(path.read_text()).get('events',[])
  pre=next((e for e in events if e['event']=='milestone' and e['phase']=='preprocessing' and e['status']=='complete'),None)
  done=next((e for e in events if e['event']=='pipeline' and e['status']=='complete'),None)
  if pre:
   row['preprocessing_wall_ms']=pre['elapsed_ms']
   row['preprocessing_phase_heartbeats']=sum(e.get('heartbeats',0) for e in events if e['event']=='stage' and e['status']=='complete' and e['phase'] in VEIL)
  if done and row.get('translation_status')=='complete':
   row['pipeline_wall_ms']=done['elapsed_ms']
   row['pipeline_phase_heartbeats']=sum(e.get('heartbeats',0) for e in events if e['event']=='stage' and e['status']=='complete')
   if row.get('solver_status') in ('sat','unsat'):
    row['vc_pipeline_solver_ms']=int(row.get('query_elaboration_ms') or 0)+done['elapsed_ms']+int(row['solver_ms'])

def pipeline_seconds(row):
 return row['pipeline_wall_ms']/1000 if row and 'pipeline_wall_ms' in row else None

def export(out,indexed):
 fields=['cell_id','model','depth','variant','translation_status','solver_status','query_elaboration_ms','preprocessing_ms','preprocessing_wall_ms','preprocessing_phase_heartbeats','query_total_ms','pipeline_wall_ms','pipeline_phase_heartbeats','solver_ms','vc_pipeline_solver_ms']
 with (out/'pipeline-work.csv').open('w') as f:
  w=csv.DictWriter(f,fieldnames=fields);w.writeheader();w.writerows({k:r.get(k,'') for k in fields} for r in indexed.values())
 pairs=[]
 for (m,d,v),a in indexed.items():
  if v!='early':continue
  b=indexed.get((m,d,'local'),{})
  entry=dict(model=m,depth=d)
  for key in ['pipeline_wall_ms','pipeline_phase_heartbeats','preprocessing_phase_heartbeats','vc_pipeline_solver_ms']:
   x,y=a.get(key),b.get(key)
   entry['early_'+key]=x if x is not None else ''
   entry['local_'+key]=y if y is not None else ''
   entry[key+'_ratio']=x/y if x is not None and y is not None and y>0 else ''
  pairs.append(entry)
 with (out/'matched-pipeline-work.csv').open('w') as f:
  w=csv.DictWriter(f,fieldnames=list(pairs[0]));w.writeheader();w.writerows(pairs)
 summary={}
 for key in ['pipeline_wall_ms','pipeline_phase_heartbeats','preprocessing_phase_heartbeats','vc_pipeline_solver_ms']:
  xs=[p[key+'_ratio'] for p in pairs if isinstance(p[key+'_ratio'],(int,float))]
  summary[key]={'pairs':len(xs),'median_early_over_local':statistics.median(xs) if xs else None,'minimum':min(xs) if xs else None,'maximum':max(xs) if xs else None,'local_faster_pairs':sum(x>1 for x in xs),'local_slower_pairs':sum(x<1 for x in xs)}
 summary['pipeline_wall_by_depth']={}
 for d in [1,2,4,8,16,32]:
  xs=[p['pipeline_wall_ms_ratio'] for p in pairs if p['depth']==d and isinstance(p['pipeline_wall_ms_ratio'],(int,float))]
  summary['pipeline_wall_by_depth'][str(d)]={'pairs':len(xs),'median_early_over_local':statistics.median(xs) if xs else None,'local_faster':sum(x>1 for x in xs),'local_slower':sum(x<1 for x in xs),'equal':sum(x==1 for x in xs)}
 summary['limits']='Phase heartbeat sums exclude allocations between phases; full pipeline wall includes dispatch and event IO. VC + pipeline + solver excludes setup and Lean proof/model reconstruction. One observation per cell. Ratios are only for matched completed work.'
 (out/'pipeline-work-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
 return pairs

def plot(plt,out,pairs,save):
 fig,axes=plt.subplots(1,3,figsize=(16,5.8))
 fields=[('pipeline_wall_ms',1000,'Complete query pipeline wall time','seconds'),('pipeline_phase_heartbeats',1e6,'Allocation heartbeats inside completed phases','millions of raw heartbeats'),('vc_pipeline_solver_ms',1000,'VC + pipeline + definite solver call','seconds')]
 for ax,(key,div,title,unit) in zip(axes,fields):
  good=[p for p in pairs if isinstance(p['early_'+key],(int,float)) and isinstance(p['local_'+key],(int,float)) and p['early_'+key]>0 and p['local_'+key]>0]
  for d,c in zip([1,2,4,8,16,32],plt.cm.viridis([i/5 for i in range(6)])):
   group=[p for p in good if p['depth']==d]
   if group:ax.scatter([p['early_'+key]/div for p in group],[p['local_'+key]/div for p in group],s=20,color=c,label=f'depth {d}',alpha=.75)
  values=[p[v+'_'+key]/div for p in good for v in ['early','local']]
  if values:
   lo,hi=min(values)*.7,max(values)*1.4
   ax.plot([lo,hi],[lo,hi],color='#9aa6b1',ls='--',lw=1);ax.set_xscale('log');ax.set_yscale('log');ax.set_xlim(lo,hi);ax.set_ylim(lo,hi)
  ax.set_title(title+'\n'+str(len(good))+' matched pairs',fontsize=10);ax.set_xlabel('Early introduction · '+unit);ax.set_ylabel('Per-transition · '+unit);ax.grid(alpha=.35)
 axes[0].legend(fontsize=7,frameon=False)
 fig.suptitle('Full query cost and allocation work',fontsize=17,x=.035,ha='left',y=.98)
 fig.text(.035,.91,'Below the diagonal favors per-transition normalization. Failed work is excluded; see the corpus outcomes for coverage.',fontsize=9)
 fig.subplots_adjust(left=.07,right=.98,bottom=.16,top=.78,wspace=.35)
 save(fig,out,'pipeline-wall-and-work')
