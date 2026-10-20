#!/usr/bin/env python3
"""Render the exact-cache benchmark, retaining failed cases and cold setup cost."""
from pathlib import Path
from collections import Counter,defaultdict
import csv,json,statistics,math,html,shutil
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np
H=Path(__file__).resolve().parent; R=H/'results'; O=H/'report'; O.mkdir(exist_ok=True);(O/'models').mkdir(exist_ok=True)
MODELS=json.loads((H/'manifest.json').read_text()); DEPTHS=[1,2,4,8,16,32];V=['local','cached']; COLORS={'local':'#64748b','cached':'#00856a'}
rows=[]
for p in sorted((R/'cells').glob('*.json')):
 c=json.loads(p.read_text());r=c['row'];e=c.get('events',[])
 complete=[x for x in e if x['event']=='stage' and x['status']=='complete']
 pipeline=next((x for x in e if x['event']=='pipeline' and x['status'] in ['complete','discharged']),None)
 r['pipeline_wall_ms']=pipeline['elapsed_ms'] if pipeline else None
 phases=['nextSimp','hoist'] if r['variant']=='local' else ['cached_normalize']
 norm=[x for x in complete if x['phase'] in phases]
 r['normalization_ms']=sum(x['elapsed_ms'] for x in norm) if len(norm)==len(phases) else None
 r['normalization_allocations']=sum(x['heartbeats'] for x in norm) if len(norm)==len(phases) else None
 r['pipeline_allocations']=sum(x.get('heartbeats',0) for x in complete) if pipeline else None
 r['cold_to_query_ms']=sum(r.get(x) or 0 for x in ['batch_setup_ms','query_elaboration_ms','pipeline_wall_ms']) if pipeline else None
 r['complete_with_solver_ms']=r['pipeline_wall_ms']+r['query_elaboration_ms']+r['solver_ms'] if r['solver_status'] in ['sat','unsat'] else None
 rows.append(r)
idx={(r['model'],r['depth'],r['variant']):r for r in rows}
assert len(rows)==588
assert all(r['status'] not in ['not_started','query_ready'] for r in rows)
def median(xs): return statistics.median(xs) if xs else None
def paired(field,depth=None):
 result=[]
 for m in MODELS:
  for d in DEPTHS:
   if depth and d!=depth:continue
   a,b=(idx[m['model'],d,v] for v in V)
   if a[field] is not None and b[field] is not None and b[field]>0:result.append(a[field]/b[field])
 return result
def verdict(r):return 'unsat' if r['status']=='unsat_preprocessing' else r['solver_status'] if r['solver_status'] in ['sat','unsat'] else None
def emitted(r):return r['translation_status']=='complete'
summary={'models':len(MODELS),'depths':DEPTHS,'cells':len(rows),'variants':{},'paired_speedups':{},'gains':[],'losses':[],'new_queries':[],'lost_queries':[],'disagreements':[]}
for v in V:
 rs=[r for r in rows if r['variant']==v]
 summary['variants'][v]={'emitted':sum(map(emitted,rs)),'native_accepted':sum(r['solver_status'] in ['sat','unsat','timeout','unknown'] for r in rs),'definite':sum(verdict(r)!=None for r in rs),'statuses':dict(Counter(r['status'] for r in rs)),'failure_phases':dict(Counter(r['failure_phase'] for r in rs if r['failure_phase'])),'failure_kinds':dict(Counter(r['failure_kind'] for r in rs if r['failure_kind']))}
for field in ['normalization_ms','normalization_allocations','pipeline_wall_ms','pipeline_allocations','cold_to_query_ms','complete_with_solver_ms']:
 xs=paired(field);summary['paired_speedups'][field]={'pairs':len(xs),'median':median(xs),'faster':sum(x>1 for x in xs),'slower':sum(x<1 for x in xs)}
for m in MODELS:
 for d in DEPTHS:
  a,b=(idx[m['model'],d,v] for v in V);key={'model':m['model'],'depth':d,'local':a['status'],'cached':b['status']}
  if emitted(b) and not emitted(a):summary['new_queries'].append(key)
  if emitted(a) and not emitted(b):summary['lost_queries'].append(key)
  if verdict(b) and not verdict(a):summary['gains'].append(key)
  if verdict(a) and not verdict(b):summary['losses'].append(key)
  if verdict(a) and verdict(b) and verdict(a)!=verdict(b):summary['disagreements'].append(key)
assert not summary['disagreements']
setups=[]
for m in MODELS:
 a,b=(idx[m['model'],1,v] for v in V)
 setups.append({'model':m['model'],'local_ms':a['batch_setup_ms'],'cached_ms':b['batch_setup_ms'],'difference_ms':b['batch_setup_ms']-a['batch_setup_ms'] if a['batch_setup_ms'] is not None and b['batch_setup_ms'] is not None else None})
summary['cold_setup']={'pairs':sum(x['difference_ms'] is not None for x in setups),'median_added_ms':median([x['difference_ms'] for x in setups if x['difference_ms'] is not None]),'note':'Separate fresh model/variant processes. One sample; includes model elaboration/imports, so differences include noise.'}
for name,data in [('measurements',rows),('setup',setups)]:
 with (O/(name+'.csv')).open('w') as f:w=csv.DictWriter(f,fieldnames=list(data[0]));w.writeheader();w.writerows(data)
(O/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False,'figure.dpi':125})
def finish(fig,path):
 fig.savefig(path.with_suffix('.png'),bbox_inches='tight');fig.savefig(path.with_suffix('.svg'),bbox_inches='tight');plt.close(fig)
def graphaxis(ax,title):
 ax.set_title(title,loc='left',fontweight='bold');ax.set_xscale('log',base=2);ax.set_xticks(DEPTHS,DEPTHS);ax.set_xlabel('Exact number of actions');ax.grid(alpha=.16)
fig,axs=plt.subplots(2,2,figsize=(12,8),layout='constrained')
for ax,field,title in [(axs[0,0],'normalization_ms','Normalization: median paired speedup'),(axs[0,1],'pipeline_wall_ms','Complete query production: median paired speedup')]:
 ys=[median(paired(field,d)) or np.nan for d in DEPTHS];ax.plot(DEPTHS,ys,'o-',color=COLORS['cached']);ax.axhline(1,color=COLORS['local'],ls='--');graphaxis(ax,title);ax.set_ylabel('Uncached / cached (higher is better)')
 for d,y in zip(DEPTHS,ys):ax.annotate(f'n={len(paired(field,d))}',(d,y),xytext=(0,8),textcoords='offset points',ha='center',fontsize=8)
for v in V:
 axs[1,0].plot(DEPTHS,[sum(emitted(r) for r in rows if r['variant']==v and r['depth']==d) for d in DEPTHS],'o-',label=v,color=COLORS[v])
 axs[1,1].plot(DEPTHS,[sum(verdict(r)!=None for r in rows if r['variant']==v and r['depth']==d) for d in DEPTHS],'o-',label=v,color=COLORS[v])
for ax,title in [(axs[1,0],'Emitted queries, out of 49 models'),(axs[1,1],'Definite answers within the 10-second solver limit')]:graphaxis(ax,title);ax.set_ylim(0,49);ax.legend()
fig.suptitle('Exact transition caching vs per-transition normalization',fontsize=16);finish(fig,O/'overview')
fig,ax=plt.subplots(figsize=(11,15),layout='constrained');y=np.arange(len(setups))
ax.barh(y-.18,[(x['local_ms'] if x['local_ms'] is not None else np.nan)/1000 for x in setups],.35,label='local',color=COLORS['local']);ax.barh(y+.18,[(x['cached_ms'] if x['cached_ms'] is not None else np.nan)/1000 for x in setups],.35,label='cached',color=COLORS['cached'])
for v,offset in [('local',-.18),('cached',.18)]:
 for i,x in enumerate(setups):
  if x[v+'_ms'] is None:
   ax.scatter([60],[i+offset],marker='>',facecolors='none',edgecolors=COLORS[v],s=65)
   ax.annotate('setup timeout', (60,i+offset),xytext=(-8,-10 if offset>0 else 6),textcoords='offset points',ha='right',fontsize=7)
ax.set_yticks(y,[x['model'] for x in setups],fontsize=8);ax.invert_yaxis();ax.set_xlabel('Cold model setup, seconds (one sample each; ▷ timeout at 60 s)');ax.set_title('Setup cost is paid before the trace queries');ax.legend();finish(fig,O/'setup-cost')
# Show where time remains at the largest sampled depth, only when both query
# production runs completed. This avoids comparing a failure cap with a timing.
phase_map={}
for p in (R/'cells').glob('*.json'):
 c=json.loads(p.read_text());r=c['row']
 phase_map[r['model'],r['depth'],r['variant']]={e['phase']:e['elapsed_ms']/1000 for e in c.get('events',[]) if e['event']=='stage' and e['status']=='complete'}
matched=[m['model'] for m in MODELS if all(idx[m['model'],32,v]['pipeline_wall_ms'] is not None for v in V)]
matched.sort(key=lambda m:idx[m,32,'local']['pipeline_wall_ms'],reverse=True)
categories=[('Unfold + hoist',['nextSimp','hoist','cached_normalize']),('Destruct context',['destruct']),('Field dsimp',['dsimp1','dsimp2']),('SMT simplification',['smtSimp']),('Backend + serialize',['cleanup','pushHints','smt-intros','negateGoal','normalize','embedding','translate','serialize']),('Other overhead',[])]
if matched:
 fig,ax=plt.subplots(figsize=(12,max(6,len(matched)*.6)),layout='constrained')
 labels=[];values=[]
 for m in matched:
  for v in V:
   phases=phase_map[m,32,v];parts=[sum(phases.get(x,0) for x in names) for name,names in categories[:-1]]
   parts.append(max(0,idx[m,32,v]['pipeline_wall_ms']/1000-sum(parts)));values.append(parts);labels.append(m+' / '+v)
 data=np.array(values);left=np.zeros(len(labels));palette=['#00856a','#e09f55','#91b9cd','#9b83c6','#d26a80','#bcc6c2']
 for j,(name,names) in enumerate(categories):
  ax.barh(np.arange(len(labels)),data[:,j],left=left,label=name,color=palette[j]);left+=data[:,j]
 ax.set_yticks(np.arange(len(labels)),labels,fontsize=8);ax.invert_yaxis();ax.set_xlabel('Complete query-production seconds at depth 32');ax.set_title('Remaining work after caching — matched completed queries');ax.legend(loc='upper left',bbox_to_anchor=(1.01,1),fontsize=8);finish(fig,O/'phase-costs')
CSS='''body{max-width:1250px;margin:35px auto;padding:0 24px;font:16px/1.5 system-ui;color:#162a35;background:#fafcfb}h1,h2{line-height:1.2}a{color:#007562}img{max-width:100%;background:white}table{border-collapse:collapse;width:100%;font-size:13px}th,td{padding:8px;border-bottom:1px solid #dbe4df;text-align:left;vertical-align:top}th{background:#e9f0ed}code{background:#edf1ef;padding:2px 5px}.note{background:#edf3f0;padding:18px;border-left:4px solid #00856a}details{margin:12px 0}pre{white-space:pre-wrap;overflow-wrap:anywhere}nav{display:flex;gap:15px;flex-wrap:wrap}.gallery{display:grid;grid-template-columns:repeat(auto-fit,minmax(330px,1fr));gap:20px}.gallery a{background:white;padding:10px;text-decoration:none;border:1px solid #dbe4df}'''
def document(title,body):return '<!doctype html><meta charset="utf-8"><meta name="viewport" content="width=device-width"><title>'+html.escape(title)+'</title><style>'+CSS+'</style>'+body
E=html.escape
def num(x):return '—' if x is None else f'{x/1000:.3f}'
def table(headers,data):return '<table><thead><tr>'+''.join('<th>'+E(x)+'</th>' for x in headers)+'</tr></thead><tbody>'+''.join('<tr>'+''.join('<td>'+str(x)+'</td>' for x in row)+'</tr>' for row in data)+'</tbody></table>'
status_colors={'sat':'#7dbcde','unsat':'#70b594','unsat_preprocessing':'#bad8a6','solver_timeout':'#f0bd72','solver_error':'#e095a1','translation_failed':'#c5c9ce','blocked_model_setup':'#c5a6d1'}
for m in MODELS:
 key=m['model'];rs=[idx[key,d,v] for d in DEPTHS for v in V]
 fig,axs=plt.subplots(2,2,figsize=(12,7.8),layout='constrained')
 for ax,field,title in [(axs[0,0],'normalization_ms','Unfolding + witness hoisting'),(axs[0,1],'pipeline_wall_ms','Complete query production'),(axs[1,0],'solver_ms','Native cvc5 replay')]:
  for v in V:
   xs=[];ys=[]
   for d in DEPTHS:
    r=idx[key,d,v];t=r[field]
    ok=t is not None and (field!='solver_ms' or verdict(r)!=None)
    xs.append(d);ys.append(max(t/1000,.001) if ok else np.nan)
    if field=='solver_ms' and r['solver_status'] in ['timeout','process_timeout']:
     ax.scatter([d],[10],marker='^',facecolors='none',edgecolors=COLORS[v],s=65)
   ax.plot(xs,ys,'o-',label=v,color=COLORS[v])
  graphaxis(ax,title);ax.set_ylabel('Seconds (log scale)')
  have_points=any(r[field] is not None and (field!='solver_ms' or verdict(r)!=None) for r in rs)
  if not have_points:
   ax.set_ylim(.001,20)
   ax.text(.5,.5,'No completed timings',transform=ax.transAxes,ha='center',color='#64748b')
  ax.set_yscale('log');ax.legend()
  if field=='solver_ms':ax.axhline(10,color='#aaa',ls=':',lw=1);ax.text(.02,.02,'△ solver timeout; not a completed timing',transform=ax.transAxes,fontsize=8)
 ax=axs[1,1];ax.axis('off');grid=[];colors=[]
 for v in V:
  grid.append([idx[key,d,v]['status'].replace('translation_failed','TRANSL.').replace('blocked_model_setup','SETUP').replace('unsat_preprocessing','PRE').replace('solver_timeout','TIMEOUT').replace('solver_error','ERROR') for d in DEPTHS]);colors.append([status_colors.get(idx[key,d,v]['status'],'#ddd') for d in DEPTHS])
 t=ax.table(cellText=grid,rowLabels=V,colLabels=[str(d) for d in DEPTHS],cellColours=colors,loc='upper center',cellLoc='center');t.auto_set_font_size(False);t.set_fontsize(7);t.scale(1,1.7)
 setup=next(x for x in setups if x['model']==key)
 setup_label=lambda ms: ">=60 s (timeout)" if ms is None else num(ms)+" s"
 ax.text(0,.58,f"Cold setup: local {setup_label(setup['local_ms'])}; cached {setup_label(setup['cached_ms'])}",transform=ax.transAxes,fontsize=9)
 ax.text(0,.39,'Missing points are failures, not zero cost.\nNormalization timings remain visible when a later stage fails.\nQuery production excludes setup, VC elaboration and solving.\nOne observation per model, depth and variant.',transform=ax.transAxes,fontsize=9,va='top')
 fig.suptitle(key,fontsize=16);finish(fig,O/'models'/key)
 body=f'<nav><a href="../index.html">All models</a><a href="{key}.svg">SVG figure</a></nav><h1>{E(key)}</h1><p><code>{E(m["path"])}</code> · <code>{E(m["query"])}</code></p><img src="{key}.png">'
 data=[]
 for r in rs:
  stem=r['cell_id'];q=f'<a href="../../raw/queries/{Path(r["query_path"]).name}">SMT-LIB</a>' if emitted(r) else ''
  log=f'<a href="../../raw/logs/{Path(r["translation_log"]).name}">log</a>'
  data.append([r['depth'],r['variant'],E(r['status']),num(r['normalization_ms']),num(r['pipeline_wall_ms']),num(r['query_elaboration_ms']),num(r['cold_to_query_ms']),num(r['solver_ms']),E(str(r['failure_phase'] or '')),E(str(r['failure_kind'] or '')),q+' '+log])
 body+=table(['Depth','Variant','Result','Normalize s','Query s','VC s','Cold→query s','Solver s','Stopped at','Failure kind','Evidence'],data)
 for r in rs:
  if r['failure_message']:body+=f'<details><summary>{r["depth"]}, {r["variant"]}: {E(str(r["failure_kind"]))}</summary><pre>{E(r["failure_message"])}</pre></details>'
 (O/'models'/(key+'.html')).write_text(document(key,body))
body='<h1>Exact transition normalization cache</h1><p>Paired benchmark against per-transition normalization: 49 models × 6 depths × 2 variants, with cold setup and native cvc5 replay.</p><nav><a href="measurements.csv">Measurements CSV</a><a href="summary.json">Summary JSON</a><a href="setup-cost.svg">Setup figure</a><a href="../METHODS.txt">Methods</a><a href="../IMPLEMENTATION.txt">Implementation and semantics</a></nav>'
body+='<div class="note">'+E((H/'EXECUTIVE_SUMMARY.txt').read_text()) .replace('\n','<br>')+'</div>' if (H/'EXECUTIVE_SUMMARY.txt').exists() else ''
body+='<img src="overview.png" alt="Aggregate paired speedups and completion counts">'
body+=table(['Outcome','Per-transition','Cached'],[[k,summary['variants']['local'][k],summary['variants']['cached'][k]] for k in ['emitted','native_accepted','definite']])
for category,title in [('failure_phases','Stopping phases'),('failure_kinds','Failure kinds')]:
 keys=sorted(set(summary['variants']['local'][category])|set(summary['variants']['cached'][category]))
 body+=f'<h2>{title}</h2>'+table(['Failure','Per-transition','Cached'],[[E(k),summary['variants']['local'][category].get(k,0),summary['variants']['cached'][category].get(k,0)] for k in keys])
body+='<p>A stopping phase identifies where the budget ran out or an error appeared; it does not assign all earlier work to that phase.</p>'
body+='<h2>Paired timing comparisons</h2>'+table(['Measurement','Matched pairs','Median local / cached','Faster / slower'],[[k,v['pairs'],f'{v["median"]:.3f}×' if v['median'] else '—',str(v['faster'])+' / '+str(v['slower'])] for k,v in summary['paired_speedups'].items()])
body+='<p>Higher ratios mean faster cached runs. These are matched completed measurements, not averages assigning time limits to failures. Timing variability and different solver search behavior remain.</p>'
for key,title in [('new_queries','New emitted queries'),('lost_queries','Lost emitted queries'),('gains','New definite answers'),('losses','Lost definite answers')]:
 body+=f'<h2>{title}</h2>'+table(['Model','Depth','Local','Cached'],[[f'<a href="models/{x["model"]}.html">{x["model"]}</a>',x['depth'],x['local'],x['cached']] for x in summary[key]])
body+='<h2>Remaining phase costs at depth 32</h2><p>Both variants must complete query production to appear here.</p><img src="phase-costs.png">'
body+='<h2>Cold setup</h2><p>Separate fresh processes, cache disabled/enabled before model elaboration. Setup includes imports and specification generation. Median added setup: '+str(summary['cold_setup']['median_added_ms'])+' ms. Single samples can be noisy.</p><details><summary>All 49 setup measurements</summary><img src="setup-cost.png"></details>'
body+='<h2>Every example</h2><p>Each figure includes normalization, complete query production, solver timings, and all failure outcomes.</p><div class="gallery">'
for m in MODELS:body+=f'<a href="models/{m["model"]}.html"><strong>{m["model"]}</strong><img loading="lazy" src="models/{m["model"]}.png"></a>'
body+='</div>'
(O/'index.html').write_text(document('Veil exact BMC cache benchmark',body))
print(json.dumps(summary,indent=2))
