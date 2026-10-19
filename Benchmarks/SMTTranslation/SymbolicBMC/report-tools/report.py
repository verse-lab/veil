#!/usr/bin/env python3
"""Report a complete symbolic-BMC depth sweep without turning failures into timings.

Requires matplotlib. One observation per cell; exact-N trace queries.
Example:
  python3 report.py --manifest ../manifest.json --exclusions ../exclusions.json \
    --results ../results --out-dir ../report
"""
from __future__ import annotations
import argparse,csv,hashlib,html,json,math,os,re,statistics,sys
from collections import Counter,defaultdict
from dataclasses import dataclass
from pathlib import Path

csv.field_size_limit(sys.maxsize)

DEPTHS=[1,2,4,8,16,32]
VARIANTS=['old','early']
VARIANT_LABEL={'old':'Original','early':'Early introduction'}
COLORS={'old':'#C65336','early':'#176F91'}
# Phase and resource kind remain separate in exported tables and cell tooltips.
STYLES={
 'sat':('SAT','#B8DECC','#164E39'),
 'unsat':('UNSAT','#B6D3EB','#163F61'),
 'discharged':('Closed in preprocessing','#8FBFB6','#163F39'),
 'query_ready':('Query ready; solver pending','#D4E4EB','#3A586A'),
 'simp_steps':('Simp step limit','#C44F4F','#FFFFFF'),
 'recursion':('Recursion limit','#E28B4B','#432313'),
 'heartbeat':('Heartbeat limit','#F1C06C','#513707'),
 'embedding':('Embedding failure','#9079B0','#FFFFFF'),
 'translation':('SMT translation failure','#C68EB5','#43233C'),
 'setup':('Model setup failure','#9EAAB5','#25333F'),
 'blocked_setup':('Not attempted: setup failed','#DFE3E7','#68747F'),
 'query_elaboration':('Query / VC elaboration failure','#BCC3A3','#344224'),
 'solver_timeout':('Solver timeout','#F2DCA2','#6A4B0D'),
 'solver_unknown':('Solver unknown','#DDC6AA','#59412B'),
 'solver_error':('Solver error','#B6957E','#FFFFFF'),
 'process_timeout':('Process timeout','#7E8992','#FFFFFF'),
 'other':('Other failure','#B6B0B9','#3B3540'),
 'not_run':('No recorded result','#F0F2F4','#727B82'),
}

def read_csv(path):
    if not path.exists():return []
    with path.open() as f:return list(csv.DictReader(f))

def read_json(path,default=None):
    return json.loads(path.read_text()) if path and path.exists() else default

def number(value):
    if value is None or value=='':return None
    try:return float(value)
    except (ValueError,TypeError):return None

def norm(value):return str(value or '').strip().lower().replace('-','_').replace(' ','_')

def phase_code(phase):
    p=norm(phase)
    if 'nextsimp' in p or 'next_simp' in p:return 'N'
    if 'hoist' in p or 'exists' in p:return 'H'
    if 'embedding' in p or p=='embed':return 'E'
    if 'normalize' in p:return 'Z'
    if 'serialize' in p:return 'W'
    if 'translate' in p or p=='translation':return 'T'
    if 'query_elab' in p or 'vc_elab' in p or p=='query':return 'V'
    if 'setup' in p or 'gen_spec' in p or 'model' in p:return 'G'
    if 'solver' in p or p=='solve':return 'Q'
    if 'smt_simp' in p or 'smtsimp' in p:return 'M'
    if 'dsimp' in p:return 'D'
    if 'destruct' in p:return 'D'
    if 'intro' in p:return 'I'
    return '?'

@dataclass(frozen=True)
class Outcome:
    family:str
    code:str
    detail:str


def classify(row):
    if row is None:return Outcome('not_run','—','No recorded result')
    status=norm(row.get('status'));solver=norm(row.get('solver_status'))
    phase=row.get('failure_phase','');kind=norm(row.get('failure_kind'))
    message=str(row.get('failure_message',''))
    joined=' '.join([status,solver,kind,message.lower()])
    p=phase_code(phase)
    if status=='blocked_model_setup':return Outcome('blocked_setup','G:—','Query not attempted because model setup failed')
    # Prefer a definite solver response to stale incidental diagnostic fields.
    if solver=='sat' or status=='sat':return Outcome('sat','SAT','Solver returned SAT')
    if solver=='unsat' or status=='unsat':return Outcome('unsat','UNSAT','Solver returned UNSAT')
    if status=='unsat_preprocessing' or norm(row.get('translation_status'))=='discharged':
        return Outcome('discharged','PRE','Goal closed by preprocessing; solver not called')
    if 'process_timeout' in status or 'process_timeout' in kind or solver=='process_timeout' or kind=='wall_timeout' or status=='translation_timeout' or status=='timeout' and not solver:
        return Outcome('process_timeout',p+':P','Process time cap; '+str(phase or 'phase unrecorded'))
    if ('timeout' in solver) or ('solver_timeout' in joined):
        return Outcome('solver_timeout','Q:T','Solver timeout')
    # Structured failure_kind takes precedence over incidental names in large Lean goals.
    fallback=kind in {'','unknown'}
    if kind in {'steps','step_limit','max_steps','simp_steps'} or fallback and 'simp' in joined and ('step' in joined or 'maxsteps' in joined):
        return Outcome('simp_steps',p+':S','Simplifier step limit; '+str(phase))
    if kind in {'recursion','recursion_limit','max_rec_depth'} or fallback and ('recursion' in joined or 'maxrecdepth' in joined or 'max_rec_depth' in joined):
        return Outcome('recursion',p+':R','Recursion limit; '+str(phase))
    if kind in {'heartbeat','heartbeats','heartbeat_limit'} or fallback and 'heartbeat' in joined:
        return Outcome('heartbeat',p+':B','Heartbeat limit; '+str(phase))
    if p=='E':return Outcome('embedding','E:!','SMT embedding failure')
    if p in {'T','W'}:return Outcome('translation',p+':!','SMT translation/serialization failure')
    if p=='V' or 'query_elaboration' in status or 'query_elaboration' in kind:
        return Outcome('query_elaboration','V:!','Query or verification-condition elaboration failed')
    if p=='G' or 'setup' in status or 'setup' in kind:
        return Outcome('setup','G:!','Setup or model elaboration failed')
    if status=='query_ready':return Outcome('query_ready','READY','SMT query emitted; solver result pending')
    if solver.startswith('unknown') or status.startswith('unknown') or status=='solver_unknown':
        return Outcome('solver_unknown','Q:?','Solver returned unknown')
    if solver and solver not in {'not_run','not_reached','not_needed','skipped','pending'}:
        return Outcome('solver_error','Q:!','Solver error: '+solver)
    if 'not_started' in status or 'not_run' in status or 'skipped' in status:
        return Outcome('not_run','—',row.get('status','No recorded result'))
    return Outcome('other',p+':!',row.get('status','Unclassified failure'))


def definite_verdict(row):
    family=classify(row).family
    if family in {'unsat','discharged'}:return 'unsat'
    if family=='sat':return 'sat'
    return None


def query_seconds(row):
    if not row:return None
    value=number(row.get('query_total_ms'))
    ts=norm(row.get('translation_status'))
    if value is None or ts!='complete':return None
    # Only a fully emitted query is timed here, including when its solver later times out.
    return value/1000


def preprocessing_seconds(row):
    if not row:return None
    value=number(row.get('preprocessing_ms'))
    return None if value is None else value/1000


def completed_solver_seconds(row):
    if not row or classify(row).family not in {'sat','unsat'}:return None
    value=number(row.get('solver_ms'))
    return None if value is None else value/1000


def completed_seconds(row):
    if not row or classify(row).family not in {'sat','unsat'}:return None
    value=number(row.get('completed_total_ms'))
    return None if value is None else value/1000


def write_csv(path,rows,fields=None):
    if not rows and not fields:return
    with path.open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=fields or list(rows[0]));w.writeheader();w.writerows(rows)


def esc(value):return html.escape(str(value or ''))

def model_query(model):return str(model.get('query',model.get('assertion','')))


def load(args):
    manifest=read_json(args.manifest,[])
    if isinstance(manifest,dict):manifest=manifest.get('models',manifest.get('manifest',[]))
    exclusions=read_json(args.exclusions,[])
    if isinstance(exclusions,dict):exclusions=exclusions.get('exclusions',[])
    raw=read_csv(args.results/'runs.csv')
    rows=[r for r in raw if not r.get('profile') or r['profile']==args.profile]
    indexed={}
    for r in rows:
        variant={'current':'old','original':'old'}.get(r['variant'],r['variant'])
        key=(r['model'],int(r['depth']),variant)
        if key in indexed:raise ValueError(f'Duplicate cell {key}; resolve repetitions/profiles before reporting')
        if variant not in VARIANTS:raise ValueError(f'Unknown variant {variant}')
        indexed[key]=r
    names={m['model'] for m in manifest}
    unexpected={r['model'] for r in rows}-names
    if unexpected:raise ValueError(f'Results contain models outside manifest: {sorted(unexpected)}')
    stages=read_csv(args.results/'stages.csv')
    by_cell=defaultdict(list)
    for r in stages:by_cell[r['cell_id']].append(r)
    return manifest,exclusions,indexed,by_cell


def sampled_depth_summary(models,indexed,depths):
    """Largest observed successful sample, with all successes preserved (not a bound)."""
    summaries=[]
    for model in models:
        name=model['model'];row=dict(model=name,path=model.get('path',''))
        for variant in VARIANTS:
            candidates=[(d,indexed.get((name,d,variant))) for d in sorted(depths)]
            emitted=[d for d,r in candidates if r and norm(r.get('translation_status'))=='complete' and r.get('query_sha256')]
            definite=[d for d,r in candidates if classify(r).family in {'sat','unsat'}]
            discharged=[d for d,r in candidates if classify(r).family=='discharged']
            row[variant+'_serialized_depths']=' '.join(map(str,emitted))
            row[variant+'_highest_sampled_serialized_depth']=max(emitted) if emitted else ''
            row[variant+'_definite_solver_depths']=' '.join(map(str,definite))
            row[variant+'_highest_sampled_definite_solver_depth']=max(definite) if definite else ''
            row[variant+'_solver_answer_at_highest_sample']=classify(indexed[name,max(definite),variant]).family if definite else ''
            row[variant+'_preprocessing_discharge_depths']=' '.join(map(str,discharged))
            row[variant+'_highest_sampled_preprocessing_discharge_depth']=max(discharged) if discharged else ''
        row['interpretation']='Largest successful sampled exact depth only; no monotonicity or all-depths-up-to-N claim.'
        summaries.append(row)
    return summaries


def export_tables(out,models,indexed,depths,by_cell=None):
    by_cell=by_cell or {}
    outcomes=[];matches=[];prematches=[];queries=[];failures=[];inventory=[]
    counts=Counter()
    disagreements=[]
    for model in models:
        name=model['model']
        inventory.append(dict(model=name,path=model.get('path',''),module=model.get('module',''),category=model.get('category',''),cut_line=model.get('cut_line',''),query_kind=model.get('query_kind',''),query=model_query(model),query_source=model.get('query_source',''),expected_status=model.get('expected_status',''),notes=model.get('notes',''),source_options=json.dumps(model.get('source_options',[])),imports=json.dumps(model.get('imports',[])),source_sha256=model.get('source_sha256','')))
        for d in depths:
            paired={v:indexed.get((name,d,v)) for v in VARIANTS}
            for v,r in paired.items():
                o=classify(r);counts[d,v,o.family]+=1
                outcomes.append(dict(model=name,path=model.get('path',''),depth=d,variant=v,recorded=r is not None,outcome_family=o.family,outcome_code=o.code,outcome=o.detail,failure_phase=r.get('failure_phase','') if r else '',failure_kind=r.get('failure_kind','') if r else '',preprocessing_seconds=preprocessing_seconds(r) if preprocessing_seconds(r) is not None else '',query_seconds=query_seconds(r) if query_seconds(r) is not None else '',query_elaboration_seconds=(number(r.get('query_elaboration_ms'))/1000 if r and number(r.get('query_elaboration_ms')) is not None else ''),solver_seconds=(number(r.get('solver_ms'))/1000 if r and number(r.get('solver_ms')) is not None else ''),completed_solver_seconds=completed_solver_seconds(r) if completed_solver_seconds(r) is not None else '',completed_seconds=completed_seconds(r) if completed_seconds(r) is not None else '',cell_id=r.get('cell_id','') if r else ''))
                if r and o.family not in {'sat','unsat','discharged','query_ready','not_run'}:
                    failures.append(dict(model=name,depth=d,variant=v,outcome_family=o.family,phase=r.get('failure_phase',''),kind=r.get('failure_kind',''),message=r.get('failure_message',''),cell_id=r.get('cell_id',''),event_path=r.get('event_path',''),translation_log=r.get('translation_log',''),solver_log=r.get('solver_log','')))
                if r and norm(r.get('translation_status'))=='complete' and r.get('query_sha256'):
                    queries.append(dict(model=name,depth=d,variant=v,status=r.get('status',''),query_bytes=r.get('query_bytes',''),query_commands=r.get('query_commands',''),query_sha256=r.get('query_sha256',''),query_path=r.get('query_path',''),proof_status=r.get('proof_status','')))
            a,b=paired['old'],paired['early'];ta,tb=query_seconds(a),query_seconds(b);ca,cb=completed_seconds(a),completed_seconds(b)
            pa,pb=preprocessing_seconds(a),preprocessing_seconds(b)
            if pa is not None and pb is not None:
                prematches.append(dict(model=name,depth=d,old_preprocessing_seconds=pa,early_preprocessing_seconds=pb,preprocessing_speedup=pa/pb if pa>0 and pb>0 else '',old_outcome=classify(a).family,early_outcome=classify(b).family))
            if ta is not None and tb is not None:
                matches.append(dict(model=name,depth=d,old_query_seconds=ta,early_query_seconds=tb,query_speedup=ta/tb if ta>0 and tb>0 else '',old_completed_seconds=ca if ca is not None else '',early_completed_seconds=cb if cb is not None else '',completed_speedup=ca/cb if ca is not None and cb is not None and ca>0 and cb>0 else '',old_outcome=classify(a).family,early_outcome=classify(b).family))
            if definite_verdict(a) is not None and definite_verdict(b) is not None and definite_verdict(a)!=definite_verdict(b):
                disagreements.append(dict(model=name,depth=d,old=classify(a).family,early=classify(b).family,old_verdict=definite_verdict(a),early_verdict=definite_verdict(b)))
    write_csv(out/'matched-preprocessing-timings.csv',prematches,['model','depth','old_preprocessing_seconds','early_preprocessing_seconds','preprocessing_speedup','old_outcome','early_outcome'])
    countrows=[dict(depth=d,variant=v,outcome_family=f,count=counts[d,v,f]) for d in depths for v in VARIANTS for f in STYLES]
    failurecounts=Counter((r['variant'],r['outcome_family'],r['phase'],r['kind']) for r in failures)
    failurecountrows=[dict(variant=v,outcome_family=f,phase=p,kind=k,count=n) for (v,f,p,k),n in sorted(failurecounts.items())]
    emptyfields={'matched-timings.csv':['model','depth','old_query_seconds','early_query_seconds','query_speedup','old_completed_seconds','early_completed_seconds','completed_speedup','old_outcome','early_outcome'],'queries.csv':['model','depth','variant','status','query_bytes','query_commands','query_sha256','query_path','proof_status'],'failures.csv':['model','depth','variant','outcome_family','phase','kind','message','cell_id','event_path','translation_log','solver_log'],'definite-disagreements.csv':['model','depth','old','early','old_verdict','early_verdict'],'failure-counts-by-phase.csv':['variant','outcome_family','phase','kind','count']}
    for filename,rs in [('failure-counts-by-phase.csv',failurecountrows),('outcomes.csv',outcomes),('matched-timings.csv',matches),('queries.csv',queries),('failures.csv',failures),('inventory.csv',inventory),('counts-by-depth.csv',countrows),('definite-disagreements.csv',disagreements)]:
        write_csv(out/filename,rs,emptyfields.get(filename))
    deltas=[];transitions=Counter()
    for model in models:
        for d in depths:
            a=indexed.get((model['model'],d,'old'));b=indexed.get((model['model'],d,'early'))
            transitions[classify(a).family,classify(b).family]+=1
            if a is not None and b is not None and (query_seconds(a) is not None)!=(query_seconds(b) is not None):
                deltas.append(dict(model=model['model'],depth=d,old_outcome=classify(a).family,early_outcome=classify(b).family,old_query_complete=query_seconds(a) is not None,early_query_complete=query_seconds(b) is not None))
    write_csv(out/'query-completion-differences.csv',deltas,['model','depth','old_outcome','early_outcome','old_query_complete','early_query_complete'])
    write_csv(out/'outcome-transitions.csv',[dict(old_outcome=a,early_outcome=b,count=n) for (a,b),n in sorted(transitions.items())])
    depth_summary=sampled_depth_summary(models,indexed,depths)
    write_csv(out/'sampled-depth-summary.csv',depth_summary)
    summary={'model_files':len(models),'depths':depths,'requested_cells':len(outcomes),'recorded_cells':sum(r['recorded'] for r in outcomes),'attempted_query_cells':sum(r['recorded'] and r['outcome_family'] not in {'not_run','blocked_setup'} and phase_code(r['failure_phase'])!='G' for r in outcomes),'outcome_counts':{v:dict(Counter(r['outcome_family'] for r in outcomes if r['variant']==v)) for v in VARIANTS},'completed_query_cells':{v:sum(query_seconds(r) is not None for (m,d,rv),r in indexed.items() if rv==v and d in depths) for v in VARIANTS},'matched_completed_query_pairs':len(matches),'definite_answer_disagreements':disagreements,'definite_solver_disagreements':[r for r in disagreements if r['old'] in {'sat','unsat'} and r['early'] in {'sat','unsat'}],'query_completion_changes':{'early_only':sum(r['early_query_complete'] for r in deltas),'old_only':sum(r['old_query_complete'] for r in deltas)}}
    pipeline_rows=[r for (m,d,v),r in indexed.items() if d in depths and by_cell.get(r.get('cell_id'))]
    blocked_rows=[r for r in outcomes if r['outcome_family']=='blocked_setup']
    summary.update(pipeline_entered_cells=len(pipeline_rows),pipeline_entered_files=len({r['model'] for r in pipeline_rows}),model_setup_blocked_cells=len(blocked_rows),model_setup_blocked_files=len({r['model'] for r in blocked_rows}),not_started_cells=sum(r['outcome_family']=='not_run' for r in outcomes))
    summary['completed_preprocessing_cells']={v:sum(preprocessing_seconds(r) is not None for (m,d,rv),r in indexed.items() if rv==v and d in depths) for v in VARIANTS}
    summary['matched_completed_preprocessing_pairs']=len(prematches)
    summary['outcome_file_counts']={v:{family:len({r['model'] for r in outcomes if r['variant']==v and r['outcome_family']==family}) for family in STYLES if any(r['variant']==v and r['outcome_family']==family for r in outcomes)} for v in VARIANTS}
    ratios=[r['query_speedup'] for r in matches if isinstance(r['query_speedup'],(float,int))]
    if ratios:summary['observed_matched_query_ratios']={'minimum':min(ratios),'median':statistics.median(ratios),'maximum':max(ratios),'description':'Original / early time across matched cells; one observation per cell, heterogeneous models/depths, no uncertainty estimate.'}
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    return dict(depth_summary=depth_summary,outcomes=outcomes,matches=matches,prematches=prematches,queries=queries,failures=failures,counts=counts,disagreements=disagreements,failurecounts=failurecountrows,summary=summary)


def setup_plots():
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':9,'axes.spines.top':False,'axes.spines.right':False,'axes.edgecolor':'#B0BAC2','axes.labelcolor':'#30424F','text.color':'#173044','xtick.color':'#4C5C68','ytick.color':'#4C5C68','grid.color':'#E0E5E9','svg.fonttype':'none','savefig.bbox':'tight'})
    return plt


def save(fig,out,name):
    import matplotlib.pyplot as plt
    for ext in ['png','svg']:fig.savefig(out/(name+'.'+ext),dpi=180,facecolor='white')
    plt.close(fig)


def matrix(fig,ax,models,indexed,depths,compact=False):
    from matplotlib.patches import Rectangle
    n=len(models)
    ax.set_xlim(-.02,len(depths)*2+.02);ax.set_ylim(-.02,n+.02);ax.invert_yaxis()
    for y,m in enumerate(models):
        for di,d in enumerate(depths):
            for vi,v in enumerate(VARIANTS):
                o=classify(indexed.get((m['model'],d,v)));_,bg,fg=STYLES[o.family];x=di*2+vi
                ax.add_patch(Rectangle((x+.035,y+.035),.93,.93,facecolor=bg,edgecolor='white',linewidth=.8))
                ax.text(x+.5,y+.5,o.code,ha='center',va='center',color=fg,fontsize=7 if compact else 8,fontweight='bold')
    ax.set_yticks([i+.5 for i in range(n)],labels=[m['model'] for m in models],fontsize=7.8 if compact else 9)
    ax.set_xticks([i+.5 for i in range(len(depths)*2)],labels=[f'{d}\n{v}' for d in depths for v in ['old','early']],fontsize=8)
    ax.tick_params(length=0);ax.xaxis.tick_top();ax.tick_params(axis='x',pad=8)
    for spine in ax.spines.values():spine.set_visible(False)
    for d in range(1,len(depths)):ax.axvline(d*2,color='#87949E',lw=.8)


def matrix_legend(fig,y=.04):
    from matplotlib.patches import Patch
    handles=[Patch(facecolor=style[1],label=style[0]) for style in STYLES.values()]
    fig.legend(handles=handles,loc='lower center',bbox_to_anchor=(.5,y),ncol=5,frameon=False,fontsize=7.5)
    fig.text(.02,.012,'Cell code = phase:limit. N nextSimp · H hoist · D destruct/dsimp · M smtSimp · I intros · E embedding · Z normalize · T translate · W serialize · G setup · V query/VC · Q solver.\nLimits: S simp steps · R recursion · B heartbeat · P process cap · ! other error. G:— = unattempted because shared model setup failed.',fontsize=7,color='#5C6B76')


def plot_matrices(plt,out,models,indexed,args):
    names=[]
    pages=[models[i:i+args.rows_per_page] for i in range(0,len(models),args.rows_per_page)]
    for pi,page in enumerate(pages,1):
        height=max(6,len(page)*.29+2.8)
        fig,ax=plt.subplots(figsize=(15,height))
        matrix(fig,ax,page,indexed,args.depths)
        fig.suptitle(f'Symbolic BMC outcomes · models {(pi-1)*args.rows_per_page+1}–{(pi-1)*args.rows_per_page+len(page)} of {len(models)}',x=.02,ha='left',fontsize=17,fontweight='bold',y=.98)
        fig.text(.02,.91,'Exact-N action traces; one sample per cell. SAT/UNSAT are solver responses; G:— means the query was not attempted because model setup failed. Shared batch setup measurements must not be summed across cells. PRE means preprocessing closed the goal.',fontsize=10,color='#536675')
        fig.subplots_adjust(left=.29,right=.99,top=.83,bottom=.18)
        matrix_legend(fig,.045)
        name=f'outcome-matrix-{pi:02d}';save(fig,out,name);names.append(name)
    return names


def plot_counts(plt,out,stats,models,args):
    from matplotlib.patches import Patch
    fig,ax=plt.subplots(figsize=(14,6.5));xs=list(range(len(args.depths)*2));bottom=[0]*len(xs)
    present=[]
    for family,(label,color,_) in STYLES.items():
        vals=[stats['counts'][d,v,family] for d in args.depths for v in VARIANTS]
        if not any(vals):continue
        present.append(Patch(facecolor=color,label=label));ax.bar(xs,vals,bottom=bottom,color=color,width=.8,edgecolor='white',linewidth=.5)
        bottom=[a+b for a,b in zip(bottom,vals)]
    ax.set_xticks(xs,labels=[f'{d}\n{v}' for d in args.depths for v in ['old','early']]);ax.set_ylim(0,len(models));ax.set_ylabel('Models (all manifest entries)');ax.set_xlabel('Exact action count / variant');ax.grid(axis='y');ax.set_axisbelow(True)
    ax.legend(handles=present,bbox_to_anchor=(1.01,1),loc='upper left',frameon=False,fontsize=9)
    fig.suptitle('Outcomes across the complete example corpus',x=.04,ha='left',fontsize=18,fontweight='bold')
    fig.text(.04,.02,f'{len(models)} models × {len(args.depths)} exact depths × 2 variants; missing results stay visible. Query limits: heartbeats {args.heartbeats:,}, recursion {args.recdepth}; Veil simp default {args.simpsteps:,}.\nResource failures are classified by their actual error; phase is retained in the detailed matrices and CSV. Solver timeouts are not UNSAT.',fontsize=8,color='#5C6B76')
    fig.subplots_adjust(left=.065,right=.78,top=.9,bottom=.18);save(fig,out,'outcome-counts')


def plot_matched(plt,out,stats,args,metric='query'):
    from matplotlib.lines import Line2D
    source=stats['prematches'] if metric=='preprocessing' else stats['matches']
    completed_pairs=[r for r in source if isinstance(r[f'old_{metric}_seconds'],(int,float)) and isinstance(r[f'early_{metric}_seconds'],(int,float))]
    zero_pairs=[r for r in completed_pairs if r[f'old_{metric}_seconds']==0 or r[f'early_{metric}_seconds']==0]
    pairs=[r for r in completed_pairs if r[f'old_{metric}_seconds']>0 and r[f'early_{metric}_seconds']>0]
    fig,ax=plt.subplots(figsize=(8,7))
    colors=plt.get_cmap('viridis')
    for i,d in enumerate(args.depths):
        rs=[r for r in pairs if r['depth']==d]
        if rs:ax.scatter([r[f'old_{metric}_seconds'] for r in rs],[r[f'early_{metric}_seconds'] for r in rs],color=colors(i/max(1,len(args.depths)-1)),label=f'depth {d}',s=28,alpha=.75,edgecolors='white',linewidths=.4)
    if pairs:
        nums=[r[f'{v}_{metric}_seconds'] for r in pairs for v in VARIANTS];lo=min(nums)*.75;hi=max(nums)*1.4
        ax.plot([lo,hi],[lo,hi],color='#88949D',ls='--',lw=1);ax.set_xlim(lo,hi);ax.set_ylim(lo,hi)
        ax.set_xscale('log');ax.set_yscale('log');ax.legend(frameon=False,title='Exact action count',loc='upper left')
    else:ax.text(.5,.5,'Completed pairs include 0 ms recordings;\nbelow timer resolution, omitted on log axes.' if zero_pairs else 'No matched completed observations',ha='center',va='center',transform=ax.transAxes)
    ax.set_xlabel('Original order (seconds)');ax.set_ylabel('Early introduction (seconds)');ax.grid(alpha=.55);ax.set_axisbelow(True)
    title={'completed':'Complete query + solver timings','query':'Complete SMT-query timings','preprocessing':'Complete Veil-preprocessing timings'}[metric]
    fig.suptitle(title+' on matched cells',x=.04,ha='left',fontsize=17,fontweight='bold')
    fig.text(.04,.915,f'{len(pairs)} plotted pairs; {len(zero_pairs)} completed pairs omitted due to 0 ms timer readings.\nBelow the diagonal means early introduction was faster.',fontsize=10,color='#536675',va='top')
    note={'completed':'Only definite SAT/UNSAT cells with both completed_total_ms values; solver time includes parsing and native model/core retrieval.','query':'Only cells with completed SMT query serialization in both variants; solver execution excluded.','preprocessing':'Both variants completed all Veil preprocessing phases; later backend failures are allowed. SMT stages and solving excluded.'}[metric]
    fig.text(.04,.025,note+'\nOne observation per cell; this is a matched subset, not the full corpus. Setup/query elaboration excluded; failed work is never plotted as completed time.',fontsize=8,color='#5C6B76')
    fig.subplots_adjust(left=.13,right=.97,top=.82,bottom=.14);save(fig,out,'matched-'+metric+'-timings')


def phase_values(row,by_cell,preprocessing_only=False):
    stages=by_cell.get(row['cell_id'],[])
    successful=[s for s in stages if norm(s.get('status')) in {'complete','completed','ok','success','passed'}]
    def stage_ms(code):return sum(number(s.get('elapsed_ms')) or 0 for s in successful if phase_code(s.get('phase'))==code)
    pre=number(row.get('preprocessing_ms'));smt=number(row.get('smt_preprocessing_ms'));tr=number(row.get('translation_ms'));ser=number(row.get('serialization_ms'))
    if pre is None:return None
    n,h,e=stage_ms('N'),stage_ms('H'),stage_ms('E')
    if n+h>pre+2:return None
    if preprocessing_only:return [n/1000,h/1000,max(0,pre-n-h)/1000]
    if None in [smt,tr,ser] or e>smt+2:return None
    return [n/1000,h/1000,max(0,pre-n-h)/1000,e/1000,(max(0,smt-e)+tr+ser)/1000]


def plot_remaining_phases(plt,out,models,indexed,by_cell,args):
    """Show successful early query costs, without assigning costs to failed work."""
    labels=['nextSimp','hoist','other Veil','embedding','other SMT']
    colors=['#247C9C','#E6AB4A','#B7C4CF','#7862A1','#C8BCDD']
    table=[];names=[]
    for model in models:
        candidates=[(d,indexed.get((model['model'],d,'early'))) for d in args.depths]
        candidates=[(d,r) for d,r in candidates if query_seconds(r) is not None]
        if candidates:
            d,row=max(candidates,key=lambda x:x[0]);vals=phase_values(row,by_cell)
            table.append(dict(model=model['model'],selected_exact_depth=d,query_seconds=query_seconds(row),nextSimp_seconds=vals[0] if vals else '',hoist_seconds=vals[1] if vals else '',other_Veil_seconds=vals[2] if vals else '',embedding_seconds=vals[3] if vals else '',other_SMT_seconds=vals[4] if vals else '',outcome=classify(row).family,selection='largest sampled exact depth with a completed early query',cell_id=row['cell_id']))
        else:
            table.append(dict(model=model['model'],selected_exact_depth='',query_seconds='',nextSimp_seconds='',hoist_seconds='',other_Veil_seconds='',embedding_seconds='',other_SMT_seconds='',outcome='no_completed_query',selection='no sampled depth emitted an early query',cell_id=''))
    write_csv(out.parent/'selected-early-phase-costs.csv',table)
    for page_index,start in enumerate(range(0,len(table),args.rows_per_page),1):
        page=table[start:start+args.rows_per_page];height=max(6,len(page)*.31+2.4)
        fig,ax=plt.subplots(figsize=(15,height));ax.set_xlim(0,116);ax.set_ylim(-.65,len(page)-.35);ax.invert_yaxis()
        for y,row in enumerate(page):
            keys=['nextSimp_seconds','hoist_seconds','other_Veil_seconds','embedding_seconds','other_SMT_seconds']
            if row['selected_exact_depth']!='' and all(isinstance(row[k],(float,int)) for k in keys):
                vals=[row[k] for k in keys];total=sum(vals);left=0
                for label,color,value in zip(labels,colors,vals):
                    width=value/total*100 if total else 0
                    ax.barh(y,width,left=left,color=color,height=.7,label=label if y==0 else None);left+=width
                ax.text(102,y,f"{row['query_seconds']:.3g} s",va='center',fontsize=8.5)
            else:ax.text(1,y,'No completed query' if row['selected_exact_depth']=='' else 'Phase components unavailable',va='center',fontsize=8.5,color='#7B8790')
        ax.set_yticks(range(len(page)),labels=[r['model']+(f"  (N={r['selected_exact_depth']})" if r['selected_exact_depth']!='' else '') for r in page],fontsize=8)
        ax.set_xticks([0,25,50,75,100],labels=['0%','25%','50%','75%','100%']);ax.set_xlabel('Share of completed SMT-query stage time');ax.grid(axis='x',alpha=.5);ax.set_axisbelow(True);ax.tick_params(axis='y',length=0)
        from matplotlib.patches import Patch
        fig.legend(handles=[Patch(facecolor=c,label=l) for l,c in zip(labels,colors)],loc='lower center',bbox_to_anchor=(.6,.075),ncol=5,frameon=False,fontsize=9)
        fig.suptitle(f'Where query time goes after early introduction · files {start+1}–{start+len(page)}',x=.02,ha='left',fontsize=17,fontweight='bold',y=.98)
        fig.text(.02,.92,'Each row selects its largest sampled exact depth with a completed query; N varies and is shown. One observation per cell.',fontsize=9.5,color='#536675')
        fig.text(.02,.018,'Right labels give the completed query-stage total in seconds. Solver, setup and query/VC elaboration excluded. Failed attempts have no completed timing.\nThis selection is not a monotone depth limit; consult the full outcome matrix for failed and nonmonotone results.',fontsize=8,color='#5C6B76')
        fig.subplots_adjust(left=.34,right=.98,top=.86,bottom=.17)
        name=f'early-phase-costs-{page_index:02d}';save(fig,out,name);names.append(name)
    return names


def plot_model(plt,out,model,indexed,by_cell,args):
    from matplotlib.patches import Rectangle
    from matplotlib.ticker import NullFormatter
    name=model['model'];fig=plt.figure(figsize=(13,9.4));gs=fig.add_gridspec(3,2,height_ratios=[3,2.1,.7],hspace=.95,wspace=.35)
    ax=fig.add_subplot(gs[0,0]);solver=fig.add_subplot(gs[0,1]);phase=fig.add_subplot(gs[1,0]);size=fig.add_subplot(gs[1,1]);strip=fig.add_subplot(gs[2,:])
    any_times=False;completed_timings=0;zero_timings=0
    for v in VARIANTS:
        for metric,extractor,style,marker in [('Veil preprocessing',preprocessing_seconds,'--','s'),('SMT query',query_seconds,'-','o')]:
            vals=[extractor(indexed.get((name,d,v))) for d in args.depths]
            completed_timings+=sum(t is not None for t in vals);zero_timings+=sum(t==0 for t in vals if t is not None)
            vals=[t if t is not None and t>0 else math.nan for t in vals]
            if any(math.isfinite(t) for t in vals):ax.plot(args.depths,vals,color=COLORS[v],linestyle=style,marker=marker,markersize=4,label=('Original' if v=='old' else 'Early')+' · '+metric);any_times=True
    ax.set_xscale('log',base=2);ax.set_xticks(args.depths,labels=args.depths);ax.set_xlim(min(args.depths)*.8,max(args.depths)*1.25);ax.set_xlabel('Exact number of actions');ax.set_ylabel('Completed stages (seconds)');ax.set_title('Translation preparation',loc='left',fontsize=11,fontweight='bold');ax.grid(axis='y');ax.set_axisbelow(True)
    if any_times:ax.set_yscale('log');ax.yaxis.set_minor_formatter(NullFormatter());ax.legend(frameon=False,fontsize=8)
    elif completed_timings:ax.set_yscale('log');ax.yaxis.set_minor_formatter(NullFormatter())
    else:ax.text(.5,.5,'No completed preprocessing or query timings',ha='center',va='center',transform=ax.transAxes)
    if zero_timings:ax.text(.02,.02,f'{zero_timings} completed timing(s) recorded as 0 ms;\nbelow timer resolution, omitted on log axes.',ha='left',va='bottom',transform=ax.transAxes,fontsize=7,color='#536675')
    for axis,extractor,ylabel,title in [
        (solver,completed_solver_seconds,'Completed wrapper call (seconds)','Native solver wrapper · definite SAT/UNSAT only'),
        (size,lambda r:(number(r.get('query_bytes'))/1024 if r and query_seconds(r) is not None and number(r.get('query_bytes')) is not None else None),'Serialized query (KiB)','SMT-query size')]:
        plotted=False;completed_values=0;zero_values=0
        for v in VARIANTS:
            vals=[extractor(indexed.get((name,d,v))) for d in args.depths]
            completed_values+=sum(x is not None for x in vals);zero_values+=sum(x==0 for x in vals if x is not None)
            vals=[x if x is not None and x>0 else math.nan for x in vals]
            if any(math.isfinite(x) for x in vals):
                axis.plot(args.depths,vals,color=COLORS[v],marker='o',markersize=4,label='Original' if v=='old' else 'Early');plotted=True
        axis.set_xscale('log',base=2);axis.set_xticks(args.depths,labels=args.depths);axis.set_xlim(min(args.depths)*.8,max(args.depths)*1.25);axis.set_xlabel('Exact number of actions');axis.set_ylabel(ylabel);axis.set_title(title,loc='left',fontsize=11,fontweight='bold');axis.grid(axis='y');axis.set_axisbelow(True)
        if plotted:axis.set_yscale('log');axis.yaxis.set_minor_formatter(NullFormatter());axis.legend(frameon=False,fontsize=8)
        elif completed_values:axis.set_yscale('log');axis.yaxis.set_minor_formatter(NullFormatter())
        else:axis.text(.5,.5,'No completed SAT/UNSAT solver call' if axis is solver else 'No serialized query',ha='center',va='center',transform=axis.transAxes,fontsize=9)
        if zero_values:
            note=f'{zero_values} completed call(s) recorded as 0 ms;\nbelow timer resolution, omitted on log axes.' if axis is solver else f'{zero_values} serialized query/queries recorded as 0 bytes; omitted on log axes.'
            axis.text(.02,.02,note,ha='left',va='bottom',transform=axis.transAxes,fontsize=7,color='#536675')
    common=[d for d in args.depths if all(preprocessing_seconds(indexed.get((name,d,v))) is not None for v in VARIANTS)]
    if common:
        d=max(common);pre_only=not all(query_seconds(indexed.get((name,d,v))) is not None for v in VARIANTS);values=[phase_values(indexed[name,d,v],by_cell,preprocessing_only=pre_only) for v in VARIANTS]
        if all(x is not None for x in values):
            labels=['nextSimp','hoist','other Veil','embedding','other SMT'];colors=['#247C9C','#E6AB4A','#B7C4CF','#7862A1','#C8BCDD']
            if pre_only:labels,colors=labels[:3],colors[:3]
            for y,(v,vals) in enumerate(zip(VARIANTS,values)):
                left=0
                for label,color,value in zip(labels,colors,vals):phase.barh(y,value,left=left,color=color,height=.5,label=label if y==0 else None);left+=value
                phase.text(left,y,f' {left:.3g}s',va='center',fontsize=8)
            phase.set_yticks([0,1],labels=['Original','Early']);phase.invert_yaxis();phase.set_xlim(0,phase.get_xlim()[1]*1.2);phase.set_xlabel('Sum of completed phases (seconds)');phase.set_title(f'{"Veil phases" if pre_only else "Query phases"} at depth {d}',loc='left',fontsize=11,fontweight='bold');phase.grid(axis='x');phase.set_axisbelow(True);phase.legend(ncol=3,loc='upper left',bbox_to_anchor=(0,-.32),frameon=False,fontsize=7)
        else:phase.text(.5,.5,'Phase components unavailable',ha='center',va='center',transform=phase.transAxes);phase.axis('off')
    else:phase.text(.5,.5,'No depth completed preprocessing in both variants',ha='center',va='center',transform=phase.transAxes);phase.axis('off')
    strip.set_xlim(0,len(args.depths));strip.set_ylim(0,2);strip.invert_yaxis()
    for yi,v in enumerate(VARIANTS):
        for xi,d in enumerate(args.depths):
            o=classify(indexed.get((name,d,v)));_,bg,fg=STYLES[o.family];strip.add_patch(Rectangle((xi+.025,yi+.04),.95,.92,facecolor=bg));strip.text(xi+.5,yi+.5,o.code,ha='center',va='center',color=fg,fontsize=8,fontweight='bold')
    strip.set_xticks([i+.5 for i in range(len(args.depths))],labels=args.depths);strip.xaxis.tick_top();strip.set_yticks([.5,1.5],labels=['Original','Early']);strip.tick_params(length=0)
    for spine in strip.spines.values():spine.set_visible(False)
    fig.suptitle(name,x=.035,ha='left',fontsize=17,fontweight='bold',y=.98)
    fig.text(.035,.94,model.get('path',''),fontsize=9,color='#536675')
    fig.text(.035,.018,f'One observation per cell; exact-N traces. Query limits: {args.heartbeats:,} heartbeats / recursion {args.recdepth}; Veil simp default {args.simpsteps:,}.\nPreparation: dashed = completed Veil phases; solid = serialized query stages. Setup/VC elaboration excluded. Solver wrapper includes parsing and native model/core retrieval.\nTimeout/unknown calls have no completed timing point; outcomes appear in the strip. 10s checkSat limit; 15s wrapper watchdog. Phase/limit code key is in the report.',fontsize=8,color='#5C6B76')
    fig.subplots_adjust(left=.08,right=.97,top=.875,bottom=.14);save(fig,out,name)


def query_artifact_link(row,args):
    if not row or norm(row.get('translation_status'))!='complete' or not row.get('query_sha256'):
        return '—'
    recorded=Path(row.get('query_path',''))
    candidates=[args.results/'queries'/recorded.name,recorded]
    found=next((p for p in candidates if p.is_file()),None)
    if found is None:return 'Emitted query missing from report inputs'
    relative=Path(os.path.relpath(found,args.out_dir)).as_posix()
    return f'<a href="{esc(relative)}" title="SHA256 {esc(row["query_sha256"])}">SMT-LIB</a> <span class="small muted">{esc(row.get("query_bytes",""))} bytes</span>'


def write_report(out,models,exclusions,indexed,stats,matrices,args,phase_panels=()):
    comparison=stats.get('comparison',{})
    metadata=read_json(args.results/'metadata.json',{})
    environment=read_json(args.environment,{})
    watchdog_description='Recorded wall watchdog caps: '+', '.join(f'{label} {metadata.get(key, "unrecorded")} seconds' for label,key in [('model setup','setup_timeout_seconds'),('query/VC elaboration','query_elaboration_timeout_seconds'),('query pipeline','pipeline_timeout_seconds')])+'. The native solver has the separate checkSat and wrapper limits described below.'
    baseline_definition=f'Old/Original replays the pre-change tactic order on the current source base ({metadata.get("commit","recorded in results metadata")}); it is not the historical issue commit. Each file has one selected assertion, which may combine safety clauses. The inventory contains overlapping variants, not {len(models)} independent protocols.'
    appendices=[p for p in args.appendix if p.exists()]
    executive=args.executive_summary.read_text().strip() if args.executive_summary and args.executive_summary.exists() else ''
    expected=len(models)*len(args.depths)*2;recorded=sum(r['recorded'] for r in stats['outcomes'])
    early_steps=[r for r in stats['outcomes'] if r['variant']=='early' and r['outcome_family']=='simp_steps']
    early_resources=[r for r in stats['outcomes'] if r['variant']=='early' and r['outcome_family'] in {'simp_steps','recursion','heartbeat'}]
    definite=[(m['model'],d) for m in models for d in args.depths if all(classify(indexed.get((m['model'],d,v))).family in {'sat','unsat'} for v in VARIANTS)]
    definite_with_pre=[(m['model'],d) for m in models for d in args.depths if all(definite_verdict(indexed.get((m['model'],d,v))) is not None for v in VARIANTS)]
    solver_disagreements=stats['summary']['definite_solver_disagreements']
    lines=[f'Symbolic BMC before/after report: {len(models)} models, {len(args.depths)} exact depths, two variants.',f'Recorded rows for {recorded}/{expected} predeclared slots; {stats['summary']['pipeline_entered_cells']} pipelines entered across {stats['summary']['pipeline_entered_files']} files; one observation per attempted cell.',baseline_definition,f'Query resource settings: maxHeartbeats={args.heartbeats}, maxRecDepth={args.recdepth}, Veil simp default maxSteps={args.simpsteps}; dependency-local overrides are retained.',f'Early introduction still has {len(early_steps)} observed simp-step-limit cells across {len({r['model'] for r in early_steps})} files and {len(early_resources)} total observed Lean resource-limit cells across {len({r['model'] for r in early_resources})} files.',f'Definite solver outcomes: {len(definite)} matched pairs, {len(solver_disagreements)} disagreements.', f'Including preprocessing discharge as UNSAT: {len(definite_with_pre)} matched definite pairs, {len(stats["disagreements"])} contradictory answers.','Queries are for exactly N actions, not every trace length up to N. SAT/UNSAT concerns the manifest assertion, not general protocol safety.','Symbolic types and parameters remain abstract or unbounded; concrete #model_check instantiations are not run. SAT for the chosen assertion need not establish a bug in an intended concrete instance.', 'PRE denotes goal closure during preprocessing, separate from solver UNSAT. Query and VC elaboration failures are distinct from model setup.', 'No reconstructed proof is claimed by these measurements; terminal benchmark scaffolds do not establish the trace proposition.','Translation and solver failure durations are not completed timings. Model setup and query/VC elaboration are excluded from query-stage timers. Shared batch_setup_ms must not be summed across cells.', 'Production validation: lake build VeilTest passed 1226 jobs, including proof-header and kernel-checkable early-introduction regression cases.','', 'Included models and queries:']
    if executive:lines=lines[:1]+['','Executive summary',executive,'']+lines[1:]
    for m in models:lines.append(f"{m['model']} | {m.get('path','')} | {model_query(m)} | {m.get('notes','')}")
    lines+=['','Largest successful SAMPLED exact depths (not monotone bounds):']+[json.dumps(r) for r in stats['depth_summary']]
    lines+=['','Outcome counts (all requested cells):',json.dumps(stats['summary']['outcome_counts'],indent=2),'','Completed query cells:',json.dumps(stats['summary']['completed_query_cells']),'','Query completion changes:',json.dumps(stats['summary']['query_completion_changes']),'','Failure counts by variant and phase:']+[str(r) for r in stats['failurecounts']]
    lines+=['','Execution method:','The earlier seven-model benchmark used different assertions and raised budgets, and its backend helper omitted the production compatibility wrapper. Its Veil-preprocessing timings remain exploratory evidence; its backend measurements do not establish production behavior and are not merged here.', 'The sweep uses the explicit original/early trusted SMT pipeline with finite-model-find enabled and standardized query limits; original model definitions and setup are retained. It does not execute every original example command or retain source-specific query solver choices.', 'Model setup is shared within each batch. Exact-N traces are separate Lean commands with separate command budgets; Elab.async=false enforces sequential elaboration. Original/early order alternates across model/depth pairs. Process caches are shared, so these are paired single observations, not independent cold-start repetitions.','A wall watchdog terminates the process group for the active query and restarts unattempted commands. Completed cells retain their emitted queries and timings. Solver replay is a separate sequential batch; shared process wall/setup time is not apportioned to cells. solver_ms measures Smt.solve including native manager/solver creation, SMT-LIB parsing, checkSat, native model values/domain retrieval or unsat-core retrieval. The 10-second tlimit-per limits checkSat; a separate 15-second watchdog covers the active wrapper call. Lean proof/model/trace reconstruction is excluded.',json.dumps({k:metadata.get(k) for k in ['setup_timeout_seconds','query_elaboration_timeout_seconds','pipeline_timeout_seconds','solver_timeout_seconds']},indent=2),'','Paired SMT-query comparison:',json.dumps(comparison,indent=2)]
    if stats.get('logical_comparison'):lines+=['','Additional classical logical-normal-form audit:',json.dumps(stats['logical_comparison']), 'Uses scope-aware bound renaming, quantifier negation and Boolean identities; not an SMT type checker.']
    if environment:lines+=['','Environment:',json.dumps(environment,indent=2)]
    lines+=['','Excluded files:']+[str(e) for e in exclusions]
    lines+=['','Remaining early simplifier step-limit cells:']+[f"{r['model']} depth {r['depth']}: {r['failure_phase']} ({r['failure_kind']})" for r in early_steps]
    lines+=['','Original issue scope:','The original LamportMutexV1 branch referenced by issue #123 is unavailable. This corpus does not establish that the exact original reproducer is fixed. The implemented production change is conservative early introduction of the data/type/instance prefix; per-transition/context-based translation and downstream backend repairs remain future proposals.']
    for appendix in appendices:lines+=['',appendix.name,appendix.read_text()]
    (out/'report.txt').write_text('\n'.join(lines)+'\n')
    style='''body{max-width:1500px;margin:2rem auto;padding:0 1.4rem;font:15px/1.5 system-ui,sans-serif;color:#193345;background:#fff}h1,h2,h3{line-height:1.2}h1{font-size:2.1rem}h2{margin-top:2.3rem}p{max-width:1100px}table{border-collapse:collapse;width:100%;font-size:13px}td,th{border-bottom:1px solid #dce3e8;padding:.45rem;text-align:left}th{background:#edf2f5;position:sticky;top:0}code{font-size:.9em;white-space:pre-wrap}.muted{color:#5a6c79}.notice{background:#fff0d1;padding:.8rem 1rem;border-left:4px solid #d19b32}.bad{background:#fbdcda}.plots{display:grid;grid-template-columns:repeat(auto-fit,minmax(500px,1fr));gap:1rem}img{max-width:100%;height:auto}details{margin:.6rem 0}summary{cursor:pointer;font-weight:600}.scroll{overflow:auto}a{color:#126a8d}.cell{text-align:center;font:600 11px system-ui;min-width:43px}input{font:inherit;padding:.5rem;width:25rem;max-width:90%}.small{font-size:12px}'''
    parts=['<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Symbolic BMC depth sweep</title><style>'+style+'</style></head><body>',f'<h1>Symbolic BMC before and after early introduction</h1><p>{len(models)} model-bearing files × {len(args.depths)} exact action counts × two variants. <strong>{recorded}/{expected} slots have recorded rows; {stats['summary']['pipeline_entered_cells']} pipelines were entered.</strong> Every included file is listed below, including overlapping tutorial and optimized variants.</p>',f'<p>{esc(baseline_definition)}</p>',f'<p class="muted">One sample per cell. Standardized query limits: {args.heartbeats:,} heartbeats, recursion depth {args.recdepth}, Veil simp default {args.simpsteps:,} steps (dependency-local overrides retained). Setup uses its separately recorded options. The earlier seven-model repeated benchmark used different assertions and raised budgets; its backend helper omitted the production compatibility wrapper. Its Veil-preprocessing timings remain exploratory evidence, while its backend measurements do not establish production behavior. None of its measurements are merged into this dataset.</p>',f'<div class="notice"><strong>Do simp errors remain?</strong> The early variant has {len(early_steps)} observed simplifier step-limit cells across {len({r['model'] for r in early_steps})} files and {len(early_resources)} total observed Lean resource-limit cells across {len({r['model'] for r in early_resources})} files. The tables distinguish step, recursion and heartbeat limits and retain the failing phase. Missing results are not successes or failures.</div>',f'<p>Among {len(definite)} matched pairs with definite solver responses, {len(solver_disagreements)} differ. Including preprocessing discharge as UNSAT, {len(definite_with_pre)} pairs have definite answers and {len(stats["disagreements"])} contradict. <a href="definite-disagreements.csv">Contradiction audit</a>. SAT and UNSAT are answers to the exact manifest query; neither is a claim that all trace lengths ≤ N are safe. No reconstructed proof is claimed by the benchmark.</p>','<p>Downloads: <a href="outcomes.csv">all outcomes</a> · <a href="matched-timings.csv">matched completed query timings</a> · <a href="matched-preprocessing-timings.csv">matched preprocessing timings</a> · <a href="failures.csv">failure details</a> · <a href="failure-counts-by-phase.csv">failures by phase</a> · <a href="inventory.csv">inventory and assertions</a> · <a href="queries.csv">emitted query provenance</a> · <a href="report.txt">plain-text report</a>.</p>','<h2>Complete corpus outcomes</h2><img src="figures/outcome-counts.png" alt="Outcome counts at each exact depth for original and early variants">']
    parts.insert(4,'<p class="small muted">'+esc(watchdog_description)+'</p>')
    if executive:
        paragraphs=''.join('<p style="white-space:pre-wrap">'+esc(paragraph)+'</p>' for paragraph in re.split(r'\n\s*\n',executive))
        parts.insert(2,'<section id="executive-summary"><h2>Findings and next steps</h2>'+paragraphs+'<p class="small"><a href="EXECUTIVE_SUMMARY.txt">Download executive summary</a></p></section>')
    for name in matrices:parts.append(f'<details open><summary>{esc(name)}</summary><a href="figures/{name}.svg">SVG</a><img src="figures/{name}.png" alt="Outcome matrix showing every included model in this page"></details>')
    if comparison:parts.append(f'<p>Paired SMT-query check: {comparison["both_queries"]} pairs had two emitted query texts; {comparison["same_after_implication_currying"]} matched after command ordering and implication currying, {comparison["different_after_implication_currying"]} differed, and {comparison["parser_errors"]} had comparison errors. Equality after command ordering and implication currying is positive evidence of the same asserted formula. Textual differences after normalization are inconclusive, not semantic counterexamples. <a href="query-comparison.csv">Comparison details</a>.</p>')
    if logical:=stats.get('logical_comparison'):
        parts.append(f'<p>The additional scope-aware logical audit matches {logical["matched"]}/{logical["pairs"]} pairs after bound renaming, classical quantifier negation and Boolean identities. It does not change solver inputs or certify SMT well-typedness. <a href="logical-query-comparison.csv">Logical audit</a>; <a href="appendices/QUERY_EQUIVALENCE.txt">rules, differences and limits</a>.</p>')
    parts.append(f'<p>Shared model-setup failures blocked {stats["summary"]["model_setup_blocked_cells"]} query slots across {stats["summary"]["model_setup_blocked_files"]} source files. Those are unattempted queries, not independent setup attempts. {stats["summary"]["not_started_cells"]} requested cells have no started result.</p>')
    parts.append(f'<p>Serialized query texts: original {stats["summary"]["completed_query_cells"]["old"]}, early {stats["summary"]["completed_query_cells"]["early"]}. Early alone emitted a query in {stats["summary"]["query_completion_changes"]["early_only"]} matched cells; original alone did so in {stats["summary"]["query_completion_changes"]["old_only"]}. <a href="query-completion-differences.csv">Exact cells</a>. Emission does not guarantee that cvc5 accepts the script: parser errors remain solver errors in the outcomes, and never count as completed solver calls.</p>')
    parts.append('<h2>Largest successful sampled exact depths</h2><p>Each entry is the largest successful sample among the six tested depths, not a monotone depth limit or an all-lengths-up-to-N result. The full CSV retains every successful sampled depth; intermediate failures can coexist with a larger successful sample. A dash means no such observed result. Solver answers concern the selected assertion; PRE is separate preprocessing closure. <a href="sampled-depth-summary.csv">Exact depth summary</a>.</p><div class="scroll"><table><thead><tr><th>Model</th><th>Serialized · old</th><th>Serialized · early</th><th>Definite solver · old</th><th>Definite solver · early</th><th>PRE · old</th><th>PRE · early</th></tr></thead><tbody>')
    for row in stats['depth_summary']:
        cells=[row['model']]
        cells += [row[v+'_highest_sampled_serialized_depth'] for v in VARIANTS]
        cells += [str(row[v+'_highest_sampled_definite_solver_depth'])+' '+row[v+'_solver_answer_at_highest_sample'].upper() if row[v+'_highest_sampled_definite_solver_depth']!='' else '' for v in VARIANTS]
        cells += [row[v+'_highest_sampled_preprocessing_discharge_depth'] for v in VARIANTS]
        parts.append('<tr>'+''.join('<td>'+esc(x if x!='' else '—')+'</td>' for x in cells)+'</tr>')
    parts.append('</tbody></table></div>')
    parts+=['<h2>Failure phases and blocked queries</h2><p>Blocked setup rows mean the query was never attempted. Explicit resource errors remain attributed to the failing phase. nextSimp unfolds transitions, hoist moves higher-order existential witnesses, smtSimp normalizes the resulting local formulas, and SMT embedding converts the first-order problem for the solver.</p><div class="scroll"><table><thead><tr><th>Variant</th><th>Outcome</th><th>Phase</th><th>Count</th></tr></thead><tbody>'+''.join(f'<tr><td>{esc(r["variant"])}</td><td>{esc(STYLES[r["outcome_family"]][0])}</td><td>{esc(r["phase"])}</td><td>{r["count"]}</td></tr>' for r in stats['failurecounts'])+'</tbody></table></div>']
    if phase_panels:
        parts.append('<h2>Remaining costs after early introduction</h2><p>For each file this view selects the largest sampled exact depth with a completed early query. Depths vary and are labeled; this is not a monotone maximum-depth claim. The full matrix records all failures. <a href="selected-early-phase-costs.csv">Exact seconds by phase</a>.</p>')
        for name in phase_panels:parts.append(f'<img src="figures/{name}.png" alt="Selected early query phase costs for every model in this page">')
    parts+=['<h2>Matched completed timings</h2><p>These figures include only cells completed in both variants. They are a subset of the corpus; the outcome matrices above show failures and missing measurements. Failure and timeout durations never appear as completed work. Query-stage times exclude process startup, model setup, query/VC elaboration, and solver execution; the query-plus-solver plot adds the separately measured successful solver call.</p><p>The preprocessing comparison also includes cases whose later SMT embedding or solver failed; only the fully completed Veil phase sequence is timed.</p><div class="plots"><img src="figures/matched-preprocessing-timings.png" alt="Matched fully completed Veil preprocessing timings"><img src="figures/matched-query-timings.png" alt="Matched completed query timing comparison"><img src="figures/matched-completed-timings.png" alt="Matched completed query and solver timing comparison"></div>','<h2>All models, queries, and outcomes</h2><p class="small">Cell code = phase:limit. N nextSimp; H hoist; D destruct/dsimp; M smtSimp; I intros; E embedding; Z normalize; T translate; W serialize; G setup; V query/VC elaboration; Q solver. S simp steps; R recursion; B heartbeat; P process timeout; ! other error. Hover for details.</p><input id="filter" placeholder="Filter model, source path or query" aria-label="Filter models"><div class="scroll"><table id="inventory"><thead><tr><th>Model / exact query</th>']
    for d in args.depths:
        for v in VARIANTS:parts.append(f'<th>{d}<br>{esc(v)}</th>')
    parts.append('</tr></thead><tbody>')
    for m in models:
        name=m['model'];search=name+' '+m.get('path','')+' '+model_query(m)
        parts.append(f'<tr data-search="{esc(search.lower())}"><td><a href="#model-{esc(name)}">{esc(name)}</a><br><span class="small muted">{esc(m.get("path",""))}</span><details><summary>query / notes</summary><code>{esc(model_query(m))}</code><p>{esc(m.get("query_source",""))}</p><p>{esc(m.get("notes",""))}</p></details></td>')
        for d in args.depths:
            for v in VARIANTS:
                r=indexed.get((name,d,v));o=classify(r);_,bg,fg=STYLES[o.family];tip=o.detail
                if r:tip+=' | '+r.get('failure_message','')+' | query seconds: '+str(query_seconds(r))+' | solver status: '+r.get('solver_status','')
                parts.append(f'<td class="cell" style="background:{bg};color:{fg}" title="{esc(tip)}">{esc(o.code)}</td>')
        parts.append('</tr>')
    parts.append('</tbody></table></div><h2>Per-model preprocessing, solver timings, query sizes, and phase costs</h2><p>Solver curves include only completed SAT/UNSAT calls to the entire native Smt.solve wrapper. Timeouts and unknown results appear only in the outcome strip; their elapsed durations are not plotted as completed work.</p>')
    for m in models:
        name=m['model'];parts.append(f'<details id="model-{esc(name)}"><summary>{esc(name)}</summary><p><code>{esc(model_query(m))}</code></p><a href="figures/models/{esc(name)}.svg">SVG</a><img loading="lazy" src="figures/models/{esc(name)}.png" alt="Completed preprocessing, query and solver timing, query size, phase costs and all outcomes for {esc(name)}">')
        parts.append('<details><summary>Exact emitted SMT-LIB queries</summary><table><thead><tr><th>Exact actions</th><th>Original</th><th>Early introduction</th></tr></thead><tbody>')
        for depth in args.depths:parts.append('<tr><td>'+str(depth)+'</td>'+''.join('<td>'+query_artifact_link(indexed.get((name,depth,v)),args)+'</td>' for v in VARIANTS)+'</tr>')
        parts.append('</tbody></table><p class="small muted">A dash means no serialized query was emitted. Query hashes and exact byte counts are in queries.csv; these are the files replayed by the solver.</p></details></details>')
    if environment:parts.append(f'<h2>Environment</h2><p>{esc(environment.get("cpu"))}; {esc(environment.get("logical_cpus_visible"))} logical CPUs visible. {esc(environment.get("lean_version"))}. Python {esc(environment.get("python"))}. <a href="environment.json">Exact dependency revisions, platform, and suite-log hash</a>.</p>')
    if appendices:
        parts.append('<h2>Discussion and technical appendices</h2><p>The implemented change is conservative early introduction of the data/type/instance prefix. Per-transition/context-based translation and downstream backend repairs discussed below are future proposals. The original LamportMutexV1 branch linked in issue #123 is unavailable, so this corpus does not establish that the exact original reproducer is fixed.</p>')
        for appendix in appendices:parts.append(f'<details><summary>{esc(appendix.name)}</summary><a href="appendices/{esc(appendix.name)}">Download</a><pre style="white-space:pre-wrap;font-size:13px;line-height:1.5">{esc(appendix.read_text())}</pre></details>')
    parts.append('<h2>Inventory exclusions</h2><ul>')
    for e in exclusions:parts.append('<li><code>'+esc(json.dumps(e,ensure_ascii=False) if isinstance(e,dict) else e)+'</code></li>')
    parts+=['</ul><h2>Execution method</h2><p>The sweep uses the explicit original/early trusted SMT pipeline with finite-model-find enabled and standardized query limits. Model definitions and setup are retained, while source-specific query solver choices are standardized. It does not execute every original example command or its concrete model-checking configuration.</p><p>Model setup is shared within a batch. Each exact-N trace is a separate Lean command with its own command budget; <code>Elab.async=false</code> enforces sequential elaboration. Original/early ordering alternates across model/depth pairs. Process caches are shared: these are paired single observations, not independent cold-start repetitions. If the active query hits a wall watchdog, its process group is terminated and unattempted commands restart. Finished cells keep their recorded outputs. Solver replay runs separately. The recorded solver time measures the whole <code>Smt.solve</code> wrapper: native manager/solver creation, SMT-LIB parsing, <code>checkSat</code>, and native model-domain/value or unsat-core retrieval. It excludes Lean proof/model reconstruction and trace rendering. The 10-second <code>tlimit-per</code> applies to <code>checkSat</code>; a separate 15-second watchdog bounds the whole active solver call. Shared Lean process startup is excluded.</p><h2>Validation</h2><p>The production change passed <code>lake build VeilTest</code> (1226 jobs), including proof-header compatibility and kernel-checkable early-introduction regression cases. This suite result is separate from the timing scaffold, which reconstructs no SMT proof.</p><h2>Interpretation and limits</h2><p>One observation measures feasibility and approximate cost; it does not establish a stable speedup distribution or confidence interval. Different depths can have different SAT/UNSAT answers and resource outcomes. No monotone maximum working depth is inferred. The exact query, source path, resource settings, stage records and emitted SMT-LIB should be consulted together. Symbolic types and parameters remain abstract or unbounded: these runs do not use the concrete #model_check instantiations. SAT for a chosen query can include behaviors outside an intended concrete instance. Where a source has several safety properties, the manifest records the selected assertion and its scope.</p><p>Model-setup and query/VC-elaboration failures remain in the inventory rather than silently dropping examples. G:— means the query was not attempted because model setup failed. Shared batch setup measurements must not be summed across cells. PRE means preprocessing closed the goal without asking the solver, and is separate from solver UNSAT. Process timeouts are distinct from solver timeouts and from explicit Lean resource errors. A successful translation with a timed-out solver is still represented as a solver timeout, while its completed query-stage time may appear in the translation comparison.</p><script>document.getElementById("filter").addEventListener("input",function(){let q=this.value.toLowerCase();document.querySelectorAll("#inventory tbody tr").forEach(r=>r.hidden=!r.dataset.search.includes(q))});document.querySelectorAll("a[href^=\"#model-\"]").forEach(a=>a.addEventListener("click",()=>{let d=document.querySelector(a.getAttribute("href"));if(d)d.open=true}));</script></body></html>']
    (out/'index.html').write_text('\n'.join(parts))


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--manifest',type=Path,required=True);ap.add_argument('--exclusions',type=Path);ap.add_argument('--results',type=Path,required=True);ap.add_argument('--out-dir',type=Path,required=True)
    ap.add_argument('--depths',nargs='+',type=int,default=DEPTHS);ap.add_argument('--profile',default='default');ap.add_argument('--rows-per-page',type=int,default=25)
    ap.add_argument('--heartbeats',type=int,default=200000);ap.add_argument('--recdepth',type=int,default=512);ap.add_argument('--simpsteps',type=int,default=100000)
    ap.add_argument('--appendix',type=Path,action='append',help='Technical discussion text appendix; defaults to standard files beside manifest')
    ap.add_argument('--executive-summary',type=Path,help='Plain-text executive synthesis; defaults to EXECUTIVE_SUMMARY.txt beside the manifest')
    ap.add_argument('--environment',type=Path,help='Environment JSON; defaults to environment.json beside the manifest')
    ap.add_argument('--query-comparison',type=Path,help='Optional completed paired-query comparison CSV from compare_queries.py')
    ap.add_argument('--logical-comparison',type=Path,help='Optional stronger logical-normal-form audit CSV')
    ap.add_argument('--tables-only',action='store_true')
    args=ap.parse_args();args.out_dir.mkdir(parents=True,exist_ok=True)
    if args.appendix is None:args.appendix=[args.manifest.parent/name for name in ['INVENTORY_METHODS.txt','DATASET_PROVENANCE.txt','CONTROL_FINDINGS.txt','DIAGNOSTICS_README.txt','PIPELINE_PARITY_AUDIT.txt','BACKEND_FINDINGS.txt','AWS_EMBEDDING_REPAIR_PLAN.txt','PAXOS_UNIVERSE_FINDINGS.txt','SMT_PARSER_FINDINGS.txt','QUERY_EQUIVALENCE.txt','TRANSITION_FORM_FINDINGS.txt','HOISTING_FOLLOWUPS.txt','LOCAL_NORMALIZATION_DESIGN.txt','NEXT_FIXES.txt','ARCHITECTURE_NEXT_STEPS.txt']]
    if any(p.exists() for p in args.appendix):
        (args.out_dir/'appendices').mkdir(exist_ok=True)
        for p in args.appendix:
            if p.exists():(args.out_dir/'appendices'/p.name).write_bytes(p.read_bytes())
    if args.executive_summary is None:args.executive_summary=args.manifest.parent/'EXECUTIVE_SUMMARY.txt'
    if args.executive_summary.exists():(args.out_dir/'EXECUTIVE_SUMMARY.txt').write_bytes(args.executive_summary.read_bytes())
    if args.environment is None:args.environment=args.manifest.parent/'environment.json'
    if args.environment.exists():(args.out_dir/'environment.json').write_bytes(args.environment.read_bytes())
    models,exclusions,indexed,by_cell=load(args);stats=export_tables(args.out_dir,models,indexed,args.depths,by_cell)
    if args.query_comparison and args.query_comparison.exists():
        comparisons=[r for r in read_csv(args.query_comparison) if (not r.get('profile') or r['profile']==args.profile) and int(r['depth']) in args.depths and r['model'] in {m['model'] for m in models}];truth=lambda value:str(value).lower()=='true'
        comparison={'pairs':len(comparisons),'both_queries':sum(truth(r['both_queries']) for r in comparisons),'same_after_implication_currying':sum(truth(r['same_after_implication_currying']) for r in comparisons),'different_after_implication_currying':sum(str(r['same_after_implication_currying']).lower()=='false' for r in comparisons),'parser_errors':sum(bool(r.get('comparison_error')) for r in comparisons)}
        stats['comparison']=comparison;stats['summary']['paired_query_comparison']=comparison
        write_csv(args.out_dir/'query-comparison.csv',comparisons)
        (args.out_dir/'summary.json').write_text(json.dumps(stats['summary'],indent=2)+'\n')
    if args.logical_comparison and args.logical_comparison.exists():
        logical=[r for r in read_csv(args.logical_comparison) if int(r['depth']) in args.depths and r['model'] in {m['model'] for m in models}]
        stats['logical_comparison']={'pairs':len(logical),'matched':sum(str(r['same_after_logical_normalization']).lower()=='true' for r in logical)}
        stats['summary']['paired_logical_comparison']=stats['logical_comparison']
        write_csv(args.out_dir/'logical-query-comparison.csv',logical)
        (args.out_dir/'summary.json').write_text(json.dumps(stats['summary'],indent=2)+'\n')
    config={k:([str(p) for p in v] if k=='appendix' else str(v) if isinstance(v,Path) else v) for k,v in vars(args).items()};config['inputs']={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [args.manifest,args.exclusions,args.results/'runs.csv',args.results/'stages.csv',args.results/'metadata.json',args.query_comparison,args.logical_comparison,args.environment,args.executive_summary]+args.appendix if p is not None and p.exists()};config['model_count']=len(models)
    (args.out_dir/'report-config.json').write_text(json.dumps(config,indent=2)+'\n')
    matrices=[];phase_panels=[]
    if not args.tables_only:
        plt=setup_plots();figures=args.out_dir/'figures';figures.mkdir(exist_ok=True);(figures/'models').mkdir(exist_ok=True)
        matrices=plot_matrices(plt,figures,models,indexed,args);plot_counts(plt,figures,stats,models,args);plot_matched(plt,figures,stats,args);plot_matched(plt,figures,stats,args,metric='completed');plot_matched(plt,figures,stats,args,metric='preprocessing')
        phase_panels=plot_remaining_phases(plt,figures,models,indexed,by_cell,args)
        for model in models:plot_model(plt,figures/'models',model,indexed,by_cell,args)
    write_report(args.out_dir,models,exclusions,indexed,stats,matrices,args,phase_panels)
    print(f'Reported {len(models)} models; {len(indexed)} recorded cells; {len(stats["matches"])} matched completed-query pairs; {len(stats["disagreements"])} definite disagreements.')
if __name__=='__main__':main()
