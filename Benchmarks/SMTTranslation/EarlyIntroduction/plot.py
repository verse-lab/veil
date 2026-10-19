#!/usr/bin/env python3
"""Plot benchmark.py CSVs. Requires matplotlib (pip install matplotlib).

python3 plot.py --results ./results --out-dir ./figures
All plotted times are completed stages, never the elapsed time of a failure.
Preprocessing points show medians and min/max of up to three repetitions.
Query endpoint timings are single observed runs, measured separately.
"""
import argparse,csv,json,statistics
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import Rectangle
from matplotlib.ticker import ScalarFormatter,MaxNLocator,NullFormatter

COLORS={'current':'#C65336','early':'#176F91'}
LABELS={'current':'Original order','early':'Early introduction'}
PHASES=[('nextSimp','#247C9C'),('hoist','#E6AB4A'),('other','#B7C4CF')]

def rows(path):
    with path.open() as f:return list(csv.DictReader(f))
def median(xs):return statistics.median(xs)
def save(fig,out,name):
    fig.savefig(out/(name+'.png'),dpi=200,facecolor='white')
    fig.savefig(out/(name+'.svg'),facecolor='white')
    plt.close(fig)
def setup():
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.titlesize':12,'axes.titleweight':'bold','axes.labelsize':10,'axes.spines.top':False,'axes.spines.right':False,'axes.edgecolor':'#ADB7BF','axes.labelcolor':'#2E3841','text.color':'#172B3A','xtick.color':'#46525B','ytick.color':'#46525B','grid.color':'#DEE4E8','grid.linewidth':.7,'svg.fonttype':'none','figure.dpi':120,'savefig.bbox':'tight'})

def status_text(data,model,mode):
    rs=[r for r in data if r['model']==model and r['mode']==mode]
    failed=[r for r in rs if r['status']=='failed']
    interrupted=[r for r in rs if r['status']=='interrupted' and not any(q['depth']==r['depth'] and q['status']=='complete' for q in rs)]
    if failed:
        r=failed[0];return f"{LABELS[mode]}: depth {r['depth']} failed ({r['failure_stage']}); later depths untested"
    if interrupted:
        r=interrupted[0];return f"{LABELS[mode]}: depth {r['depth']} interrupted by model time cap"
    if not any(r['status']=='complete' for r in rs):return f"{LABELS[mode]}: no completed measurement"
    return ''

def summaries(data):
    groups={}
    for r in data:groups.setdefault((r['model'],r['mode'],int(r['depth'])),[]).append(r)
    out=[]
    for (model,mode,depth),rs in groups.items():
        good=[r for r in rs if r['status']=='complete'];ts=[int(r['preprocessing_ms'])/1000 for r in good]
        out.append(dict(model=model,mode=mode,depth=depth,n=len(ts),median_seconds=median(ts) if ts else '',min_seconds=min(ts) if ts else '',max_seconds=max(ts) if ts else '',statuses=';'.join(r['status'] for r in rs)))
    return out

def draw_lines(ax,summary,model,depths,small=False):
    for mode in ['current','early']:
        pts=sorted([r for r in summary if r['model']==model and r['mode']==mode and r['n']],key=lambda r:r['depth'])
        if not pts:continue
        xs=[r['depth'] for r in pts];ys=[r['median_seconds'] for r in pts]
        errs=[[r['median_seconds']-r['min_seconds'] for r in pts],[r['max_seconds']-r['median_seconds'] for r in pts]]
        ax.errorbar(xs,ys,yerr=errs,label=LABELS[mode],color=COLORS[mode],marker='o',ms=4 if small else 6,lw=1.8,capsize=3,elinewidth=1)
        for r in pts:
            if r['n']<3:ax.annotate(f"n={r['n']}",(r['depth'],r['median_seconds']),xytext=(4,5),textcoords='offset points',fontsize=8,color=COLORS[mode])
    ax.set_xscale('log',base=2);ax.set_xticks(depths,labels=[str(d) for d in depths]);ax.set_xlim(min(depths)*.85,max(depths)*1.2)
    ax.grid(axis='y',zorder=0);ax.set_axisbelow(True);ax.set_xlabel('Trace depth (actions)')
    ax.set_ylabel('Preprocessing time (seconds)')
    if small:ax.tick_params(labelsize=9)

def foot(fig,y=.01):
    fig.text(.04,y,'Medians with min–max bars; 3 sequential repetitions unless noted. Stage times exclude startup, model generation, instrumentation and SMT solving.\nHeartbeat/recursion limits relaxed (0 / 10,000); default simp step cap (100,000). Elaboration synchronous; variants alternate order. See CSVs for all statuses.',fontsize=8,color='#53626D',va='bottom')

def draw_phases(ax,data,stages,model):
    depths=sorted({int(r['depth']) for r in data if r['model']==model})
    common=[d for d in depths if all(any(r['model']==model and r['mode']==m and int(r['depth'])==d and r['status']=='complete' for r in data) for m in ['current','early'])]
    if not common:ax.text(.5,.5,'No depth completed in both variants',ha='center',va='center',transform=ax.transAxes);ax.set_axis_off();return
    depth=max(common)
    reference_total=max(int(r['preprocessing_ms'])/1000 for r in data if r['model']==model and int(r['depth'])==depth and r['status']=='complete')
    for y,mode in enumerate(['current','early']):
        complete={(r.get('batch','main'),int(r['repeat'])) for r in data if r['model']==model and r['mode']==mode and int(r['depth'])==depth and r['status']=='complete'}
        totals={'nextSimp':[],'hoist':[],'other':[]}
        for batch,rep in complete:
            rs=[r for r in stages if r['model']==model and r['mode']==mode and int(r['depth'])==depth and int(r['repeat'])==rep and r.get('batch','main')==batch and r['kind']=='STAGE']
            totals['nextSimp'].append(sum(int(r['milliseconds']) for r in rs if r['stage']=='nextSimp')/1000)
            totals['hoist'].append(sum(int(r['milliseconds']) for r in rs if r['stage']=='hoist')/1000)
            totals['other'].append(sum(int(r['milliseconds']) for r in rs if r['stage'] not in ['nextSimp','hoist'])/1000)
        left=0
        for phase,color in PHASES:
            value=median(totals[phase]);ax.barh(y,value,left=left,color=color,height=.48,label=phase if y==0 else None)
            if value>max(.25,.10*reference_total):ax.text(left+value/2,y,f'{value:.2f}',ha='center',va='center',fontsize=9,color='white' if phase=='nextSimp' else '#223744')
            left+=value
        ax.text(left,y,f'  {left:.2f} s',va='center',fontsize=10,fontweight='bold')
    ax.set_yticks([0,1],labels=[LABELS['current'],LABELS['early']]);ax.invert_yaxis();ax.set_ylim(1.7,-.7);ax.set_xlim(0,ax.get_xlim()[1]*1.24)
    ax.set_title(f'Where time goes at depth {depth}',loc='left',pad=15)
    ax.set_xlabel('Seconds (median of each phase)');ax.grid(axis='x');ax.set_axisbelow(True);ax.legend(loc='lower left',bbox_to_anchor=(0,-.39),ncol=3,frameon=False)

def solver_matrix(path,models,out):
    solver=rows(path)
    keyed={(r['model'],int(r['depth']),r['mode']):r for r in solver}
    fig,ax=plt.subplots(figsize=(11.5,7.8))
    ax.set_xlim(-1.45,4.05);ax.set_ylim(-1.3,8.25);ax.axis('off')
    styles={'sat':('#D8EFE6','#195E48'),'unsat':('#DCE9F4','#235678'),'timeout':('#F9E7C5','#805510'),'missing':('#E9EDF0','#596771')}
    for y,model in zip(reversed(range(len(models))),models):
        ax.text(-.12,y+.44,model,ha='right',va='center',fontsize=12,fontweight='bold')
        for x,(depth,mode) in enumerate([(4,'old'),(4,'early'),(8,'old'),(8,'early')]):
            r=keyed.get((model,depth,mode),keyed.get((model,depth,'current' if mode=='old' else mode)))
            status=r['status'] if r else 'missing'
            if status in ['sat','unsat']:
                style=status;ms=r.get('isolated_solver_ms','');label=status.upper();detail=f"{int(ms)/1000:.2f} s" if ms else ''
            elif 'TIMEOUT' in status.upper():style='timeout';label='TIMEOUT';detail='10 s limit'
            else:style='missing';label='No query';detail='preprocessing failed'
            bg,fg=styles[style]
            ax.add_patch(Rectangle((x+.025,y+.03),.95,.82,facecolor=bg,edgecolor='white',linewidth=1.5))
            ax.text(x+.5,y+.54,label,ha='center',va='center',fontsize=11,fontweight='bold',color=fg)
            ax.text(x+.5,y+.28,detail,ha='center',va='center',fontsize=9,color=fg)
    ax.text(1,7.6,'Depth 4',ha='center',fontsize=13,fontweight='bold')
    ax.text(3,7.6,'Depth 8',ha='center',fontsize=13,fontweight='bold')
    for x,label in enumerate(['Original','Early introduction','Original','Early introduction']):ax.text(x+.5,7.12,label,ha='center',fontsize=10)
    ax.plot([2,2],[-.05,7.8],color='#AFBAC3',lw=1)
    fig.suptitle('SMT outcomes for the measured trace queries',x=.04,y=.98,ha='left',fontsize=19,fontweight='bold')
    fig.text(.04,.90,'One isolated solver run per query; timeout cells are censored, not completed solves.',fontsize=11,color='#53626D')
    fig.text(.04,.055,'''Queries come from the finalized data-prefix helper benchmark. cvc5 uses the trusted Veil options and a 10-second limit.
SAT/UNSAT refer to the selected bounded trace assertions, not protocol safety in general. These samples do not establish a solver speedup.
A missing query records preprocessing failure; it is distinct from a solver timeout. Exact results and assertions are retained in the solver CSV.''',fontsize=8.5,color='#53626D')
    fig.subplots_adjust(left=.03,right=.98,top=.88,bottom=.13)
    save(fig,out,'overview-solver-outcomes')

def deepest_phases(data,stages,models,out):
    fig,ax=plt.subplots(figsize=(12.5,6.8))
    phases=[('nextSimp','#247C9C'),('hoist','#E6AB4A'),('other Veil','#B7C4CF'),('SMT embedding','#7862A1'),('other SMT','#C8BCDD')]
    labels=[];max_total=0
    for y,model in enumerate(models):
        rs=[r for r in data if r['model']==model and r['mode']=='early' and r['status']=='complete' and r['smt_status']=='complete']
        if not rs:labels.append(model+' (no complete query)');continue
        r=max(rs,key=lambda r:int(r['depth']));labels.append(f"{model} · depth {r['depth']}")
        ss=[s for s in stages if s['model']==model and s['mode']=='early' and s['depth']==r['depth'] and s['repeat']==r['repeat'] and s.get('batch','main')==r.get('batch','main')]
        times={'nextSimp':0.,'hoist':0.,'other Veil':0.,'SMT embedding':0.,'other SMT':0.}
        for s in ss:
            if s['kind']=='STAGE':key=s['stage'] if s['stage'] in ['nextSimp','hoist'] else 'other Veil'
            elif s['kind']=='SMT_STAGE':key='SMT embedding' if s['stage']=='embedding' else 'other SMT'
            else:continue
            times[key]+=int(s['milliseconds'])/1000
        total=sum(times.values());max_total=max(max_total,total);left=0
        for phase,color in phases:
            value=times[phase];ax.barh(y,value,left=left,color=color,height=.62,label=phase if y==0 else None)
            if value>max(1,total*.10):ax.text(left+value/2,y,f'{value:.1f}',ha='center',va='center',fontsize=9,color='white' if phase in ['nextSimp','SMT embedding'] else '#263E4C')
            left+=value
        ax.text(total+.25,y,f'{total:.1f} s',va='center',fontsize=10,fontweight='bold')
    ax.set_yticks(range(len(models)),labels=labels);ax.invert_yaxis();ax.set_xlim(0,max_total*1.14)
    ax.set_xlabel('Sum of timed stages (seconds)');ax.grid(axis='x');ax.set_axisbelow(True)
    ax.legend(loc='upper left',bbox_to_anchor=(0,-.13),ncol=5,frameon=False,fontsize=9)
    fig.suptitle('What remains after early introduction',x=.035,ha='left',fontsize=20,fontweight='bold',y=.98)
    fig.text(.035,.90,'Deepest completed serialized query for each model; depths differ and are shown beside each bar.',fontsize=11,color='#53626D')
    fig.text(.035,.035,'One observed first-repetition query per row, not repetition medians. Includes Veil preprocessing, lean-smt preprocessing, translation and serialization.\nStartup, model generation, instrumentation and solver time are excluded. Resource settings match the preprocessing figures.',fontsize=8.5,color='#53626D')
    fig.subplots_adjust(left=.24,right=.97,top=.84,bottom=.23)
    save(fig,out,'overview-remaining-phases')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--results',type=Path,required=True);ap.add_argument('--out-dir',type=Path,required=True);ap.add_argument('--solver-results',type=Path);a=ap.parse_args()
    a.out_dir.mkdir(parents=True,exist_ok=True);data=rows(a.results/'runs.csv');stages=rows(a.results/'stages.csv');meta=json.loads((a.results/'metadata.json').read_text());setup()
    summary=summaries(data)
    with (a.out_dir/'summary.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=summary[0].keys());w.writeheader();w.writerows(summary)
    models=[m[0] for m in meta['models']];depths=meta['depths']
    fig,axes=plt.subplots(2,4,figsize=(16,8.2));axes=axes.flatten()
    for ax,model in zip(axes,models):
        draw_lines(ax,summary,model,depths,True);ax.set_yscale('log');ax.set_ylim(.1,40);ax.set_yticks([.1,1,10],labels=['0.1','1','10']);ax.yaxis.set_minor_formatter(NullFormatter());ax.set_title(model,loc='left',pad=30)
        notes=[status_text(data,model,m) for m in ['current','early']];notes=[n for n in notes if n]
        if notes:ax.text(0,1.03,'\n'.join(n.replace('; later depths untested','; later untested').replace('Original order','Original').replace('Early introduction','Early') for n in notes),transform=ax.transAxes,fontsize=7.3,va='bottom',color='#7E432D',wrap=True)
    for ax in axes[len(models):]:ax.axis('off')
    handles=[Line2D([0],[0],color=COLORS[m],marker='o',lw=2,label=LABELS[m]) for m in ['current','early']]
    axes[-1].legend(handles=handles,loc='upper left',frameon=False,fontsize=12)
    axes[-1].text(0,.60,'Completed measurements only.\nBars show repetition range.\n\nLogarithmic time axis.\nFailures are annotations,\nnot completed timing points.\n\nSMT solver time is excluded.',transform=axes[-1].transAxes,fontsize=11,linespacing=1.5,va='top')
    fig.suptitle('Preprocessing with early introduction across seven Veil models',x=.04,ha='left',fontsize=20,fontweight='bold',y=.995)
    fig.subplots_adjust(left=.06,right=.99,bottom=.15,top=.88,hspace=.75,wspace=.38);foot(fig,.025);save(fig,a.out_dir,'overview-preprocessing')
    for model in models:
        fig,axes=plt.subplots(1,2,figsize=(12,5.7),gridspec_kw={'width_ratios':[1.1,1]})
        draw_lines(axes[0],summary,model,depths);axes[0].set_ylim(bottom=0);axes[0].legend(frameon=False,loc='upper left')
        draw_phases(axes[1],data,stages,model)
        notes='\n'.join(filter(None,[status_text(data,model,m) for m in ['current','early']]))
        fig.suptitle(model+': cost of trace preprocessing',x=.055,ha='left',fontsize=18,fontweight='bold',y=.98)
        if notes:fig.text(.055,.88,notes,fontsize=9,color='#7E432D',va='top')
        fig.subplots_adjust(left=.075,right=.98,top=.77,bottom=.27,wspace=.40);foot(fig,.03);save(fig,a.out_dir,model+'-preprocessing')
    # One query measurement per cell: keep it explicitly separate from the repeated main benchmark.
    fig,axes=plt.subplots(2,4,figsize=(16,8.2));axes=axes.flatten()
    endpoints=[]
    for ax,model in zip(axes,models):
        for mode in ['current','early']:
            rs=sorted([r for r in data if r['model']==model and r['mode']==mode and r['smt_status']=='complete'],key=lambda r:int(r['depth']))
            xs=[int(r['depth']) for r in rs];ys=[(int(r['preprocessing_ms'])+int(r['smt_ms']))/1000 for r in rs if r['preprocessing_ms']]
            if len(xs)==len(ys):ax.plot(xs,ys,color=COLORS[mode],marker='o',lw=1.8)
            for r in rs:endpoints.append(dict(model=model,mode=mode,depth=r['depth'],preprocessing_seconds=int(r['preprocessing_ms'])/1000 if r['preprocessing_ms'] else '',downstream_smt_seconds=int(r['smt_ms'])/1000,query_bytes=r['query_bytes']))
        ax.set_xscale('log',base=2);ax.set_xticks(depths,labels=depths);ax.set_yscale('log');ax.set_ylim(.1,80);ax.set_yticks([.1,1,10],labels=['0.1','1','10']);ax.yaxis.set_minor_formatter(NullFormatter());ax.set_xlim(min(depths)*.85,max(depths)*1.2);ax.grid(axis='y');ax.set_title(model,loc='left');ax.set_xlabel('Trace depth (actions)');ax.set_ylabel('Sum of timed stages (seconds)')
    for ax in axes[len(models):]:ax.axis('off')
    axes[-1].legend(handles=handles,loc='upper left',frameon=False,fontsize=12)
    axes[-1].text(0,.60,'One observed query per cell.\n\nIncludes Veil preprocessing,\nlean-smt preprocessing,\ntranslation and serialization.\n\nExcludes startup/modelgen\nand SMT solver execution.\nMissing endpoints unmeasured.',transform=axes[-1].transAxes,fontsize=11,linespacing=1.4,va='top')
    fig.suptitle('Measured stages through serialized SMT queries',x=.04,ha='left',fontsize=20,fontweight='bold',y=.995)
    fig.subplots_adjust(left=.06,right=.99,bottom=.15,top=.89,hspace=.52,wspace=.40)
    fig.text(.04,.025,'Single first-repetition observations; no confidence intervals. Only fully completed preprocessing + SMT-output stage sums are plotted.\nTrusted Veil preprocessing (embedBool=false); queries use logic ALL. No solver is run by this benchmark. Same resource limits as the preprocessing figure.',fontsize=8,color='#53626D');save(fig,a.out_dir,'overview-smt-output')
    if endpoints:
        with (a.out_dir/'smt-output.csv').open('w',newline='') as f:w=csv.DictWriter(f,fieldnames=endpoints[0].keys());w.writeheader();w.writerows(endpoints)
    deepest_phases(data,stages,models,a.out_dir)
    if a.solver_results:solver_matrix(a.solver_results,models,a.out_dir)
    print(f'Wrote {len(models)+3+bool(a.solver_results)} figure pairs to {a.out_dir}')
if __name__=='__main__':main()
