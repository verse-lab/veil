#!/usr/bin/env python3
"""Sequential, repeated Veil preprocessing/SMT-output benchmark for issue #123.

Usage (after lake build Veil):
  python3 benchmark.py --repo /path/to/veil --out-dir ./results

Every cell generates a standalone measurement scaffold (ending with sorry),
not a proof. The original and early-introduction pipelines are explicit. The early helper
introduces only data/type/instance prefix binders, stopping before propositions;
independent of the installed veil_bmc order. Stages exclude Lean startup,
model generation, instrumentation, and solver execution. Resource overrides:
maxHeartbeats=0; maxRecDepth=10000; default simp maxSteps is unchanged (100000).
Three repetitions per successful preprocessing cell. Only repetition 1 also
measures downstream SMT preprocessing, translation, and serialization. Timed
runs are sequential; alternate variant order at every repetition/depth. Each
model is elaborated once and shares process caches; model timeout is 180 seconds. Larger
depths after a failed variant are marked untested, not inferred failures.
"""
import argparse, csv, hashlib, json, os, platform, re, subprocess, time
from pathlib import Path

MODELS = [
 ('Ring','Examples/Ivy/Ring.lean','∃ l, leader l','Ordered ring; quantified binary relations'),
 ('DieHard','Examples/Puzzles/DieHard.lean','big = 4','Scalar natural numbers; six actions'),
 ('TwoPhaseCommit','Examples/Ivy/TwoPhaseCommit.lean','∃ n, decide_commit n','Commit protocol; quantified relations'),
 ('RicartAgrawala','Examples/Ivy/RicartAgrawala.lean','∃ n, holds n','Mutual exclusion; two actions'),
 ('MultiSigAll','Examples/Ivy/MultiSigAll.lean','∃ n k v d, paid n k v d','Five sorts; high-arity relations'),
 ('Peterson','Examples/TLA/Peterson.lean','∃ p, pc p critical ∨ pc p release','Finite enums; mutual exclusion'),
 ('FloodSet','Examples/Synchronous/FloodSet.lean','∃ n v, decision n v','Higher-order delivery choices; arithmetic'),
]
HELPER = r'''
open Lean Elab Tactic Meta Veil

meta partial def introDataPrefix (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let .forallE _ domain _ _ := target.consumeMData | return goal
  if ← isProp domain then return goal
  let (_, goal') ← withOptions (fun opts => opts.setBool `tactic.hygienic false) goal.intro1
  introDataPrefix goal'

elab "intro_data_prefix" : tactic => do
  liftMetaTactic1 fun goal => return some (← introDataPrefix goal)


meta def benchPrint (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

elab "bench_stage " key:str label:str t:tactic : tactic => do
  let start ← IO.monoMsNow
  try
    evalTactic t
    benchPrint s!"STAGE {key.getString} {label.getString} ms={(← IO.monoMsNow)-start}"
  catch ex =>
    benchPrint s!"FAILED {key.getString} {label.getString} ms={(← IO.monoMsNow)-start}: {← ex.toMessageData.toString}"
    throw ex

elab "bench_run " label:str marker:str t:tactic : tactic => do
  if ← System.FilePath.pathExists marker.getString then
    benchPrint s!"RUN_SKIPPED {label.getString} prior_failure"
    evalTactic (← `(tactic| sorry))
  else
    benchPrint s!"RUN_BEGIN {label.getString}"
    let saved ← saveState
    try
      evalTactic t
      benchPrint s!"RUN_COMPLETE {label.getString}"
    catch _ =>
      saved.restore
      IO.FS.writeFile marker.getString "failed"
      benchPrint s!"RUN_FAILED {label.getString}"
    evalTactic (← `(tactic| sorry))

elab "bench_smt_pipeline " key:str path:str : tactic => do
  let saved ← saveState
  try
    withMainContext do
      let hs := (← getFVarIds (← Veil.getPropsInContext)).map Expr.fvar
      let goal ← getMainGoal
      let mut mv := (← Meta.mkFreshExprMVar (← goal.getType)).mvarId!
      mv ← mv.cleanup (← hs.foldlM (fun s h => return (← (Expr.collectFVars h).run s).snd) {}).fvarIds
      let mut hs := hs
      let steps : Array (String × (MVarId → Array Expr → MetaM Smt.Preprocess.Result)) := #[
        ("pushHints", Smt.Preprocess.pushHintsToCtx),
        ("smt-intros", Smt.Preprocess.intros),
        ("negateGoal", Smt.Preprocess.negateGoal),
        ("normalize", Smt.Preprocess.normalize),
        ("embedding", Smt.Preprocess.embeddingWithConfig { embedBool := false })]
      for (name, step) in steps do
        let start ← IO.monoMsNow
        let r ← mv.withContext <| step mv hs
        mv := r.mv
        hs := r.hs
        benchPrint s!"SMT_STAGE {key.getString} {name} ms={(← IO.monoMsNow)-start}"
      let start ← IO.monoMsNow
      let cmds ← mv.withContext do
        let (fvNames, _) ← Smt.genUniqueFVarNames
        Smt.prepareSmtQuery hs.toList fvNames
      benchPrint s!"SMT_STAGE {key.getString} translate ms={(← IO.monoMsNow)-start} commands={cmds.length}"
      let start ← IO.monoMsNow
      let query := Smt.Translate.Command.cmdsAsQuery (.setLogic "ALL" :: cmds ++ [.checkSat])
      IO.FS.writeFile path.getString query
      benchPrint s!"SMT_STAGE {key.getString} serialize ms={(← IO.monoMsNow)-start} bytes={query.utf8ByteSize}"
      benchPrint s!"PIPELINE_COMPLETE {key.getString}"
  catch ex =>
    benchPrint s!"PIPELINE_FAILED {key.getString}: {← ex.toMessageData.toString}"
  saved.restore
'''
CURRENT = '''    bench_stage "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "intros" veil_intros
    bench_stage "destruct" veil_destruct
    bench_stage "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
'''

def source_for(repo, out, model, depths, repeats):
    name, relative, assertion, _ = model
    original = (repo / relative).read_text()
    if name == 'Ring':
        prefix = original.split('set_option veil.smt.trust false',1)[0]
    else:
        boundary = re.search(r'^\s*(?:#time\s+)?#gen_spec\b', original, re.M)
        assert boundary, relative
        prefix = original[:boundary.start()]
    source = prefix.replace('public import Veil\n','public import Veil\n'+HELPER+'\n',1)
    source += '\n#gen_spec\nset_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 10000\n'
    for di,depth in enumerate(depths):
      for rep in range(1,repeats+1):
       for mode in (['current','early'] if (di+rep)%2 else ['early','current']):
        key = f'{name}_{mode}_{depth}_{rep}'
        stages = ('    bench_stage "early_intros" intro_data_prefix\n' if mode=='early' else '') + CURRENT
        stages = stages.replace('bench_stage ',f'bench_stage "{key}" ')
        if rep == 1:
            stages += f'    bench_smt_pipeline "{key}" "{out / "queries" / (key+".smt2")}"\n'
        marker = out / 'markers' / (name+'_'+mode)
        source += f'\nunsat trace [bench_{mode}_{depth}_{rep}] {{\n  any {depth} actions\n  assert ({assertion})\n}} by\n  bench_run "{key}" "{marker}" (\n{stages}  )\n'
    return source+f'\nend {name}\n'

def parse_output(output, model, mode, depth, repeats):
    result=[]
    for rep in range(1,repeats+1):
        key=f'{model}_{mode}_{depth}_{rep}'
        stage=[]
        for kind,label,ms,extra in re.findall(r'^(STAGE|SMT_STAGE|FAILED) '+re.escape(key)+r' (\S+) ms=(\d+)(.*)$',output,re.M):
            stage.append(dict(model=model,mode=mode,depth=depth,repeat=rep,kind=kind,stage=label,milliseconds=int(ms),bytes=(re.search(r'bytes=(\d+)',extra) or [None,''])[1],commands=(re.search(r'commands=(\d+)',extra) or [None,''])[1]))
        preproc=[r for r in stage if r['kind']=='STAGE']
        status='complete' if f'RUN_COMPLETE {key}' in output else ('failed' if f'RUN_FAILED {key}' in output else ('skipped_prior_failure' if f'RUN_SKIPPED {key}' in output else ('interrupted' if f'RUN_BEGIN {key}' in output else 'not_started')))
        smt_status='complete' if f'PIPELINE_COMPLETE {key}' in output else ('failed' if f'PIPELINE_FAILED {key}' in output else ('not_measured' if rep>1 else 'not_reached'))
        failed=next((r for r in stage if r['kind']=='FAILED'),None)
        summary=dict(model=model,mode=mode,depth=depth,repeat=rep,status=status,preprocessing_ms=sum(r['milliseconds'] for r in preproc) if status=='complete' else '',nextSimp_ms=next((r['milliseconds'] for r in preproc if r['stage']=='nextSimp'),''),hoist_ms=next((r['milliseconds'] for r in preproc if r['stage']=='hoist'),''),failure_stage=failed['stage'] if failed else '',failure_elapsed_ms=failed['milliseconds'] if failed else '',smt_status=smt_status,smt_ms=sum(r['milliseconds'] for r in stage if r['kind']=='SMT_STAGE') if smt_status=='complete' else '',query_bytes=next((r['bytes'] for r in stage if r['stage']=='serialize'),''))
        result.append((summary,stage))
    return result

def write_csv(path, rows):
    if not rows: return
    with path.open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0].keys());w.writeheader();w.writerows(rows)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--out-dir',type=Path,default=Path(__file__).parent/'results')
    ap.add_argument('--depths',type=int,nargs='+',default=[2,4,8,16,32])
    ap.add_argument('--models',nargs='+',default=[m[0] for m in MODELS],choices=[m[0] for m in MODELS])
    ap.add_argument('--repeats',type=int,default=3)
    ap.add_argument('--timeout',type=float,default=180)
    ap.add_argument('--budget',type=float,default=1260)
    ap.add_argument('--generate-only',action='store_true')
    args=ap.parse_args();repo=args.repo.resolve();out=args.out_dir.resolve();out.mkdir(parents=True,exist_ok=True)
    for sub in ['sources','logs','queries','markers']:(out/sub).mkdir(exist_ok=True)
    models=[m for m in MODELS if m[0] in args.models]
    meta=dict(repo=str(repo),commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),lean=subprocess.check_output(['lake','env','lean','--version'],cwd=repo,text=True).strip(),models=models,depths=args.depths,repeats=args.repeats,timeout_seconds=args.timeout,budget_seconds=args.budget,resources=dict(maxHeartbeats=0,maxRecDepth=10000,simp_maxSteps=100000),source_hashes={m[0]:hashlib.sha256((repo/m[1]).read_bytes()).hexdigest() for m in models},solver_executed=False,elab_async=False,cpu=next((x.split(':',1)[1].strip() for x in Path('/proc/cpuinfo').read_text().splitlines() if x.startswith('model name')),'unknown'),platform=platform.platform(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),core_sha256=hashlib.sha256((repo/'Veil/Frontend/DSL/Tactic/Core.lean').read_bytes()).hexdigest(),ordering='model-major; depths increasing; original/early order alternates per repetition and depth',timing='Sequential processes and synchronous Lean elaboration; stage wall time; excludes startup/modelgen/instrumentation/solver. SMT output measured only repetition1. Same-process repetitions include warm caches; variants alternate order.')
    (out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
    allrows=[];allstages=[];start=time.monotonic()
    for model in models:
        name=model[0];path=out/'sources'/(name+'.lean')
        path.write_text(source_for(repo,out,model,args.depths,args.repeats))
        for mode in ['current','early']:(out/'markers'/(name+'_'+mode)).unlink(missing_ok=True)
        if args.generate_only:continue
        skip='skipped_budget' if time.monotonic()-start>=args.budget else ''
        if skip:
            output='';status=skip;wall=0
        else:
            print(f'BEGIN {name} elapsed={time.monotonic()-start:.1f}s',flush=True)
            t=time.monotonic()
            log_path=out/'logs'/(name+'.log')
            with log_path.open('w') as log:
                try:
                    p=subprocess.run(['lake','env','lean','-D','Elab.async=false',str(path)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,text=True,timeout=min(args.timeout,max(1,args.budget-(time.monotonic()-start))))
                    status=f'exit{p.returncode}'
                except subprocess.TimeoutExpired:
                    status='timeout'
            output=log_path.read_text()
            wall=time.monotonic()-t
            with log_path.open('a') as log:log.write(f'\nPROCESS status={status} wall_seconds={wall:.6f}\n')
        for depth in args.depths:
          for mode in ['current','early']:
            rows=parse_output(output,name,mode,depth,args.repeats)
            for row,stages in rows:
                if skip:row['status']=skip
                row.update(process_status=status,process_wall_seconds=round(wall,6))
                allrows.append(row);allstages.extend(stages)
            if not skip:print(f'  {name} {mode} {depth} '+','.join(f"r{r['repeat']}:{r['status']}/{r['preprocessing_ms']}" for r,_ in rows),flush=True)
        write_csv(out/'runs.csv',allrows);write_csv(out/'stages.csv',allstages)
        if not skip:print(f'END {name} {status} wall={wall:.1f}s',flush=True)
    meta['elapsed_seconds']=time.monotonic()-start
    (out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
if __name__=='__main__':main()
