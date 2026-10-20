from pathlib import Path
import datetime, hashlib, json, shutil, subprocess, sys
here=Path(__file__).resolve().parent
repo=Path('/home/george/src/veil-issue-123')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
suite=(here/'full-suite.log').read_text()
if 'Build completed successfully' not in suite or '\nerror:' in suite or '\n✖' in suite:
 raise SystemExit('Full suite has not passed; refuse to benchmark this build.')
paths=['Veil/Base.lean','Veil/Frontend/DSL/Infra/Simp.lean','Veil/Frontend/DSL/Tactic/Core.lean','Veil/Frontend/DSL/Module/Elaborators/Verification.lean','Veil/Core/Tools/ModelChecker/Symbolic/TraceLang.lean','Veil/Frontend/DSL/Module/Util/TraceTemplates.lean','Veil/Frontend/DSL/Module/Util/BmcCache.lean','VeilTest/Regression/TraceCachedNormalization.lean']
files=[repo/p for p in paths]+[repo/'.lake/build/lib/lean'/Path(p).with_suffix('.olean') for p in paths if p.startswith('Veil/')]
freeze={str(p):sha(p) for p in files}
freeze_path=here/'frozen-build.json'
if freeze_path.exists():
 previous=json.loads(freeze_path.read_text())
 if previous['files']!=freeze:raise SystemExit('Frozen build changed before resuming')
 previous.setdefault('resumed_utc',[]).append(datetime.datetime.now(datetime.timezone.utc).isoformat())
 freeze_path.write_text(json.dumps(previous,indent=2)+'\n')
else:
 freeze_path.write_text(json.dumps({'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),'files':freeze,'suite_sha256':sha(here/'full-suite.log')},indent=2)+'\n')

out=here/'results';snap=out/'runner-snapshot';snap.mkdir(parents=True,exist_ok=True)
for name in ['run.py','run_batch.py','solve_batch.py','manifest.json','run_full.py']:
 shutil.copy2(here/name,snap/name)
for script,extra,logname in [('run_batch.py',['--manifest',str(here/'manifest.json')],'full-translation.log'),('solve_batch.py',[],'full-solver.log')]:
 for p,h in freeze.items():
  if sha(Path(p))!=h:raise SystemExit('Frozen build changed: '+p)
 with (here/logname).open('a') as log:
  result=subprocess.run([sys.executable,str(here/script),'--repo',str(repo),'--out',str(out)]+extra,stdout=log,stderr=subprocess.STDOUT)
 if result.returncode:raise SystemExit(f'{script} failed; see {logname}')
(here/'completed.json').write_text(json.dumps({'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'frozen_build_verified':all(sha(Path(p))==h for p,h in freeze.items())},indent=2)+'\n')
