#!/usr/bin/env python3
"""Package the completed report with raw provenance, then verify its links/hashes."""
from pathlib import Path
import argparse,hashlib,json,re,shutil,subprocess,urllib.parse,zipfile
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
repo=a.repo.resolve();out=a.out.resolve()
if not (root/'completed.json').exists():raise SystemExit('Primary run not complete')
if not json.loads((root/'validation.json').read_text())['passed']:raise SystemExit('Validation has not passed')
if out.exists():raise SystemExit('Use a new package output path; do not overwrite a prior package')
out.mkdir(parents=True)
def copyfile(source,target):
 target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(source,target)
for directory in ['results','report','query-comparison','step-profile','solver-controls','solver-order-probe','report-tools']:
 shutil.copytree(root/directory,out/directory,ignore=shutil.ignore_patterns('__pycache__','mpl-cache','*.pyc'))
for pattern in ['*.txt','*.json']:
 for p in root.glob(pattern):
  if p.name not in ['CONTINUE_STATE.txt']:copyfile(p,out/p.name)
for name in ['run.py','run_batch.py','solve_batch.py','run_full.py','validate_results.py','compare_local_queries.py','parse_queries.py','summarize_step_profile.py','summarize_results.py','replay_controls.py','replay_extended.py','probe_solver_order.py','run_diagnostics.py','summarize_diagnostics.py','package.py']:
 copyfile(root/name,out/'runner'/name)
for name in ['full-suite.log','full-translation.log','full-solver.log','orchestration.log','diagnostics-orchestration.log','query-audit.log','controls.log','extended-controls.log','order-probe.log','diagnostic-validation.log']:
 copyfile(root/name,out/'logs'/name)
for name in ['Veil/Frontend/DSL/Tactic/Core.lean','VeilTest/Regression/TraceLocalNormalization.lean']:
 copyfile(repo/name,out/'implementation'/name)
for name in ['LICENSE','LICENSE.md','LICENSE.txt']:
 if (repo/name).is_file():copyfile(repo/name,out/name)
manifest=json.loads((root/'manifest.json').read_text())
for model in manifest:copyfile(repo/model['path'],out/'model-sources'/model['path'])
copyfile(repo/'Examples/StellarConsensus/SCPTheory.lean',out/'model-sources/Examples/StellarConsensus/SCPTheory.lean')
patch=subprocess.check_output(['git','diff','HEAD','--','Veil/Frontend/DSL/Tactic/Core.lean'],cwd=repo)
p=subprocess.run(['git','diff','--no-index','--','/dev/null','VeilTest/Regression/TraceLocalNormalization.lean'],cwd=repo,stdout=subprocess.PIPE)
if p.returncode not in (0,1):raise SystemExit('Cannot create regression patch')
(out/'implementation.patch').write_bytes(patch+p.stdout)
(out/'.gitignore').write_text('!*.json\n!**/*.json\n__pycache__/\n*.pyc\n')
# The report uses relative links so it can be moved with its sibling data folders.
links=[]
for match in re.finditer(r'(?:href|src)="([^"]+)"',(out/'report/index.html').read_text()):
 url=match.group(1)
 if url.startswith(('#','http:','https:','data:')):continue
 local=urllib.parse.unquote(url.split('#',1)[0].split('?',1)[0])
 target=(out/'report'/local).resolve()
 if not target.exists():raise SystemExit('Broken report link: '+url)
 if not target.is_relative_to(out):raise SystemExit('Report link leaves package: '+url)
 links.append(url)
files=[p for p in out.rglob('*') if p.is_file()]
manifest_text=''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(out))+'\n' for p in sorted(files))
(out/'SHA256SUMS').write_text(manifest_text)
for line in manifest_text.splitlines():
 digest,name=line.split('  ',1)
 if hashlib.sha256((out/name).read_bytes()).hexdigest()!=digest:raise SystemExit('Hash changed: '+name)
print(json.dumps({'files_hashed':len(files),'relative_report_links_checked':len(links),'bytes':sum(p.stat().st_size for p in out.rglob('*') if p.is_file()),'package':str(out)}))
