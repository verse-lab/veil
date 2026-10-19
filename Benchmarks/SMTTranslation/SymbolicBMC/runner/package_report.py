#!/usr/bin/env python3
"""Assemble a portable, checksummed report; never change raw measurements."""
import argparse, hashlib, json, shutil, subprocess, sys, zipfile
from pathlib import Path
HERE=Path(__file__).resolve().parent
REPO=Path('/home/george/src/veil-issue-123')
DOCS=['README.txt','EXECUTIVE_SUMMARY.txt','NEXT_FIXES.txt','DATASET_PROVENANCE.txt',
 'CONTROL_FINDINGS.txt','DIAGNOSTICS_README.txt','INVENTORY_METHODS.txt','METHODS.txt','PIPELINE_PARITY_AUDIT.txt','BACKEND_FINDINGS.txt',
 'AWS_EMBEDDING_REPAIR_PLAN.txt','PAXOS_UNIVERSE_FINDINGS.txt','SMT_PARSER_FINDINGS.txt','QUERY_EQUIVALENCE.txt','TRANSITION_FORM_FINDINGS.txt','HOISTING_FOLLOWUPS.txt',
 'LOCAL_NORMALIZATION_DESIGN.txt','ARCHITECTURE_NEXT_STEPS.txt','manifest.json',
 'exclusions.json','environment.json','validation.json']
RUNNERS=['run.py','run_batch.py','solve_batch.py','compare_queries.py','validate_results.py',
 'compare_logical_forms.py','make_manifest.py','diagnose_backends.py','finish_benchmark.py','package_report.py']
def copytree(source,dest):
 shutil.copytree(source,dest,dirs_exist_ok=True,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);args=ap.parse_args();out=args.out
 assert json.loads((HERE/'post-sweep-state.json').read_text()).get('all_timed_work_complete')
 assert json.loads((HERE/'validation.json').read_text())['passed']
 assert not out.exists(), 'Use a fresh package path; do not mix versions'
 out.mkdir(parents=True)
 for name in DOCS:shutil.copy2(HERE/name,out/name)
 for name in ['results','report','report-tools','controls'] :copytree(HERE/name,out/name)
 copytree(HERE/'query-comparison',out/'query-comparison')
 runner=out/'runner';runner.mkdir()
 for name in RUNNERS:shutil.copy2(HERE/name,runner/name)
 shutil.copy2(HERE/'RUNNER_README.txt',runner/'README.txt')
 prov=out/'provenance';prov.mkdir()
 for name in ['namespace-audit','namespace-equivalence','setup-diagnostics','post-sweep-logs']:
  copytree(HERE/name,prov/name)
 for name in ['post-sweep-state.json','post-sweep.log','full-translation.log']:
  shutil.copy2(HERE/name,prov/name)
 diag=out/'diagnostics';diag.mkdir()
 for name in ['aws-embedding-candidates','paxos-universe-candidates','functional-diagnostics']:
  copytree(HERE/name,diag/name)
 for name in ['ProductionAWSBuggy.lean','ProductionAWSBuggy.log','ProductionAWSBuggy.result.json']:
  shutil.copy2(HERE/name,diag/name)
 shutil.copy2(HERE/'DIAGNOSTICS_README.txt',diag/'README.txt')
 synthetic=out/'synthetic';synthetic.mkdir()
 for name in ['HoistingEquivalences.lean','QuantifierHoisting.lean','QuantifierHoistingResults.txt']:
  shutil.copy2(REPO/'Benchmarks/SMTTranslation'/name,synthetic/name)
 (synthetic/'README.txt').write_text('Separate exploratory hoister-only experiment, under raised limits. Not part of the 49-file primary sweep. Timings had concurrent machine activity; simp steps/proof sizes are the relevant evidence. Local figures exclude context splitting, transport and full backend execution. See HOISTING_FOLLOWUPS.txt for interpretation.\n')
 tests=out/'tests';tests.mkdir()
 shutil.copy2('/tmp/veil-early-intro-tests/final-suite-fixed.log',tests/'final-suite-fixed.log')
 paths=['VeilTest/Regression/TraceEarlyIntroduction.lean','VeilTest/Performance/DeepBmcTranslation.lean']
 for name in paths:shutil.copy2(REPO/name,tests/Path(name).name)
 patch=subprocess.check_output(['git','diff','--','Veil/Frontend/DSL/Tactic/Core.lean'],cwd=REPO)
 for name in paths:
  r=subprocess.run(['git','diff','--no-index','--','/dev/null',name],cwd=REPO,stdout=subprocess.PIPE)
  assert r.returncode==1;patch+=r.stdout
 (out/'implementation.patch').write_bytes(patch)
 (out/'.gitignore').write_text('!*.json\n!**/*.json\n')
 subprocess.run([sys.executable,str(runner/'validate_results.py'),'--results',str(out/'results'),
   '--manifest',str(out/'manifest.json'),'--output',str(out/'portable-validation.json'),'--portable-only'],check=True)
 # Verify every relative image/download link in the HTML; external links are untouched.
 from html.parser import HTMLParser
 class Links(HTMLParser):
  def __init__(self):super().__init__();self.links=[]
  def handle_starttag(self,tag,attrs):
   for key,value in attrs:
    if key in ['href','src'] and value and not value.startswith(('#','https:','http:','data:','mailto:')):
     self.links.append(value)
 parser=Links();parser.feed((out/'report/index.html').read_text())
 broken=[link for link in parser.links if not (out/'report'/link.split('#')[0]).exists()]
 assert not broken,broken
 (out/'link-validation.json').write_text(json.dumps(dict(passed=True,relative_links_checked=len(parser.links)),indent=2)+'\n')
 manifest=out/'SHA256SUMS';manifest.write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(out))+'\n' for p in sorted(out.rglob('*')) if p.is_file() and p!=manifest))
 print(json.dumps(dict(package=str(out),files=sum(p.is_file() for p in out.rglob('*')),bytes=sum(p.stat().st_size for p in out.rglob('*') if p.is_file()))))
if __name__=='__main__':main()
