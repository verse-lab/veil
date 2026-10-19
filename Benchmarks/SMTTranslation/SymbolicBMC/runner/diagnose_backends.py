#!/usr/bin/env python3
"""Run isolated functional probes after the timed benchmark, never as timings."""
import argparse, hashlib, json, os, signal, subprocess, time
from pathlib import Path

HERE=Path(__file__).resolve().parent
REPO=Path('/home/george/src/veil-issue-123')
PLUGIN=REPO/'.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so'
GROUPS={
 'nat': [('aws-embedding-candidates',x) for x in ['MinimalOriginal','MinimalFixedNat','MinimalWithDefaultOnly','MinimalDependentOnly']],
 'aws': [('', 'ProductionAWSBuggy')]+[('aws-embedding-candidates',x) for x in ['AWSBuggyFixedNat','AWSBuggyWithDefaultOnly','AWSBuggyDependentOnly']],
 'circular': [('aws-embedding-candidates',x) for x in ['BuggyCircularBufferOriginal','BuggyCircularBufferFixedNat']],
 'universe': [('paxos-universe-candidates',x) for x in ['UniverseDependencyProbe','PaxosEPRProduction','PaxosEPRDiagnostic','ReliableBroadcastProduction','ReliableBroadcastDiagnostic']],
 'transition': [('paxos-universe-candidates',x) for x in ['TransitionFormMinimal','ActionFormMinimal']],
 'parser': [('paxos-universe-candidates',x) for x in ['ChordRingMaintenanceProduction','ChordRingMaintenanceTranslateDecide','SuzukiKasamiProduction','SuzukiKasamiTranslateDecide']],
 'decide': [('paxos-universe-candidates',x) for x in ['PaxosEPRTranslateDecide','ReliableBroadcastTranslateDecide']],
}

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('groups',nargs='+',choices=GROUPS);ap.add_argument('--timeout',type=int,default=90);args=ap.parse_args()
 state=json.loads((HERE/'post-sweep-state.json').read_text())
 if not state.get('all_timed_work_complete'):raise RuntimeError('Timed benchmark still owns CPU')
 out=HERE/'functional-diagnostics';out.mkdir(exist_ok=True)
 for group in args.groups:
  for folder,name in GROUPS[group]:
   source=HERE/folder/(name+'.lean');result_path=out/(name+'.json');log=out/(name+'.log')
   if result_path.exists():print('RETAIN',name,flush=True);continue
   command=['lake','env','lean','-D','Elab.async=false','--plugin='+str(PLUGIN),str(source)]
   print('BEGIN',name,flush=True);start=time.monotonic();timed_out=False
   with log.open('w') as stream:
    child=subprocess.Popen(command,cwd=REPO,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
    try:code=child.wait(timeout=args.timeout)
    except subprocess.TimeoutExpired:
     os.killpg(child.pid,signal.SIGKILL);code=child.wait();timed_out=True
   result=dict(group=group,source=str(source),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),command=command,
      exit_code=code,timeout=timed_out,wall_ms=round((time.monotonic()-start)*1000),log=str(log),purpose='functional diagnostic; not a performance observation')
   result_path.write_text(json.dumps(result,indent=2)+'\n');print('END',name,result,flush=True)

if __name__=='__main__':main()
