#!/usr/bin/env python3
from pathlib import Path
import datetime,json,subprocess,sys
root=Path(__file__).resolve().parent;repo='/home/george/src/veil-issue-123'
commands=[
 ('step-profile/full.log',[str(root/'step-profile/runner/run_batch.py'),'--repo',repo,'--manifest',str(root/'manifest.json'),'--out',str(root/'step-profile/results'),'--models','Ivy_Blockchain','Tutorial_FloodSet','Ivy_Ring']),
 ('controls.log',[str(root/'replay_controls.py'),'--repo',repo]),
 ('extended-controls.log',[str(root/'replay_extended.py'),'--repo',repo]),
 ('order-probe.log',[str(root/'probe_solver_order.py'),'--repo',repo]),
]
for name,command in commands:
 print('BEGIN',name,flush=True)
 with (root/name).open('w') as log:subprocess.run([sys.executable]+command,stdout=log,stderr=subprocess.STDOUT,check=True)
 print('END',name,flush=True)
(root/'diagnostics-completed.json').write_text(json.dumps({'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},indent=2)+'\n')
