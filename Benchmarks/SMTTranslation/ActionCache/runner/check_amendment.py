from pathlib import Path
from collections import defaultdict
import json,hashlib
import run_batch
h=Path(__file__).resolve().parent;r=h/'results';groups=defaultdict(list)
for p in (r/'cells').glob('*.json'):
 c=json.loads(p.read_text())
 if c['row']['status']!='not_started':groups[c['row']['batch_id']].append(c)
checked=[]
for batch,cells in sorted(groups.items()):
 cells.sort(key=lambda c:c['row']['depth']);old=Path(cells[0]['row']['source_path']);new=h/'amendment-check.lean'
 marker=r/'batch-events'/(batch+'.ready')
 run_batch.source_for(Path('/home/george/src/veil-issue-123'),cells[0]['model'],cells,new,marker,'default')
 if old.read_bytes()!=new.read_bytes():raise RuntimeError('Source differs: '+batch)
 checked.append(batch)
new.unlink(missing_ok=True)
p=h/'setup-amendment.json';data=json.loads(p.read_text());data['byte_identical_completed_batches']=checked;data['verified_completed_cells']=sum(len(x) for x in groups.values());p.write_text(json.dumps(data,indent=2)+'\n')
print('Verified byte-identical sources for',len(checked),'completed batches')
