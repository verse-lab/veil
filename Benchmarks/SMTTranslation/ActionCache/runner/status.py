from pathlib import Path
from collections import Counter
import json
h=Path('/tmp/veil-action-cache');r=h/'results'
rows=[json.loads(p.read_text())['row'] for p in (r/'cells').glob('*.json')]
print('cells',len(rows),'processed',sum(x['status']!='not_started' for x in rows))
for v in ['local','cached']:
 rs=[x for x in rows if x['variant']==v and x['status']!='not_started'];print(v,len(rs),dict(Counter(x['status'] for x in rs)))
 print('first failure phases',dict(Counter(x['failure_phase'] for x in rs if x['failure_phase'])))
for name in ['full-translation.log','full-solver.log','orchestration.log']:
 p=h/name
 if p.exists():print(name+'\n'+'\n'.join(p.read_text().splitlines()[-4:]))
