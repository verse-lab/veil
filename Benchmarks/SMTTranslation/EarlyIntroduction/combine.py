#!/usr/bin/env python3
"""Merge main and supplemental samples without overwriting their provenance.

python3 combine.py --main results --supplement supplement --out-dir combined
A batch column distinguishes original interrupted samples from fresh probes.
"""
import argparse,csv,json
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--main',type=Path,required=True)
p.add_argument('--supplement',type=Path,nargs='+',default=[])
p.add_argument('--out-dir',type=Path,required=True)
a=p.parse_args();a.out_dir.mkdir(parents=True,exist_ok=True)
batches=[('main',a.main)]+[(f'supplement{i+1}',path) for i,path in enumerate(a.supplement)]
for name in ['runs.csv','stages.csv']:
    output=[]
    for batch,path in batches:
        with (path/name).open() as f:
            for row in csv.DictReader(f):output.append(dict(batch=batch,**row))
    with (a.out_dir/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=output[0].keys());w.writeheader();w.writerows(output)
meta=json.loads((a.main/'metadata.json').read_text())
meta['batches']=[dict(batch=batch,path=str(path.resolve()),metadata=json.loads((path/'metadata.json').read_text())) for batch,path in batches]
(a.out_dir/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
