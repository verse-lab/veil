#!/usr/bin/env python3
"""Regenerate per-model figures from an existing report configuration."""
import argparse,json,multiprocessing
from pathlib import Path
from types import SimpleNamespace
import report
ap=argparse.ArgumentParser();ap.add_argument('--config',type=Path,required=True);ap.add_argument('--workers',type=int,default=3);opt=ap.parse_args()
config=json.loads(opt.config.read_text());path_keys=['manifest','exclusions','results','out_dir']
for k in path_keys:config[k]=Path(config[k]) if config.get(k) else None
args=SimpleNamespace(**config);models,_,indexed,by_cell=report.load(args);plt=report.setup_plots()
def draw(model):
 report.plot_model(plt,args.out_dir/'figures/models',model,indexed,by_cell,args)
 return model['model']
with multiprocessing.get_context('fork').Pool(opt.workers) as pool:
 for name in pool.imap_unordered(draw,models):print(name,flush=True)
print('Completed',len(models),'model figures',flush=True)
