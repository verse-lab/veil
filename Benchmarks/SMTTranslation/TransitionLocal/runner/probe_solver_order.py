#!/usr/bin/env python3
"""Diagnostic only: regroup/reorder the same TwoPhaseCommit d8 constraints."""
from pathlib import Path
import argparse,collections,copy,hashlib,json,subprocess,sys
from compare_local_queries import compare,checks
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=root);ap.add_argument('--repo',type=Path,required=True);args=ap.parse_args();root=args.root.resolve()
if not (root/'completed.json').exists():raise SystemExit('Primary sweep must complete first')
base='Ivy_TwoPhaseCommit__d8__'
a=(root/'results/queries'/(base+'early__default.smt2')).read_text();b=(root/'results/queries'/(base+'local__default.smt2')).read_text()
checks();assert compare(a,b)[0], 'Baseline/local logical audit must match before probing'
# Current serializer emits one entire SMT command per line. Refuse other forms.
def parts(s):
 lines=s.splitlines();groups=collections.defaultdict(list)
 for line in lines:
  if not line:continue
  op=line.split()[0][1:].rstrip(')')
  assert op in ['set-logic','declare-sort','declare-const','declare-fun','assert','check-sat'],op
  groups[op].append(line)
 return groups
pa,pb=parts(a),parts(b)
# Exact multiset equality permits using baseline declarations without renaming.
declops=['declare-sort','declare-const','declare-fun']
assert collections.Counter(x for op in declops for x in pa[op])==collections.Counter(x for op in declops for x in pb[op])
assert len(pb['set-logic'])==1 and len(pb['check-sat'])==1
local_decls=[x for x in b.splitlines() if x.startswith('(declare-')]
early_decls=[x for x in a.splitlines() if x.startswith('(declare-')]
def make(decls,merge):
 assertions=pb['assert']
 if merge:
  assert all(x.startswith('(assert ') and x.endswith(')') for x in assertions)
  assertions=['(assert (and '+' '.join(x[len('(assert '):-1] for x in assertions)+'))']
 return '\n'.join(pb['set-logic']+decls+assertions+pb['check-sat'])+'\n'
variants={
 'local_all_decls_first':make(local_decls,False),
 'early_declaration_order':make(early_decls,False),
 'local_single_assertion':make(local_decls,True),
 'early_order_single_assertion':make(early_decls,True)}
out=root/'solver-order-probe';out.mkdir(exist_ok=False)
for d in ['queries','cells']:(out/d).mkdir()
ids=[];audits=[]
for name,query in variants.items():
 matched,mapping,detail=compare(b,query);assert matched,(name,detail)
 p=out/'queries'/(name+'.smt2');p.write_text(query)
 cell=json.loads((root/'results/cells'/(base+'local__default.json')).read_text());r=cell['row']
 key=name+'__d8__local__default';ids.append(key)
 r.update(cell_id=key,model=name,query_path=str(p),query_sha256=hashlib.sha256(query.encode()).hexdigest(),query_bytes=len(query.encode()),status='query_ready',query_total_ms=0)
 for k in ['solver_status','solver_ms','solver_exit','solver_timeout','solver_process_wall_ms','solver_log','completed_total_ms','failure_phase','failure_kind','failure_message']:r[k]=None
 cell.pop('solver_events',None);cell.pop('solver_execution',None)
 (out/'cells'/(key+'.json')).write_text(json.dumps(cell,indent=2)+'\n')
 audits.append({'variant':name,'matches_original_local':matched,'audit_detail':detail,'query_sha256':r['query_sha256']})
(out/'requested-cells.json').write_text(json.dumps(ids)+'\n');(out/'equivalence.json').write_text(json.dumps(audits,indent=2)+'\n')
with (out/'orchestration.log').open('w') as f:subprocess.run([sys.executable,str(Path(__file__).resolve().parent/'solve_batch.py'),'--repo',str(args.repo),'--out',str(out)],stdout=f,stderr=subprocess.STDOUT,check=True)
print((out/'runs.csv').read_text())
