#!/usr/bin/env python3
"""Additional syntactic equivalence audit using only classical logical identities.
No solver input is changed. This is a comparator, not an SMT type checker.
"""
import argparse,csv,json,sys
from pathlib import Path
from compare_queries import canonical_commands
sys.setrecursionlimit(20000)

def normalized(x, env=None, depth=0, neg=False):
 env={} if env is None else env
 if isinstance(x,str):
  y=env.get(x,x)
  if neg:
   if y=='true':return 'false'
   if y=='false':return 'true'
   return ('not',y)
  return y
 if not x:return ()
 op=x[0]
 if op=='not' and len(x)==2:return normalized(x[1],env,depth,not neg)
 if op=='=>' and len(x)==3:return normalized(['or',['not',x[1]],x[2]],env,depth,neg)
 if op in ['forall','exists'] and len(x)==3:
  local=dict(env);binders=[]
  for i,(name,sort) in enumerate(x[1]):
   binders.append(normalized(sort,env,depth));local[name]=('$bound',depth+i)
  q=('exists' if op=='forall' else 'forall') if neg else op
  return (q,tuple(binders),normalized(x[2],local,depth+len(binders),neg))
 if op in ['and','or']:
  q=('or' if op=='and' else 'and') if neg else op
  identity,absorber=('true','false') if q=='and' else ('false','true')
  terms=[]
  for a in x[1:]:
   z=normalized(a,env,depth,neg)
   if z==absorber:return absorber
   if z==identity:continue
   if isinstance(z,tuple) and z and z[0]==q:terms.extend(z[1:])
   else:terms.append(z)
  if not terms:return identity
  if len(terms)==1:return terms[0]
  return (q,*terms)
 y=tuple(normalized(a,env,depth) for a in x)
 return ('not',y) if neg else y

def commands(text):
 out=[]
 for encoded in canonical_commands(text):
  x=json.loads(encoded)
  if x and x[0]=='assert':x=('assert',normalized(x[1]))
  out.append(json.dumps(x,separators=(',',':')))
 return sorted(out)

def check_boundaries():
 assert normalized(['not',['forall',[['x','A']],['P','x']]])==normalized(['exists',[['y','A']],['not',['P','y']]])
 assert normalized(['forall',[['x','A']],['P','x','y']])!=normalized(['forall',[['y','A']],['P','y','y']])
 assert normalized(['forall',[['x','A']],['exists',[['y','B']],['P','x','y']]])!=normalized(['exists',[['y','B']],['forall',[['x','A']],['P','x','y']]])
 assert normalized(['=>','p','true'])=='true'
 assert normalized(['=>','true','p'])=='p'
 assert normalized(['and','p','q'])!=normalized('p')
 assert normalized('p')!=normalized(['not','p'])
 assert commands('(declare-const p Bool) (assert p)')!=commands('(declare-const p Bool) (assert (not p))')
 assert commands('(declare-const p Bool) (assert p)')!=commands('(assert p)')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--results',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();check_boundaries()
 rows=list(csv.DictReader((args.results/'runs.csv').open()));idx={(r['model'],r['depth'],r['variant']):r for r in rows};out=[]
 for r in rows:
  if r['variant']!='old':continue
  e=idx[(r['model'],r['depth'],'early')]
  if r['translation_status']!= 'complete' or e['translation_status']!='complete':continue
  a=args.results/'queries'/Path(r['query_path']).name;b=args.results/'queries'/Path(e['query_path']).name
  out.append(dict(model=r['model'],depth=int(r['depth']),same_after_logical_normalization=commands(a.read_text())==commands(b.read_text()),old_sha256=r['query_sha256'],early_sha256=e['query_sha256']))
 args.output.parent.mkdir(parents=True,exist_ok=True);args.output.with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
 with args.output.with_suffix('.csv').open('w') as f:w=csv.DictWriter(f,fieldnames=out[0]);w.writeheader();w.writerows(out)
 print(json.dumps(dict(pairs=len(out),equivalent_normal_forms=sum(r['same_after_logical_normalization'] for r in out),remaining_differences=sum(not r['same_after_logical_normalization'] for r in out),boundary_checks='passed')))
if __name__=='__main__':main()
