#!/usr/bin/env python3
"""Conservative SAT-equivalence audit; witnesses and bound variables may be renamed.

A reported match is checked again using the explicit bijection, independently
of the graph refinement used to discover it. No solver input is modified.
Unsupported/different forms are inconclusive. This is not a type checker or a
kernel proof; native acceptance and Lean semantic regressions are separate.
"""
import argparse, csv, hashlib, itertools, json, re, signal, sys
from collections import Counter, defaultdict
from pathlib import Path
from parse_queries import canonical_commands
sys.setrecursionlimit(20000)
csv.field_size_limit(sys.maxsize)

def atom(x): return isinstance(x,str)
def combine(op,children):
 identity,absorber=('true','false') if op=='and' else ('false','true')
 out=[]
 for x in children:
  if x==absorber:return absorber
  if x==identity:continue
  out.extend(x[1:] if isinstance(x,tuple) and x and x[0]==op else (x,))
 out=sorted(set(out),key=repr)
 return identity if not out else out[0] if len(out)==1 else (op,*out)

def normalize(x,env=None,depth=0,neg=False):
 env={} if env is None else env
 if atom(x):
  x=env.get(x,x)
  if not neg:return x
  return {'true':'false','false':'true'}.get(x,('not',x)) if atom(x) else ('not',x)
 if not x:return ()
 op=x[0]
 if op=='not' and len(x)==2:return normalize(x[1],env,depth,not neg)
 if op=='=>' and len(x)==3:return normalize(['or',['not',x[1]],x[2]],env,depth,neg)
 if op in ('forall','exists') and len(x)==3:
  inner=dict(env);sorts=[]
  for i,(name,sort) in enumerate(x[1]):
   sorts.append(normalize(sort,env,depth));inner[name]=('$bound',depth+i)
  q=('exists' if op=='forall' else 'forall') if neg else op
  return (q,tuple(sorts),normalize(x[2],inner,depth+len(sorts),neg))
 if op in ('and','or'):
  q=('or' if op=='and' else 'and') if neg else op
  return combine(q,[normalize(a,env,depth,neg) for a in x[1:]])
 if op=='distinct' and len(x)==3:
  return normalize(['=',x[1],x[2]],env,depth,not neg)
 if op=='=' and len(x)==3:
  a,b=normalize(x[1],env,depth),normalize(x[2],env,depth)
  if a==b:return 'false' if neg else 'true'
  if a in ('true','false'):return normalize(x[2],env,depth,neg != (a=='false'))
  if b in ('true','false'):return normalize(x[1],env,depth,neg != (b=='false'))
  result=('=',*sorted((a,b),key=repr))
 else:result=tuple(normalize(a,env,depth) for a in x)
 return ('not',result) if neg else result

def rewrite(x,mapping):
 if atom(x):return mapping.get(x,x)
 if not x:return x
 if x[0]=='$bound':return x
 y=tuple(rewrite(a,mapping) for a in x)
 if y[0] in ('and','or'):return combine(y[0],y[1:])
 if y[0]=='=':return ('=',*sorted(y[1:],key=repr))
 return y

def parse(text):
 decls={};asserts=[];metadata=[]
 sort_names=set()
 for enc in canonical_commands(text):
  x=json.loads(enc);op=x[0]
  if op=='assert':asserts.append(normalize(x[1]))
  elif op=='declare-const':decls[x[1]]=((),normalize(x[2]))
  elif op=='declare-fun':decls[x[1]]=(tuple(normalize(t) for t in x[2]),normalize(x[3]))
  elif op in ('declare-sort','set-logic'):
   metadata.append(normalize(x))
   if op=='declare-sort':sort_names.add(x[1])
  elif op=='check-sat':pass
  else:raise ValueError('unsupported command in equivalence audit: '+op)
 if sort_names.intersection(decls):raise ValueError('sort/value name collision is unsupported by audit')
 if any(n=='$bound' or n.startswith('$audit_witness_') for n in decls):raise ValueError('reserved audit symbol in query')
 formula=combine('and',asserts)
 # SMT sorts are inhabited. Existentials in positive NNF positions outside
 # universal scopes may be represented by independent global constants.
 fresh=0
 def extract(x,level=0,under_forall=False,subst=None,newlevel=0):
  nonlocal fresh
  subst={} if subst is None else subst
  if atom(x):return x
  if not x:return x
  if x[0]=='$bound':return subst.get(x,x)
  if x[0] in ('forall','exists'):
   op,sorts,body=x
   if op=='exists' and not under_forall:
    sub=dict(subst)
    for i,sort in enumerate(sorts):
     name=f'$audit_witness_{fresh}';fresh+=1
     if name in decls:raise ValueError('audit symbol collision')
     decls[name]=((),sort);sub[('$bound',level+i)]=name
    return extract(body,level+len(sorts),False,sub,newlevel)
   sub=dict(subst)
   for i in range(len(sorts)):sub[('$bound',level+i)]=('$bound',newlevel+i)
   return (op,sorts,extract(body,level+len(sorts),True,sub,newlevel+len(sorts)))
  # Only and/or positions in NNF are positive. Existentials inside equality,
  # ite conditions, annotations or arbitrary applications must stay scoped.
  blocked=under_forall or x[0] not in ('and','or')
  y=tuple(extract(t,level,blocked,subst,newlevel) for t in x)
  return combine(y[0],y[1:]) if y and y[0] in ('and','or') else y
 formula=extract(formula)
 # Removing unused free declarations is safe for inhabited SMT sorts.
 used=set()
 def visit(x):
  if isinstance(x,tuple) and x and x[0]=='$bound':return
  if atom(x):
   if x in decls:used.add(x)
  else:
   for y in x:visit(y)
 visit(formula)
 return {n:d for n,d in decls.items() if n in used},formula,tuple(sorted(metadata,key=repr))

class Graph:
 def __init__(self,decls,formula,metadata):
  self.labels=[];self.edges=[];self.incoming=[];self.symbols={};self.cache={}
  def new(label):
   i=len(self.labels);self.labels.append(label);self.edges.append([]);self.incoming.append([]);return i
  def edge(a,b,port):self.edges[a].append((port,b));self.incoming[b].append((port,a))
  for name,signature in decls.items():
   # Anchor named trace states, theory fields and action tags/arguments.
   anchor=name if name.startswith(('st','th.','__veil_','_tr')) else ''
   self.symbols[name]=new(('symbol',repr(signature),anchor))
  def node(x):
   if atom(x) and x in self.symbols:return self.symbols[x]
   if x in self.cache:return self.cache[x]
   if atom(x):i=new(('atom',x))
   elif x and x[0]=='$bound':i=new(('bound',x[1]))
   else:
    op=x[0] if x and atom(x[0]) else '$tuple'
    i=new(('application',op if op not in self.symbols else '$free_function',len(x)))
    for j,y in enumerate(x):edge(i,node(y),-1 if op in ('and','or','=') and j else j)
   self.cache[x]=i;return i
  root=new(('root',));edge(root,node(formula),0);edge(root,node(metadata),1)

def mapping_candidates(a,b,limit=10000):
 graphs=[Graph(*a),Graph(*b)];offset=len(graphs[0].labels)
 labels=graphs[0].labels+graphs[1].labels
 edges=graphs[0].edges+[[(p,n+offset) for p,n in es] for es in graphs[1].edges]
 inc=graphs[0].incoming+[[(p,n+offset) for p,n in es] for es in graphs[1].incoming]
 def intern(signatures):
  ids={};return [ids.setdefault(s,len(ids)) for s in signatures]
 colors=intern(labels)
 for _ in range(100):
  nxt=intern([(colors[i],tuple(sorted((p,colors[n]) for p,n in edges[i])),tuple(sorted((p,colors[n]) for p,n in inc[i]))) for i in range(len(colors))])
  same_partition=len(set(nxt))==len(set(colors));colors=nxt
  if same_partition:break
 groups=[]
 for g,off in zip(graphs,[0,offset]):
  by=defaultdict(list)
  for name,node in g.symbols.items():by[colors[off+node]].append(name)
  groups.append(by)
 if {k:len(v) for k,v in groups[0].items()}!={k:len(v) for k,v in groups[1].items()}:return
 pairs=[(sorted(v),sorted(groups[1][k])) for k,v in sorted(groups[0].items())]
 explored=0
 def rec(i,m):
  nonlocal explored
  if explored>=limit:return
  if i==len(pairs):explored+=1;yield dict(m);return
  aa,bb=pairs[i]
  for perm in itertools.permutations(bb):
   if explored>=limit:break
   m.update(zip(aa,perm));yield from rec(i+1,m)
 yield from rec(0,{})

def compare(left,right):
 a,b=parse(left),parse(right)
 if a[2]!=b[2]:return False,{},'non-assertion metadata differs'
 if len(a[0])!=len(b[0]):return False,{},'different used declaration counts'
 for mapping in mapping_candidates(a,b):
  if any(a[0][n]!=b[0][m] for n,m in mapping.items()):continue
  if rewrite(a[1],mapping)==rewrite(b[1],{}):return True,mapping,'checked explicit bijection and normalized formula'
 return False,{},'no verified bijection found; inconclusive'

def checks():
 def yes(a,b):assert compare(a,b)[0],(a,b,compare(a,b))
 def no(a,b):assert not compare(a,b)[0],(a,b)
 yes('(declare-const p Bool)(declare-const q Bool)(assert (and p q))','(declare-const x Bool)(declare-const y Bool)(assert y)(assert x)')
 no('(declare-const p Bool)(declare-const q Bool)(assert (and p q))','(declare-const x Bool)(assert x)')
 no('(declare-const p Bool)(assert p)(assert (not p))','(declare-const x Bool)(assert x)')
 yes('(declare-sort A 0)(declare-fun P (A) Bool)(assert (exists ((x A)) (P x)))','(declare-sort A 0)(declare-fun P (A) Bool)(declare-const c A)(assert (P c))')
 no('(declare-sort A 0)(declare-fun P (A A) Bool)(assert (forall ((x A)) (exists ((y A)) (P x y))))','(declare-sort A 0)(declare-fun P (A A) Bool)(declare-const c A)(assert (forall ((x A)) (P x c)))')
 no('(declare-const st1.flag Bool)(assert st1.flag)','(declare-const st1.flag Bool)(assert (not st1.flag))')
 yes('(declare-sort A 0)(declare-fun P (A) Bool)(assert (not (forall ((x A)) (not (P x)))))','(declare-sort A 0)(declare-fun P (A) Bool)(declare-const c A)(assert (P c))')

 # Existentials in non-monotone Boolean equality positions cannot be lifted.
 no('(declare-const q Bool)(assert (not q))(assert (= (exists ((x Bool)) x) q))','(declare-const q Bool)(declare-const c Bool)(assert (not q))(assert (= c q))')
 yes('(declare-sort A 0)(declare-fun P (A A) Bool)(assert (exists ((x A)) (forall ((y A)) (P x y))))','(declare-sort A 0)(declare-fun P (A A) Bool)(declare-const c A)(assert (forall ((y A)) (P c y)))')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--results',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();checks()
 rows=list(csv.DictReader((args.results/'runs.csv').open()));idx={(r['model'],r['depth'],r['variant']):r for r in rows};out=[];maps={}
 for r in rows:
  if r['variant']!='early':continue
  other=idx[(r['model'],r['depth'],'local')]
  if r['translation_status']!='complete' or other['translation_status']!='complete':continue
  paths=[args.results/'queries'/Path(x['query_path']).name for x in [r,other]]
  if any(hashlib.sha256(p.read_bytes()).hexdigest()!=x['query_sha256'] for p,x in zip(paths,[r,other])):raise RuntimeError('query hash mismatch')
  def timeout(_signum,_frame):raise TimeoutError('20-second audit search cap; inconclusive')
  signal.signal(signal.SIGALRM,timeout);signal.alarm(20)
  try:matched,mapping,detail=compare(*(p.read_text() for p in paths))
  except (ValueError,RecursionError,TimeoutError) as e:matched,mapping,detail=False,{},str(e)
  finally:signal.alarm(0)
  out.append(dict(model=r['model'],depth=int(r['depth']),same_after_logical_normalization=matched,detail=detail,early_sha256=r['query_sha256'],local_sha256=other['query_sha256'],both_native_accepted=all(x['solver_status'] in ['sat','unsat','timeout','unknown'] for x in [r,other])))
  maps[r['model']+'__'+r['depth']]=mapping
  print(r['model'],r['depth'],matched,detail,flush=True)
 args.output.parent.mkdir(parents=True,exist_ok=True)
 with args.output.with_suffix('.csv').open('w') as f:
  w=csv.DictWriter(f,fieldnames=out[0]);w.writeheader();w.writerows(out)
 args.output.with_suffix('.json').write_text(json.dumps({'rows':out,'renamings':maps},indent=2)+'\n')
 print(json.dumps({'pairs':len(out),'verified_matches':sum(r['same_after_logical_normalization'] for r in out),'boundary_checks':'passed'}))
if __name__=='__main__':main()
