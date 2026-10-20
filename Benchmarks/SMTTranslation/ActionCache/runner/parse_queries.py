#!/usr/bin/env python3
"""Compare paired emitted SMT queries without changing solver inputs.

Equality after implication currying and command ordering is positive evidence
of the same asserted formula. A difference is not a semantic counterexample.
This parser is for these generated SMT-LIB scripts, not arbitrary SMT-LIB.
"""
import argparse, csv, hashlib, json, re, sys
from pathlib import Path
sys.setrecursionlimit(20000)
csv.field_size_limit(sys.maxsize)

def canonical_commands(text):
    """Parse SMT commands and normalize (a ∧ b) → c to a → b → c."""
    tokens = re.findall(r'\|[^|]*\||"(?:[^"]|"")*"|[()]|[^\s()]+', text)
    stack, commands = [], []
    for token in tokens:
        if token == '(':
            stack.append([])
        elif token == ')':
            node = stack.pop()
            if stack:
                stack[-1].append(node)
            else:
                commands.append(node)
        else:
            stack[-1].append(token)
    if stack:
        raise ValueError('unbalanced SMT parentheses')
    def normalize(node):
        if not isinstance(node, list):
            return node
        node = [normalize(x) for x in node]
        if (len(node) == 3 and node[0] == '=>' and isinstance(node[1], list)
                and len(node[1]) >= 2 and node[1][0] == 'and'):
            result = node[2]
            for antecedent in reversed(node[1][1:]):
                result = ['=>', antecedent, result]
            return result
        return node
    return sorted(json.dumps(normalize(c), ensure_ascii=False) for c in commands)


def query_path(root, recorded):
    """Allow the artifact directory to move; recorded hashes remain mandatory."""
    if not recorded:
        return root / 'queries' / '__missing_query__'
    original = Path(recorded)
    if original.is_file():
        return original
    return root / 'queries' / original.name


def compare(root):
    rows=list(csv.DictReader((root/'runs.csv').open()))
    pairs={}
    for row in rows:
        pairs.setdefault((row['model'],int(row['depth']),row['profile']),{})[row['variant']]=row
    output=[]
    for (model,depth,profile),variants in sorted(pairs.items()):
        a,b=variants.get('old',{}),variants.get('early',{})
        if not a:a=variants.get('original',{})
        r=dict(model=model,depth=depth,profile=profile,old_status=a.get('status','not_started'),early_status=b.get('status','not_started'),both_queries=False,identical_bytes='',same_commands_ignoring_order='',same_after_implication_currying='',comparison_error='')
        pa,pb=query_path(root,a.get('query_path')),query_path(root,b.get('query_path'))
        if a.get('translation_status') == 'complete' and b.get('translation_status') == 'complete' and pa.is_file() and pb.is_file():
            x,y=pa.read_text(),pb.read_text()
            if hashlib.sha256(pa.read_bytes()).hexdigest()!=a.get('query_sha256') or hashlib.sha256(pb.read_bytes()).hexdigest()!=b.get('query_sha256'):
                r['comparison_error']='Query checksum differs from recorded translation artifact'
                output.append(r)
                continue
            r.update(both_queries=True,identical_bytes=x==y,same_commands_ignoring_order=sorted(x.splitlines())==sorted(y.splitlines()))
            try:r['same_after_implication_currying']=canonical_commands(x)==canonical_commands(y)
            except Exception as e:r['comparison_error']=str(e)
        output.append(r)
    return output

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--results',required=True,type=Path)
    ap.add_argument('--output',required=True,type=Path)
    a=ap.parse_args();rows=compare(a.results)
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.with_suffix('.json').write_text(json.dumps(rows,indent=2)+'\n')
    with a.output.with_suffix('.csv').open('w') as f:
        w=csv.DictWriter(f,fieldnames=rows[0].keys());w.writeheader();w.writerows(rows)
    print(json.dumps(dict(pairs=len(rows),both_queries=sum(r['both_queries'] for r in rows),identical_after_normalization=sum(r['same_after_implication_currying'] is True for r in rows),different_after_normalization=sum(r['same_after_implication_currying'] is False for r in rows),parser_errors=sum(bool(r['comparison_error']) for r in rows))))

if __name__=='__main__':main()
