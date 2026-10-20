from pathlib import Path
from collections import Counter
import csv,json,hashlib
H=Path(__file__).resolve().parent;R=H/'results'
freeze=json.loads((H/'frozen-build.json').read_text())
assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest()==v for p,v in freeze['files'].items())
assert 'Build completed successfully' in (H/'full-suite.log').read_text()
assert all(x['exit']==0 for x in json.loads((H/'focused-validation.json').read_text()))
manifest=json.loads((H/'manifest.json').read_text());cells=[json.loads(p.read_text()) for p in (R/'cells').glob('*.json')]
assert len(cells)==len(manifest)*6*2==588
idx={}
for c in cells:
 r=c['row'];idx[r['model'],r['depth'],r['variant']]=r
 assert r['status'] not in ['query_ready','not_started']
 assert r['variant'] in ['local','cached']
 source=Path(r['source_path']);assert hashlib.sha256(source.read_bytes()).hexdigest()==c['source_sha256']
 assert f"set_option veil.experimental.bmcCache {'true' if r['variant']=='cached' else 'false'}" in source.read_text()
 if r['translation_status']=='complete':
  p=Path(r['query_path']);assert p.exists() and hashlib.sha256(p.read_bytes()).hexdigest()==r['query_sha256']
  assert sum(e['event']=='pipeline' and e['status']=='complete' for e in c['events'])==1
  assert any(e['event']=='query_elaboration' and e['status']=='begin' for e in c['events'])
  assert 'SYMBOLIC_BMC_EXTRACTION_COMPLETE' in Path(r['translation_log']).read_text()
  assert r['solver_status'] in ['sat','unsat','timeout','unknown','error','process_timeout']
 def verdict(r):return 'unsat' if r['status']=='unsat_preprocessing' else r['solver_status'] if r['solver_status'] in ['sat','unsat'] else None
pairs=0
for m in manifest:
 for d in [1,2,4,8,16,32]:
  a,b=(idx[m['model'],d,v] for v in ['local','cached'])
  if verdict(a) and verdict(b):assert verdict(a)==verdict(b);pairs+=1
q=json.loads((H/'query-comparison/logical-query-comparison.json').read_text())
summary={'cells':len(cells),'sources_and_queries_hash_checked':True,'frozen_source_and_oleans_unchanged':True,'paired_definite_answers_agree':pairs,'audited_pairs':len(q['rows']),'verified_query_matches':sum(x['same_after_logical_normalization'] for x in q['rows']),'native_accepted_matched_pairs':sum(x['same_after_logical_normalization'] and x['both_native_accepted'] for x in q['rows']),'unresolved_audit_pairs':[x for x in q['rows'] if not x['same_after_logical_normalization']]}
(H/'validation.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
