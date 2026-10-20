"""Publish the finished, validated package locally; never commits or pushes."""
from pathlib import Path
import json,hashlib,shutil,zipfile,subprocess
H=Path('/tmp/veil-action-cache')
P=Path('/tmp/veil-action-cache-package')
W=Path('/home/george/src/veil-issue-123')
D=Path('/home/george/.codex/visualizations/2026/10/19/01a151bb-5c44-7e41-ad15-7cef6918cae3')
assert json.loads((H/'validation.json').read_text())['frozen_source_and_oleans_unchanged']
manifest=json.loads((P/'SHA256SUMS.json').read_text())
for rel,sha in manifest.items():assert hashlib.sha256((P/rel).read_bytes()).hexdigest()==sha,rel
subprocess.run(['git','apply','--check','--reverse',str(P/'implementation.patch')],cwd=W,check=True)
for dest in [W/'Benchmarks/SMTTranslation/ActionCache',D/'veil-action-cache']:
 if dest.exists():raise SystemExit('Refuse to replace existing artifact directory: '+str(dest))
 shutil.copytree(P,dest)
archive=D/'veil-action-cache.zip'
if archive.exists():raise SystemExit('Refuse to replace existing archive')
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for p in sorted((D/'veil-action-cache').rglob('*')):
  if p.is_file():z.write(p,p.relative_to(D))
readme=W/'Benchmarks/SMTTranslation/README.md'
s=readme.read_text()
old='The latest comparison is [early introduction versus per-transition normalization](TransitionLocal/report/index.html): 49 model-bearing files, six exact depths, all-model graphs, emitted SMT queries, native solver replay, semantic audits and separate regression diagnostics. [The code diff](TransitionLocal/implementation.patch) is against commit `543817e6`.'
new='The latest comparison is [per-transition normalization versus exact transition caching](ActionCache/report/index.html): 49 model-bearing files, six exact depths, all-model graphs, cold setup costs, emitted SMT queries, native solver replay, semantic audits and separate solver controls. [The incremental code diff](ActionCache/implementation.patch) applies on top of the preceding per-transition implementation. Enable `veil.experimental.bmcCache` before `#gen_spec` to opt in.\n\nThe preceding [early introduction versus per-transition normalization comparison](TransitionLocal/report/index.html) retains its own raw measurements and diagnostics. [Its code diff](TransitionLocal/implementation.patch) is against commit `543817e6`. The studies use separate fresh measurements; do not pool their timings.'
assert old in s
s=s.replace(old,new).replace('`VeilTest/Regression/TraceLocalNormalization.lean` and','`VeilTest/Regression/TraceLocalNormalization.lean`, `VeilTest/Regression/TraceCachedNormalization.lean` and')
readme.write_text(s)
subprocess.run(['git','diff','--check'],cwd=W,check=True)
sha=hashlib.sha256(archive.read_bytes()).hexdigest()
(H/'published.json').write_text(json.dumps({'worktree_report':str(W/'Benchmarks/SMTTranslation/ActionCache/report/index.html'),'durable_report':str(D/'veil-action-cache/report/index.html'),'archive':str(archive),'archive_sha256':sha,'files':len(manifest)},indent=2)+'\n')
print((H/'published.json').read_text())
