from pathlib import Path
import hashlib,json,shutil,subprocess,difflib,zipfile,html.parser,re
H=Path(__file__).resolve().parent;R=Path('/home/george/src/veil-issue-123');P=Path('/tmp/veil-action-cache-package')
if not (H/'completed.json').exists():raise SystemExit('Primary run not complete')
if P.exists():shutil.rmtree(P)
P.mkdir();shutil.copytree(H/'report',P/'report');shutil.copytree(H/'results',P/'raw')
for name in ['README.txt','METHODS.txt','IMPLEMENTATION.txt','EXECUTIVE_SUMMARY.txt','RESULTS_ANALYSIS.txt','VALIDATION.txt','SOLVER_BEHAVIOR.txt','NEXT_FIXES.txt','frozen-build.json','completed.json','focused-validation.json','validation.json','environment.json','setup-amendment.json','manifest.json','exclusions.json']:
 if (H/name).exists():shutil.copy2(H/name,P/name)
for folder in ['query-comparison','controls','baseline']:
 if (H/folder).exists():shutil.copytree(H/folder,P/folder)
(P/'runner').mkdir();(P/'logs').mkdir()
for p in H.glob('*.py'):shutil.copy2(p,P/'runner'/p.name)
for p in H.glob('*.log'):
 if p.name.startswith(('build','benchmark-smoke','smoke','barrier-smoke')):continue
 shutil.copy2(p,P/'logs'/p.name)
(P/'checks').mkdir()
for name in ['CacheNamesProbe.lean']:
 if (H/name).exists():shutil.copy2(H/name,P/'checks'/name)
paths=['Veil/Base.lean','Veil/Frontend/DSL/Infra/Simp.lean','Veil/Frontend/DSL/Tactic/Core.lean','Veil/Frontend/DSL/Module/Elaborators/Verification.lean','Veil/Core/Tools/ModelChecker/Symbolic/TraceLang.lean','Veil/Frontend/DSL/Module/Util/TraceTemplates.lean','Veil/Frontend/DSL/Module/Util/BmcCache.lean','VeilTest/Regression/TraceCachedNormalization.lean']
patch=[]
for rel in paths:
 p=R/rel;dest=P/'source'/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dest)
 if rel.endswith('Tactic/Core.lean'):before=(H/'baseline/Core.lean').read_text()
 else:
  c=subprocess.run(['git','show','HEAD:'+rel],cwd=R,text=True,capture_output=True);before=c.stdout if c.returncode==0 else ''
 patch.append(''.join(difflib.unified_diff(before.splitlines(keepends=True),p.read_text().splitlines(keepends=True),fromfile='a/'+rel if before else '/dev/null',tofile='b/'+rel)))
(P/'implementation.patch').write_text(''.join(patch))
(P/'index.html').write_text('<!doctype html><meta charset="utf-8"><meta http-equiv="refresh" content="0;url=report/index.html"><a href="report/index.html">Open the benchmark report</a>')
(P/'OPEN_REPORT.txt').write_text('Open report/index.html. The package contains all 49 model figures (PNG and SVG), the complete raw results and SMT queries, runner scripts, source snapshot and incremental patch. METHODS.txt specifies limits and timing interpretation. Paths inside raw JSON/events preserve the original /tmp run locations; portable report links use package-relative paths. The source patch is incremental to the preceding per-transition change on 543817e6; baseline/Core.lean records that input.\n')
# Reject broken artifact-relative HTML links.
class Links(html.parser.HTMLParser):
 def __init__(self):super().__init__();self.values=[]
 def handle_starttag(self,tag,attrs):
  for k,v in attrs:
   if k in ['src','href'] and v:self.values.append(v)
links=0
for p in P.rglob('*.html'):
 l=Links();l.feed(p.read_text())
 for ref in l.values:
  if re.match(r'^(https?:|data:|#)',ref):continue
  dest=(p.parent/ref.split('#')[0]).resolve()
  if not dest.exists():raise RuntimeError(f'broken link {p}: {ref}')
  links+=1
hashes={str(p.relative_to(P)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(P.rglob('*')) if p.is_file()}
(P/'SHA256SUMS.json').write_text(json.dumps(hashes,indent=2)+'\n')
print(json.dumps({'package':str(P),'files':len(hashes),'checked_links':links,'bytes':sum(p.stat().st_size for p in P.rglob('*') if p.is_file())}))
