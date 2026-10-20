from pathlib import Path
import subprocess,sys,json
root=Path('/home/george/src/veil-issue-123');out=Path('/tmp/veil-action-cache')
files=['TraceBindingsDependent','TraceBindingsHygiene','TraceBindingWitness','TraceInhabitedFunction','TraceWithNoActions','TraceLabelDependentReconstruction','DeepBmcTranslation']
result=[]
for name in files:
 file=root/'VeilTest/Regression'/f'{name}.lean'
 if not file.exists():
  matches=list((root/'VeilTest').rglob(f'{name}.lean'));assert len(matches)==1;file=matches[0]
 log=out/f'focused-{name}.log'
 with log.open('w') as stream:
  p=subprocess.run(['lake','env','lean','-D','Elab.async=false','-D','veil.experimental.bmcCache=true','--plugin='+str(root/'.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so'),str(file)],cwd=root,stdout=stream,stderr=subprocess.STDOUT)
 result.append({'file':str(file),'exit':p.returncode,'log':str(log)})
 print(name,p.returncode,flush=True)
 if p.returncode:sys.exit(1)
(out/'focused-validation.json').write_text(json.dumps(result,indent=2)+'\n')
