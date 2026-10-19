#!/usr/bin/env python3
"""Resume the post-sweep repairs, replay, and supplemental controls sequentially."""
import hashlib, json, os, shutil, signal, subprocess, sys, time
from pathlib import Path
import run as common
import run_batch
from compare_queries import canonical_commands

HERE=Path(__file__).resolve().parent
REPO=Path('/home/george/src/veil-issue-123')
PRIMARY=HERE/'results'
PLUGIN=REPO/'.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so'
MANIFEST=json.loads((HERE/'manifest.json').read_text())
MODELS={x['model']:x for x in MANIFEST}
STATE=HERE/'post-sweep-state.json'
state=json.loads(STATE.read_text()) if STATE.exists() else {}

def save(): common.atomic_json(STATE,state)

def stage(name, command, cwd=HERE, timeout=None):
    if state.get(name,{}).get('complete'):
        return state[name]
    log=HERE/'post-sweep-logs'/f'{name}.log';log.parent.mkdir(exist_ok=True)
    print('BEGIN',name,flush=True)
    start=time.monotonic();timed_out=False
    with log.open('w') as stream:
        child=subprocess.Popen([str(x) for x in command],cwd=cwd,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
        try: code=child.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(child.pid,signal.SIGKILL);code=child.wait();timed_out=True
    result=dict(complete=True,command=[str(x) for x in command],cwd=str(cwd),exit_code=code,
                wall_ms=round((time.monotonic()-start)*1000),timeout=timed_out,log=str(log))
    state[name]=result;save();print('END',name,result,flush=True)
    return result

def run_checked(name, command):
    result=stage(name,command)
    if result['exit_code']:
        raise RuntimeError(f'{name} failed; inspect {result["log"]}')

def snapshot(out):
    dest=out/'runner-snapshot';dest.mkdir(parents=True,exist_ok=True)
    for name in ['run.py','run_batch.py','solve_batch.py','manifest.json','exclusions.json','METHODS.txt','INVENTORY_METHODS.txt']:
        shutil.copy2(HERE/name,dest/name)

def archive_model(name):
    dest=HERE/'superseded-namespace'/name
    if dest.exists(): return
    dest.mkdir(parents=True)
    for directory in ['cells','events','logs','queries','batch-sources','batch-logs','batch-events']:
        for path in (PRIMARY/directory).glob(name+'__*'):
            target=dest/directory/path.name;target.parent.mkdir(exist_ok=True)
            shutil.copy2(path,target)

def main():
    # The audit is already saved; record its exact outcome and affected names.
    baseline=json.loads((HERE/'namespace-audit/baseline.json').read_text())['rows']
    polluted=json.loads((HERE/'namespace-audit/unscoped.json').read_text())['rows']
    differences=[dict(name=a['name'],baseline=a['matches'],unscoped=b['matches'])
                 for a,b in zip(baseline,polluted) if a!=b]
    common.atomic_json(HERE/'namespace-audit/differences.json',differences)

    # Check Room using its original source prefix and the repaired helper scope.
    room=MODELS['TLA_Room'];prefix=''.join((REPO/room['path']).read_text().splitlines(keepends=True)[:room['cut_line']-1])
    probes=HERE/'setup-diagnostics';probes.mkdir(exist_ok=True)
    import re
    imports=list(re.finditer(r'^(?:public\s+)?(?:meta\s+)?import\s+[^\n]+\n',prefix,re.M));split=imports[-1].end()
    for kind,helper in [('plain',''),('scoped','section\n'+run_batch.helper()+'\nend\n')]:
        path=probes/f'Room-{kind}.lean'
        path.write_text(prefix[:split]+'\nset_option Elab.async false\n'+helper+prefix[split:]+'\n#gen_spec\nend '+room['module']+'\n')
        stage('room-'+kind,['lake','env','lean','-D','Elab.async=false','--plugin='+str(PLUGIN),path],REPO,90)
    plain=state['room-plain'];scoped=state['room-scoped']
    if plain['timeout'] or scoped['timeout']:raise RuntimeError('Room setup diagnostic timed out')
    if bool(plain['exit_code']) != bool(scoped['exit_code']):raise RuntimeError('Room plain/scoped setup disagrees')

    checks=HERE/'namespace-equivalence'
    run_checked('namespace-equivalence',[sys.executable,HERE/'run_batch.py','--repo',REPO,'--out',checks,
        '--models','AWS_AWSFixed','Ivy_PaxosFirstOrder','Ivy_Ring','--depths','1'])
    # Manifest names vary; reject a silent selection omission.
    checked=list((checks/'cells').glob('*.json'))
    if len(checked)!=6:raise RuntimeError(f'Expected six namespace-equivalence cells; got {len(checked)}')
    comparisons=[]
    for path in checked:
        new=json.loads(path.read_text())['row'];old=json.loads((PRIMARY/'cells'/path.name).read_text())['row']
        if new['translation_status']!='complete' or old['translation_status']!='complete':
            raise RuntimeError(f'Namespace equivalence requires emitted queries: {path.name}')
        a=Path(old['query_path']).read_text();b=Path(new['query_path']).read_text()
        same=canonical_commands(a)==canonical_commands(b)
        comparisons.append(dict(cell_id=new['cell_id'],identical_bytes=a==b,same_normalized_formula=same,
                                old_sha256=old['query_sha256'],scoped_sha256=new['query_sha256']))
        if not same:raise RuntimeError(f'Namespace query differs: {path.name}')
    common.atomic_json(checks/'comparison.json',comparisons);snapshot(checks)

    repaired=['TLA_BcastByz','TLA_MutexViolation']
    if scoped['exit_code']==0: repaired.append('TLA_Room')
    repairs=HERE/'namespace-repair'
    run_checked('namespace-repair',[sys.executable,HERE/'run_batch.py','--repo',REPO,'--out',repairs,'--models',*repaired])
    snapshot(repairs)
    if not state.get('merged_repairs'):
        for name in repaired:
            archive_model(name)
            for directory in ['cells','events','logs','queries','batch-sources','batch-logs','batch-events']:
                for path in (repairs/directory).glob(name+'__*'):
                    shutil.copy2(path,PRIMARY/directory/path.name)
        # Genuine setup failures retain no attempted query, using the plain prefix's provenance.
        if scoped['exit_code']!=0:
            archive_model('TLA_Room')
            source=PRIMARY/'batch-sources/TLA_Room__default__plain_setup.lean'
            log=PRIMARY/'batch-logs/TLA_Room__default__plain_setup.log'
            shutil.copy2(probes/'Room-plain.lean',source);shutil.copy2(plain['log'],log)
            for path in (PRIMARY/'cells').glob('TLA_Room__*.json'):
                cell=json.loads(path.read_text());row=cell['row']
                row.update(source_path=str(source),translation_log=str(log),batch_id='TLA_Room__default__plain_setup',
                    batch_setup_ms=plain['wall_ms'],failure_message=log.read_text()[-8000:],failure_kind=common.failure_kind(log.read_text()))
                cell.update(source_sha256=common.sha(source),batch_log=str(log),events=[],
                    batch_execution=dict(plain,batch_id=row['batch_id'],source=str(source),setup_ms=plain['wall_ms']),
                    setup_diagnostic='Original plain source prefix and scoped-helper prefix both fail before BMC; queries unattempted.')
                common.atomic_json(path,cell)
        provenance=PRIMARY/'provenance';provenance.mkdir(exist_ok=True)
        shutil.copytree(repairs/'runner-snapshot',provenance/'namespace-repair-runner',dirs_exist_ok=True)
        shutil.copy2(repairs/'metadata.json',provenance/'namespace-repair-metadata.json')
        common.export(PRIMARY);state['merged_repairs']=repaired;save()

    run_checked('primary-solver-replay',[sys.executable,HERE/'solve_batch.py','--repo',REPO,'--out',PRIMARY,'--solver-timeout','10'])
    controls=[('river-seven','Puzzles_RiverCrossing',7,'default'),
              ('aws-recursion','AWS_AWSFixed',8,'recursion_only'),
              ('diehard-recursion','Puzzles_DieHard',32,'recursion_only'),
              ('flood-recursion','Synchronous_FloodSet',16,'recursion_only'),
              ('epaxos-recursion','TLA_EPaxos',1,'recursion_only')]
    for label,model,depth,profile in controls:
        if model not in MODELS:raise RuntimeError('Unknown control model '+model)
        out=HERE/'controls'/label
        run_checked(label+'-translation',[sys.executable,HERE/'run_batch.py','--repo',REPO,'--out',out,'--models',model,'--depths',str(depth),'--profile',profile])
        snapshot(out)
        run_checked(label+'-solver',[sys.executable,HERE/'solve_batch.py','--repo',REPO,'--out',out,'--solver-timeout','10'])
    state['all_timed_work_complete']=True;save();print('ALL_TIMED_WORK_COMPLETE',flush=True)

if __name__=='__main__':main()
