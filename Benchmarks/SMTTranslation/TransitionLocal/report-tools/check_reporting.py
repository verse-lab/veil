#!/usr/bin/env python3
"""Check the reporting boundary: failed durations are not completion times."""
import csv,json,tempfile
from pathlib import Path
from types import SimpleNamespace
from report import classify,definite_verdict,query_seconds,preprocessing_seconds,completed_solver_seconds,completed_seconds,load,export_tables,sampled_depth_summary,query_artifact_link

CASES=[
    ({'status':'sat','solver_status':'sat'},'sat','SAT'),
    ({'status':'unsat','solver_status':'unsat'},'unsat','UNSAT'),
    ({'status':'unsat_preprocessing','translation_status':'discharged','solver_status':'not_needed'},'discharged','PRE'),
    ({'status':'query_ready','translation_status':'complete','solver_status':'not_reached'},'query_ready','READY'),
    ({'status':'translation_failed','failure_kind':'simp_steps','failure_phase':'nextSimp'},'simp_steps','N:S'),
    ({'status':'translation_failed','failure_kind':'recursion','failure_phase':'embedding'},'recursion','E:R'),
    ({'status':'translation_failed','failure_kind':'heartbeats','failure_phase':'hoist'},'heartbeat','H:B'),
    ({'status':'translation_failed','failure_kind':'unsupported_translation','failure_phase':'embedding'},'embedding','E:!'),
    ({'status':'translation_failed','failure_kind':'lean_error','failure_phase':'translate'},'translation','T:!'),
    ({'status':'setup_failed','failure_kind':'lean_error','failure_phase':'model_setup'},'setup','G:!'),
    ({'status':'query_elaboration_failed','failure_kind':'lean_error','failure_phase':'query_elaboration'},'query_elaboration','V:!'),
    ({'status':'solver_timeout','solver_status':'timeout','failure_phase':'solver'},'solver_timeout','Q:T'),
    ({'status':'solver_unknown','solver_status':'unknown','failure_phase':'solver'},'solver_unknown','Q:?'),
    ({'status':'solver_error','solver_status':'error','failure_phase':'solver'},'solver_error','Q:!'),
    ({'status':'translation_timeout','failure_kind':'wall_timeout','failure_phase':'hoist'},'process_timeout','H:P'),
    ({'status':'solver_process_timeout','solver_status':'process_timeout','failure_kind':'wall_timeout','failure_phase':'solver'},'process_timeout','Q:P'),
    ({'status':'blocked_model_setup','translation_status':'not_started','failure_phase':'model_setup'},'blocked_setup','G:—'),
    ({'status':'query_elaboration_timeout','failure_kind':'wall_timeout','failure_phase':'query_elaboration'},'process_timeout','V:P'),
    ({'status':'not_started','solver_status':'not_reached'},'not_run','—'),
    ({'status':'translation_failed','failure_kind':'type_mismatch','failure_phase':'embedding','failure_message':'a goal containing a simp_step identifier and maxRecDepth value'},'embedding','E:!'),
    (None,'not_run','—')]
for row,family,code in CASES:
    result=classify(row)
    assert (result.family,result.code)==(family,code),(row,result)
for status in ['failed','timeout','discharged','not_started','']:
    assert query_seconds({'translation_status':status,'query_total_ms':1234}) is None
assert query_seconds({'translation_status':'complete','query_total_ms':1234,'solver_status':'timeout'})==1.234
assert completed_seconds({'status':'solver_timeout','solver_status':'timeout','completed_total_ms':9999}) is None
assert completed_solver_seconds({'status':'solver_timeout','solver_status':'timeout','solver_ms':9999}) is None
assert completed_solver_seconds({'status':'sat','solver_status':'sat','solver_ms':1234})==1.234
assert completed_seconds({'status':'unsat_preprocessing','completed_total_ms':9999}) is None
assert completed_seconds({'status':'sat','completed_total_ms':9999})==9.999
assert preprocessing_seconds({'preprocessing_ms':1200,'translation_status':'failed'})==1.2
assert preprocessing_seconds({'translation_status':'failed'}) is None
assert definite_verdict({'status':'unsat_preprocessing','translation_status':'discharged'})=='unsat'
with tempfile.TemporaryDirectory(prefix='report-check-',dir='/tmp') as tmp:
    out=Path(tmp);model={'model':'Test','path':'Examples/Test.lean','query':'assert False'}
    (out/'results'/'queries').mkdir(parents=True)
    (out/'report').mkdir()
    (out/'results'/'queries'/'sample.smt2').write_text('(check-sat)')
    link=query_artifact_link({'translation_status':'complete','query_sha256':'test-sha','query_path':'/missing/original/queries/sample.smt2'},SimpleNamespace(results=out/'results',out_dir=out/'report'))
    assert '../results/queries/sample.smt2' in link
    assert query_artifact_link({'translation_status':'failed','query_path':'/missing'},None)=='—'
    stats=export_tables(out,[model],{},[1,2])
    contradictory={('Test',1,'early'):{'status':'sat','solver_status':'sat','model':'Test','cell_id':'one'},('Test',1,'local'):{'status':'unsat_preprocessing','translation_status':'discharged','model':'Test','cell_id':'two'}}
    sampled={('Test',1,'early'):{'status':'sat','translation_status':'complete','query_sha256':'a'},('Test',2,'early'):{'status':'translation_failed'},('Test',4,'early'):{'status':'solver_timeout','translation_status':'complete','query_sha256':'b'},('Test',4,'local'):{'status':'unsat_preprocessing'}}
    depths=sampled_depth_summary([model],sampled,[1,2,4])[0]
    assert depths['early_serialized_depths']=='1 4' and depths['early_highest_sampled_serialized_depth']==4
    assert depths['early_highest_sampled_definite_solver_depth']==1
    assert depths['local_highest_sampled_serialized_depth']==''
    assert depths['local_highest_sampled_preprocessing_discharge_depth']==4
    audit=export_tables(out,[model],contradictory,[1])
    assert len(audit['disagreements'])==1
    assert not audit['summary']['definite_solver_disagreements']
    assert len(stats['outcomes'])==4 and all(not x['recorded'] for x in stats['outcomes'])
    assert all((out/p).exists() for p in ['queries.csv','matched-timings.csv','failures.csv','definite-disagreements.csv'])
    r={'model':'Test','depth':'1','variant':'early','profile':'default','cell_id':'one'}
    with (out/'runs.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(r));w.writeheader();w.writerows([r,r])
    (out/'manifest.json').write_text(json.dumps([model]))
    try:load(SimpleNamespace(manifest=out/'manifest.json',exclusions=None,results=out,profile='default'))
    except ValueError as error:assert 'Duplicate' in str(error)
    else:raise AssertionError('Duplicate cells were silently selected')
print(f'Reporting checks passed:{len(CASES)} outcome cases, incomplete-time filtering, complete inventory, nonmonotone sampled depths, portable query links, and duplicate rejection.')
