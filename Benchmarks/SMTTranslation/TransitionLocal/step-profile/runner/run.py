#!/usr/bin/env python3
"""Isolated exact-N symbolic BMC comparisons; extraction is not a Lean proof.

Each cell runs the explicit original or conservative early-introduction pipeline,
writes the exact SMT-LIB query, then deliberately aborts its measurement theorem.
There is no `sorry` in the generated scaffold. A separate process solves that
query with Veil's trusted solver configuration. No proof reconstruction is claimed.
"""
import argparse
import csv
import hashlib
import json
import os
import platform
import re
import signal
import subprocess
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
FIELDS = "cell_id model path module depth variant profile status translation_status solver_status failure_phase failure_kind failure_message setup_ms query_elaboration_ms batch_id batch_setup_ms preprocessing_ms smt_preprocessing_ms translation_ms serialization_ms query_total_ms solver_ms completed_total_ms process_wall_ms solver_process_wall_ms query_bytes query_commands query_sha256 query_path source_path event_path translation_log solver_log translation_exit solver_exit translation_timeout solver_timeout proof_status".split()
STAGE_FIELDS = "cell_id model depth variant profile phase status elapsed_ms error heartbeats".split()
VEIL_PHASES = {"early_intros", "nextSimp", "hoist", "intros", "destruct", "dsimp1", "smtSimp", "dsimp2", "split_trace", "prepare_hints", "check_hints"}
SMT_PHASES = {"cleanup", "pushHints", "smt-intros", "negateGoal", "normalize", "embedding"}

HELPER = r'''
open Lean Elab Tactic Meta Veil

meta def symbolicBenchEvent (event phase status : String) (elapsed : Nat := 0)
    (extra : List (String × Json) := []) : IO Unit := do
  let j := Json.mkObj ([
    ("event", toJson event), ("phase", toJson phase), ("status", toJson status),
    ("elapsed_ms", toJson elapsed), ("mono_ms", toJson (← IO.monoMsNow))] ++ extra)
  IO.FS.withFile __EVENT_PATH__ .append fun h => h.putStrLn j.compress

meta partial def symbolicBenchIntroData (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let .forallE _ domain _ _ := target.consumeMData | return goal
  if ← isProp domain then return goal
  let (_, next) ← withOptions (fun opts => opts.setBool `tactic.hygienic false) goal.intro1
  symbolicBenchIntroData next

elab "symbolic_bench_intro_data" : tactic => do
  liftMetaTactic1 fun goal => return some (← symbolicBenchIntroData goal)


meta partial def symbolicBenchStepCounts (message : MessageData) : IO (Nat × Nat) := do
  match message with
  | .trace data msg children =>
    let own ← if data.cls == `Meta.Tactic.simp.numSteps then do
      let some steps := (← msg.toString).trimAscii.toString.toNat?
        | throw <| IO.userError "invalid simp numSteps trace"
      pure (steps, 1)
    else pure (0, 0)
    children.foldlM (fun (total, calls) child => do
      let (n, k) ← symbolicBenchStepCounts child
      return (total+n, calls+k)) own
  | .withContext _ msg | .withNamingContext _ msg | .nest _ msg
    | .group msg | .tagged _ msg | .ofWidget _ msg | .ofOriginatingSyntax _ msg =>
    symbolicBenchStepCounts msg
  | .compose a b =>
    let (n, k) ← symbolicBenchStepCounts a
    let (m, j) ← symbolicBenchStepCounts b
    return (n+m, k+j)
  | _ => return (0, 0)

meta def symbolicBenchRecordSteps (phase : String) : CoreM Unit := do
  let (steps, calls) ← (← getTraceState).traces.toArray.foldlM (fun (n,k) entry => do
    let (m,j) ← symbolicBenchStepCounts entry.msg
    return (n+m,k+j)) (0,0)
  symbolicBenchEvent "simp_work" phase "complete" 0
    [("steps", toJson steps), ("calls", toJson calls)]

elab "symbolic_bench_phase " label:str t:tactic : tactic => do
  if (← getGoals).isEmpty then
    symbolicBenchEvent "stage" label.getString "skipped_goal_closed"
  else
    symbolicBenchEvent "stage" label.getString "begin"
    let start ← IO.monoMsNow
    let hbStart ← IO.getNumHeartbeats
    try
      let savedTrace ← getTraceState
      setTraceState {}
      try
        withOptions (fun opts => opts.setBool `trace.Meta.Tactic.simp.numSteps true) do
          withoutRecover <| evalTactic t
        symbolicBenchRecordSteps label.getString
      finally
        setTraceState savedTrace
      symbolicBenchEvent "stage" label.getString "complete" ((← IO.monoMsNow) - start)
        [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart))]
    catch ex =>
      symbolicBenchEvent "stage" label.getString "failed" ((← IO.monoMsNow) - start)
        [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart)), ("error", toJson (← ex.toMessageData.toString))]
      throw ex

meta def symbolicBenchMetaPhase {α : Type} (label : String) (computation : MetaM α) : MetaM α := do
  symbolicBenchEvent "stage" label "begin"
  let start ← IO.monoMsNow
  let hbStart ← IO.getNumHeartbeats
  try
    let value ← computation
    symbolicBenchEvent "stage" label "complete" ((← IO.monoMsNow) - start)
      [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart))]
    return value
  catch ex =>
    symbolicBenchEvent "stage" label "failed" ((← IO.monoMsNow) - start)
      [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart)), ("error", toJson (← ex.toMessageData.toString))]
    throw ex

meta def symbolicBenchTacticPhase {α : Type} (label : String) (computation : TacticM α) : TacticM α := do
  symbolicBenchEvent "stage" label "begin"
  let start ← IO.monoMsNow
  let hbStart ← IO.getNumHeartbeats
  try
    let value ← computation
    symbolicBenchEvent "stage" label "complete" ((← IO.monoMsNow) - start)
      [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart))]
    return value
  catch ex =>
    symbolicBenchEvent "stage" label "failed" ((← IO.monoMsNow) - start)
      [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart)), ("error", toJson (← ex.toMessageData.toString))]
    throw ex

elab "symbolic_bench_extract " path:str t:tactic : tactic => do
  symbolicBenchEvent "pipeline" "pipeline" "begin" 0 [
    ("maxHeartbeats", toJson (maxHeartbeats.get (← getOptions))),
    ("maxRecDepth", toJson (maxRecDepth.get (← getOptions)))]
  let start ← IO.monoMsNow
  withoutRecover <| evalTactic t
  symbolicBenchEvent "milestone" "preprocessing" "complete" ((← IO.monoMsNow) - start)
  symbolicBenchEvent "profile" "normalization" "complete"
  -- Deliberately abandon the measurement declaration; no theorem is admitted.
  throwError "SYMBOLIC_BMC_EXTRACTION_COMPLETE: query extraction only; no proof claimed"
'''

TAIL = r'''
    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
'''

REPLAY = r'''
import Veil
set_option Elab.async false
open Lean Elab Command in
run_cmd liftTermElabM do
  let event (status : String) (elapsed : Nat) (detail : String := "") : IO Unit := do
    let j := Json.mkObj [
      ("event", toJson "solver"), ("phase", toJson "solver"),
      ("status", toJson status), ("elapsed_ms", toJson elapsed), ("detail", toJson detail)]
    IO.FS.withFile __EVENT_PATH__ .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile __QUERY_PATH__).replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some __TIMEOUT__) false options
  let elapsed := (← IO.monoMsNow) - start
  match result with
  | .ok (.sat _) => event "sat" elapsed
  | .ok (.unsat _ _) => event "unsat" elapsed
  | .ok (.unknown reason) => event "unknown" elapsed reason.toString
  | .error error => event "error" elapsed error.toString
'''


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def atomic_json(path, value):
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')
    tmp.replace(path)


def events(path):
    if not path.exists():
        return []
    result = []
    for line in path.read_text(errors='replace').splitlines():
        try:
            result.append(json.loads(line))
        except json.JSONDecodeError:
            pass  # A killed process can leave only its final event truncated.
    return result


def failure_kind(message):
    lower = message.lower()
    if 'could not find native implementation' in lower:
        return 'missing_native_plugin'
    if 'maximum number of steps' in lower or 'maxsteps' in lower:
        return 'simp_steps'
    if 'maximum recursion depth' in lower or 'maxrecdepth' in lower:
        return 'recursion'
    if 'maximum number of heartbeats' in lower or 'maxheartbeats' in lower or 'deterministic timeout' in lower:
        return 'heartbeats'
    if 'not declared as a type' in lower or 'unsupported' in lower or 'failed to translate' in lower:
        return 'unsupported_translation'
    if 'type mismatch' in lower:
        return 'type_mismatch'
    return 'lean_error'


def run_process(command, repo, log_path, event_path, setup_cap, phase_cap, phase_event):
    start = time.monotonic()
    phase_start = None
    timeout = None
    with log_path.open('w') as log:
        process = subprocess.Popen(command, cwd=repo, stdout=log, stderr=subprocess.STDOUT,
                                   start_new_session=True, text=True)
        try:
            while process.poll() is None:
                if phase_start is None and any(e['event'] == phase_event and e['status'] == 'begin'
                                               for e in events(event_path)):
                    phase_start = time.monotonic()
                now = time.monotonic()
                if phase_start is None and now - start > setup_cap:
                    timeout = 'setup_timeout'
                elif phase_start is not None and now - phase_start > phase_cap:
                    timeout = phase_event + '_timeout'
                if timeout:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                    break
                time.sleep(0.05)
        except BaseException:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            raise
    return dict(exit_code=process.returncode, wall_ms=round((time.monotonic() - start) * 1000),
                observed_setup_ms=round((phase_start - start) * 1000) if phase_start else None,
                timeout=timeout, command=command)


def profile_limits(profile):
    return {'default': (200000, 512), 'recursion_only': (200000, 10000),
            'relaxed': (0, 10000)}[profile]


def make_source(repo, model, variant, depth, profile, event_path, query_path):
    lines = (repo / model['path']).read_text().splitlines(keepends=True)
    prefix = ''.join(lines[:model['cut_line'] - 1])
    hb, rec = profile_limits(profile)
    helper = HELPER.replace('__EVENT_PATH__', json.dumps(str(event_path)))
    imports = list(re.finditer(r'^(?:public\s+)?(?:meta\s+)?import\s+[^\n]+\n', prefix, re.M))
    if not imports:
        raise ValueError(f'No import insertion point in {model["path"]}')
    split = imports[-1].end()
    source = prefix[:split] + '\nset_option Elab.async false\nsection\n' + helper + '\nend\n' + prefix[split:] + '\n#gen_spec\n'
    source += f'\nset_option maxHeartbeats {hb}\nset_option maxRecDepth {rec}\n'
    source += 'set_option veil.smt.trust true\nset_option veil.smt.finiteModelFind true\n'
    stages = ('    symbolic_bench_phase "early_intros" symbolic_bench_intro_data\n'
              if variant == 'early' else '') + TAIL
    actions = 'any action' if depth == 1 else f'any {depth} actions'
    source += f'\nunsat trace [symbolic_bmc_probe] {{\n  {actions}\n  {model["query"]}\n}} by\n'
    source += f'  symbolic_bench_extract {json.dumps(str(query_path))} (\n{stages}  )\n'
    source += f'\nend {model["module"]}\n'
    return source, re.findall(r'^\s*set_option\s+[^\n]+', prefix, re.M)


def blank_row(model, depth, variant, profile, out):
    key = f'{model["model"]}__d{depth}__{variant}__{profile}'
    row = {name: None for name in FIELDS}
    row.update(cell_id=key, model=model['model'], path=model['path'], module=model['module'],
               depth=depth, variant=variant, profile=profile, status='not_started',
               translation_status='not_started', solver_status='not_reached',
               proof_status='no_reconstructed_proof',
               source_path=str(out / 'sources' / (key + '.lean')),
               query_path=str(out / 'queries' / (key + '.smt2')),
               event_path=str(out / 'events' / (key + '.jsonl')),
               translation_log=str(out / 'logs' / (key + '.translation.log')),
               solver_log=str(out / 'logs' / (key + '.solver.log')))
    return row


def collect_translation(row, execution, raw):
    if any(e['event']=='profile' and e['status']=='complete' for e in raw):
        row.update(status='profile_complete', translation_status='not_attempted',
                   solver_status='not_needed', failure_phase=None, failure_kind=None,
                   preprocessing_ms=sum(e['elapsed_ms'] for e in raw if e['event']=='stage' and e['status']=='complete'))
        return
    row.update(process_wall_ms=execution['wall_ms'], setup_ms=execution['observed_setup_ms'],
               translation_exit=execution['exit_code'], translation_timeout=execution['timeout'])
    done = next((e for e in reversed(raw) if e['event'] == 'pipeline' and e['status'] in ['complete', 'discharged']), None)
    stages = [e for e in raw if e['event'] == 'stage']
    complete = {e['phase']: e['elapsed_ms'] for e in stages if e['status'] == 'complete'}
    preproc_done = any(e['event'] == 'milestone' and e['phase'] == 'preprocessing' for e in raw)
    if preproc_done:
        row['preprocessing_ms'] = sum(complete.get(p, 0) for p in VEIL_PHASES)
    if done:
        if done['status'] == 'discharged':
            row.update(status='unsat_preprocessing', translation_status='discharged', solver_status='not_needed')
        else:
            row.update(status='query_ready', translation_status='complete', query_bytes=done['bytes'],
                       query_commands=done['commands'], smt_preprocessing_ms=sum(complete[p] for p in SMT_PHASES),
                       translation_ms=complete['translate'], serialization_ms=complete['serialize'])
            row['query_total_ms'] = sum(complete.values())
            row['query_sha256'] = sha(row['query_path'])
        return
    failed = next((e for e in reversed(stages) if e['status'] == 'failed'), None)
    last_begin = next((e for e in reversed(stages) if e['status'] == 'begin'), None)
    log = Path(row['translation_log']).read_text(errors='replace')
    phase = failed['phase'] if failed else (last_begin['phase'] if last_begin else 'setup')
    message = failed.get('error', '') if failed else log[-6000:]
    if execution['timeout']:
        row.update(status='translation_timeout', translation_status='timeout', failure_kind='wall_timeout')
    elif not any(e['event'] == 'pipeline' for e in raw):
        row.update(status='setup_failed', translation_status='setup_failed', failure_kind=failure_kind(message))
    else:
        row.update(status='translation_failed', translation_status='failed', failure_kind=failure_kind(message))
    row.update(failure_phase=phase, failure_message=message[:8000])


def solve(row, args, repo, out, lean_command):
    source = out / 'solver-sources' / (row['cell_id'] + '.lean')
    solver_events = out / 'events' / (row['cell_id'] + '.solver.jsonl')
    solver_events.unlink(missing_ok=True)
    text = REPLAY.replace('__EVENT_PATH__', json.dumps(str(solver_events)))
    text = text.replace('__QUERY_PATH__', json.dumps(row['query_path'])).replace('__TIMEOUT__', str(args.solver_timeout))
    source.write_text(text)
    execution = run_process(lean_command + [str(source)], repo,
                            Path(row['solver_log']), solver_events, args.setup_timeout,
                            args.solver_timeout + 5, 'solver')
    raw = events(solver_events)
    row.update(solver_exit=execution['exit_code'], solver_timeout=execution['timeout'],
               solver_process_wall_ms=execution['wall_ms'])
    result = next((e for e in reversed(raw) if e['status'] != 'begin'), None)
    if result:
        status, detail = result['status'], result.get('detail', '')
        if status == 'unknown' and ('timeout' in detail.lower() or 'time limit' in detail.lower()):
            status = 'timeout'
        row.update(solver_status=status, solver_ms=result['elapsed_ms'])
        row['status'] = status if status in ['sat', 'unsat'] else 'solver_' + status
        if status in ['sat', 'unsat']:
            row['completed_total_ms'] = row['query_total_ms'] + row['solver_ms']
        else:
            row.update(failure_phase='solver', failure_kind='solver_' + status, failure_message=detail)
    else:
        status = 'process_timeout' if execution['timeout'] else 'error'
        row.update(status='solver_' + status, solver_status=status, failure_phase='solver',
                   failure_kind='wall_timeout' if execution['timeout'] else 'solver_error',
                   failure_message=Path(row['solver_log']).read_text(errors='replace')[-6000:])
    return execution, raw


def export(out):
    cells = [json.loads(p.read_text()) for p in sorted((out / 'cells').glob('*.json'))]
    with (out / 'runs.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=FIELDS)
        writer.writeheader()
        writer.writerows(c['row'] for c in cells)
    with (out / 'stages.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=STAGE_FIELDS)
        writer.writeheader()
        for cell in cells:
            base = {k: cell['row'][k] for k in ['cell_id', 'model', 'depth', 'variant', 'profile']}
            for event in cell.get('events', []):
                if event['event'] == 'stage':
                    values = {k: event.get(k) for k in ['phase', 'status', 'elapsed_ms', 'error', 'heartbeats']}
                    if values['error']:
                        values['error'] = values['error'][:8000]
                    writer.writerow(dict(base, **values))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--manifest', type=Path, default=HERE / 'manifest.json')
    parser.add_argument('--out', type=Path, default=HERE / 'results')
    parser.add_argument('--depths', nargs='+', type=int, default=[1, 2, 4, 8, 16, 32])
    parser.add_argument('--variants', nargs='+', choices=['old', 'early'], default=['old', 'early'])
    parser.add_argument('--models', nargs='+')
    parser.add_argument('--profile', choices=['default', 'recursion_only', 'relaxed'], default='default')
    parser.add_argument('--setup-timeout', type=float, default=60)
    parser.add_argument('--translation-timeout', type=float, default=60)
    parser.add_argument('--solver-timeout', type=int, default=10)
    parser.add_argument('--generate-only', action='store_true')
    parser.add_argument('--translation-only', action='store_true')
    parser.add_argument('--solver-only', action='store_true')
    parser.add_argument('--retry-failed', action='store_true')
    parser.add_argument('--limit-cells', type=int)
    args = parser.parse_args()
    repo, out = args.repo.resolve(), args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    for name in ['sources', 'solver-sources', 'events', 'logs', 'queries', 'cells']:
        (out / name).mkdir(exist_ok=True)
    models = json.loads(args.manifest.read_text())
    if isinstance(models, dict):
        models = models['models']
    if args.models:
        models = [m for m in models if m['model'] in args.models]
    if not models:
        parser.error('No models selected')
    metadata = dict(repo=str(repo), commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip(),
                    script_sha256=sha(__file__), manifest_sha256=sha(args.manifest),
                    profiles=dict(default=dict(maxHeartbeats=200000, maxRecDepth=512), recursion_only=dict(maxHeartbeats=200000, maxRecDepth=10000), relaxed=dict(maxHeartbeats=0, maxRecDepth=10000)),
                    selected_profile=args.profile, simp_maxSteps=100000, query_trust=True, embedBool=False,
                    solver_options=dict(finite_model_find=True, nl_ext_tplanes=True, enum_inst_interleave=True),
                    setup_options='Preserved from each model prefix; recorded per cell',
                    timing='Single sample per isolated cell; sequential processes; stage wall time excludes startup/model setup and event IO. No statistical confidence claim.',
                    trace_semantics='exactly N actions; these samples do not cover all lengths <= N',
                    proof_status='Query extraction deliberately aborts; no admitted measurement theorem or reconstructed Lean proof is used as verification.',
                    depths=args.depths, variants=args.variants, models=models, setup_timeout_seconds=args.setup_timeout,
                    translation_timeout_seconds=args.translation_timeout, solver_timeout_seconds=args.solver_timeout,
                    ordering='depth-major, model-major, paired variants alternate order by model/depth index',
                    platform=platform.platform(), cpu=next((s.split(':',1)[1].strip() for s in Path('/proc/cpuinfo').read_text().splitlines() if s.startswith('model name')), 'unknown'),
                    core_source_sha256=sha(repo / 'Veil/Frontend/DSL/Tactic/Core.lean'),
                    core_olean_sha256=sha(repo / '.lake/build/lib/lean/Veil/Frontend/DSL/Tactic/Core.olean'))
    if not (out / 'metadata.json').exists():
        atomic_json(out / 'metadata.json', metadata)
    atomic_json(out / 'latest-invocation.json', metadata)
    plugin = repo / '.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so'
    if not plugin.exists():
        parser.error(f'Missing native cvc5 plugin: {plugin}')
    lean_command = ['lake', 'env', 'lean', '-D', 'Elab.async=false', '--plugin=' + str(plugin)]
    schedule = []
    for di, depth in enumerate(args.depths):
        for mi, model in enumerate(models):
            variants = args.variants if (di + mi) % 2 == 0 else list(reversed(args.variants))
            for variant in variants:
                row = blank_row(model, depth, variant, args.profile, out)
                cell_path = out / 'cells' / (row['cell_id'] + '.json')
                source, options = make_source(repo, model, variant, depth, args.profile,
                                              Path(row['event_path']), Path(row['query_path']))
                source_path = Path(row['source_path'])
                if cell_path.exists():
                    previous = json.loads(cell_path.read_text())
                    if previous.get('source_sha256') != hashlib.sha256(source.encode()).hexdigest():
                        raise RuntimeError(f'Source changed for checkpoint {row["cell_id"]}; use fresh --out')
                source_path.write_text(source)
                cell = dict(row=row, model=model, source_sha256=sha(source_path),
                            original_sha256=sha(repo / model['path']), inherited_setup_options=options)
                if not cell_path.exists():
                    atomic_json(cell_path, cell)
                schedule.append(cell_path)
    atomic_json(out / 'requested-cells.json', [p.stem for p in schedule])
    export(out)
    count = 0
    for cell_path in schedule:
        if args.generate_only or (args.limit_cells is not None and count >= args.limit_cells):
            break
        cell = json.loads(cell_path.read_text())
        row = cell['row']
        status = row['status']
        if status in ['sat', 'unsat', 'unsat_preprocessing']:
            continue
        if status not in ['not_started', 'query_ready'] and not args.retry_failed:
            continue
        if args.solver_only and row['translation_status'] != 'complete':
            continue
        if args.translation_only and row['translation_status'] == 'complete':
            continue
        print(f'BEGIN {row["cell_id"]}', flush=True)
        if not args.solver_only and row['translation_status'] != 'complete':
            Path(row['event_path']).unlink(missing_ok=True)
            Path(row['query_path']).unlink(missing_ok=True)
            cell['translation_execution'] = run_process(lean_command + [row['source_path']], repo,
                Path(row['translation_log']), Path(row['event_path']), args.setup_timeout,
                args.translation_timeout, 'pipeline')
            cell['events'] = events(Path(row['event_path']))
            collect_translation(row, cell['translation_execution'], cell['events'])
            atomic_json(cell_path, cell)
        if row['translation_status'] == 'complete' and not args.translation_only:
            cell['solver_execution'], cell['solver_events'] = solve(row, args, repo, out, lean_command)
        atomic_json(cell_path, cell)
        export(out)
        print(f'END {row["cell_id"]} {row["status"]} phase={row["failure_phase"]} kind={row["failure_kind"]} query_ms={row["query_total_ms"]} solver_ms={row["solver_ms"]}', flush=True)
        count += 1
        if row['solver_status'] in ['sat', 'unsat']:
            other_variant = 'early' if row['variant'] == 'old' else 'old'
            other_path = out / 'cells' / (row['cell_id'].replace('__' + row['variant'] + '__', '__' + other_variant + '__') + '.json')
            if other_path.exists():
                other = json.loads(other_path.read_text())['row']
                if other['solver_status'] in ['sat', 'unsat'] and other['solver_status'] != row['solver_status']:
                    raise RuntimeError(f'Contradictory solver verdicts: {row["cell_id"]} vs {other["cell_id"]}; STOP for investigation')
    export(out)


if __name__ == '__main__':
    main()
