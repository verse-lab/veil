#!/usr/bin/env python3
"""Model-batched query extraction with independent command budgets/checkpoints.

Model setup is shared; each exact-N trace is a separate Lean command. The active
cell has a wall watchdog. On timeout, kill the process group, retain finished
cells, mark only the active cell timed out, and restart the remaining commands.
No solver is run here. solve_batch.py replays only successfully emitted queries.
"""
import argparse
import hashlib
import json
import os
import re
import signal
import subprocess
import textwrap
import time
from pathlib import Path

import run as common


def helper():
    value = common.HELPER.replace('(extra : List (String × Json) := []) : IO Unit := do',
                                  '(extra : List (String × Json) := []) : CoreM Unit := do')
    value = value.replace('__EVENT_PATH__', '(System.FilePath.mk ((← getOptions).get `symbolicBench.eventPath ""))')
    before, body = value.split('elab "symbolic_bench_extract " path:str t:tactic : tactic => do\n', 1)
    return before + 'elab "symbolic_bench_extract " eventPath:str path:str t:tactic : tactic => do\n' + \
        '  withOptions (fun opts => opts.set `symbolicBench.eventPath eventPath.getString) do\n' + textwrap.indent(body, '  ')


def local_tail():
    local = r"""
    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])

"""
    return '    __veil_bmc_if_local (\n' + local + '    ) else (\n' + common.TAIL + '    )\n'


def source_for(repo, model, cells, batch_path, marker, profile):
    prefix = ''.join((repo / model['path']).read_text().splitlines(keepends=True)[:model['cut_line'] - 1])
    imports = list(re.finditer(r'^(?:public\s+)?(?:meta\s+)?import\s+[^\n]+\n', prefix, re.M))
    if not imports:
        raise RuntimeError(f'No import boundary: {model["path"]}')
    split = imports[-1].end()
    source = prefix[:split] + '\nset_option Elab.async false\nsection\n' + helper() + '\nend\n' + prefix[split:] + '\n#gen_spec\n'
    source += f'\nrun_cmd Lean.Elab.Command.liftTermElabM do\n  IO.FS.writeFile {json.dumps(str(marker))} (toString (← IO.monoMsNow))\n'
    model_ready_line = len(source.splitlines())
    hb, rec = common.profile_limits(profile)
    source += f'\nset_option maxHeartbeats {hb}\nset_option maxRecDepth {rec}\n'
    source += 'set_option veil.smt.trust true\nset_option veil.smt.finiteModelFind true\n'
    boundaries = {}
    for i, cell in enumerate(cells):
        row = cell['row']
        event_options = f'  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath {json.dumps(row["event_path"])}) do\n'
        source += '\nrun_cmd Lean.Elab.Command.liftTermElabM do\n' + event_options + '    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"\n'
        begin = len(source.splitlines()) + 1
        actions = 'any action' if row['depth'] == 1 else f'any {row["depth"]} actions'
        source += f'\nunsat trace [symbolic_bmc_probe_{i}] {{\n  {actions}\n  {model["query"]}\n}} by\n'
        source += f'  symbolic_bench_extract {json.dumps(row["event_path"])} {json.dumps(row["query_path"])} (\n'
        if row['variant'] in ['early', 'local']:
            source += '    symbolic_bench_phase "early_intros" symbolic_bench_intro_data\n'
        source += (local_tail() if row['variant'] == 'local' else common.TAIL) + '  )\n'
        end = len(source.splitlines())
        source += 'run_cmd Lean.Elab.Command.liftTermElabM do\n' + event_options + '    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"\n'
        boundaries[row['cell_id']] = (begin, end)
    source += f'\nend {model["module"]}\n'
    batch_path.write_text(source)
    return model_ready_line, boundaries


def log_messages(log, source):
    pattern = re.compile(re.escape(str(source)) + r':(\d+):(\d+): (error[^\n]*|warning[^\n]*)')
    matches = list(pattern.finditer(log))
    result = []
    for i, match in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(log)
        result.append((int(match.group(1)), match.group(3).startswith('error'), log[match.start():end]))
    return result


def run_model_batch(repo, model, cells, out, args, attempt):
    batch_id = f'{model["model"]}__{args.profile}__batch{attempt}'
    batch_source = out / 'batch-sources' / (batch_id + '.lean')
    batch_log = out / 'batch-logs' / (batch_id + '.log')
    marker = out / 'batch-events' / (batch_id + '.ready')
    marker.unlink(missing_ok=True)
    ready_line, boundaries = source_for(repo, model, cells, batch_source, marker, args.profile)
    for cell in cells:
        row = cell['row']
        Path(row['event_path']).unlink(missing_ok=True)
        Path(row['query_path']).unlink(missing_ok=True)
        row['source_path'] = str(batch_source)
        row['batch_id'] = batch_id
        cell.update(source_sha256=common.sha(batch_source), batch_log=str(batch_log))
        common.atomic_json(out / 'cells' / (row['cell_id'] + '.json'), cell)
    plugin = repo / '.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so'
    command = ['lake', 'env', 'lean', '-D', 'Elab.async=false', '--plugin=' + str(plugin), str(batch_source)]
    start = time.monotonic()
    model_ready_at = None
    active = None
    active_at = None
    pipeline_at = None
    timeout = None
    ended_cells = set()
    with batch_log.open('w') as log:
        process = subprocess.Popen(command, cwd=repo, stdout=log, stderr=subprocess.STDOUT,
                                   start_new_session=True, text=True)
        try:
            while process.poll() is None:
                now = time.monotonic()
                if model_ready_at is None and marker.exists():
                    model_ready_at = now
                found_active = False
                for cell in cells:
                    row = cell['row']
                    if row['cell_id'] in ended_cells:
                        continue
                    raw = common.events(Path(row['event_path']))
                    begun = any(e['event'] == 'query_elaboration' and e['status'] == 'begin' for e in raw)
                    ended = any(e['event'] == 'query_elaboration' and e['status'] == 'end' for e in raw)
                    if any(e['event'] == 'pipeline' and e['status'] == 'begin' for e in raw) and not begun:
                        raise RuntimeError('Missing query-begin marker; refuse to disable watchdog: '+row['cell_id'])
                    if ended:
                        ended_cells.add(row['cell_id'])
                    if begun and not ended:
                        found_active = True
                        if active != row['cell_id']:
                            active, active_at, pipeline_at = row['cell_id'], now, None
                        if pipeline_at is None and any(e['event'] == 'pipeline' and e['status'] == 'begin' for e in raw):
                            pipeline_at = now
                        break
                if not found_active:
                    active, active_at, pipeline_at = None, None, None
                if model_ready_at is None and now - start > args.setup_timeout:
                    timeout = 'model_setup_timeout'
                elif active_at is not None and pipeline_at is None and now - active_at > args.translation_timeout:
                    timeout = 'query_elaboration_timeout'
                elif pipeline_at is not None and now - pipeline_at > args.translation_timeout:
                    timeout = 'pipeline_timeout'
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
    if model_ready_at is None and marker.exists():
        model_ready_at = time.monotonic()
    execution = dict(batch_id=batch_id, source=str(batch_source), log=str(batch_log),
                     exit_code=process.returncode, wall_ms=round((time.monotonic()-start)*1000),
                     setup_ms=round((model_ready_at-start)*1000) if model_ready_at else None,
                     timeout=timeout, active_cell=active, command=command)
    common.atomic_json(out / 'batch-events' / (batch_id + '.execution.json'), execution)
    log = batch_log.read_text(errors='replace')
    if 'Could not find native implementation' in log:
        raise RuntimeError(f'Missing native implementation in benchmark dependencies; stop: {batch_log}')
    messages = log_messages(log, batch_source)
    setup_errors = [text for line, error, text in messages if error and line <= ready_line]
    marker_errors = [text for line, error, text in messages if error and line > ready_line
                     and not any(begin <= line <= end for begin, end in boundaries.values())]
    if marker_errors:
        raise RuntimeError('Benchmark marker command failed: '+marker_errors[0][:1000])
    setup_failed = model_ready_at is None or bool(setup_errors)
    unfinished = []
    for cell in cells:
        row = cell['row']
        raw = common.events(Path(row['event_path']))
        cell['events'] = raw
        cell['batch_execution'] = execution
        row['batch_setup_ms'] = execution['setup_ms']
        begin, end = boundaries[row['cell_id']]
        cell_log = '\n'.join(text for line, _, text in messages if begin <= line <= end)
        Path(row['translation_log']).write_text(cell_log)
        if setup_failed:
            row.update(status='blocked_model_setup', translation_status='not_started', failure_phase='model_setup',
                       failure_kind='wall_timeout' if timeout == 'model_setup_timeout' else common.failure_kind('\n'.join(setup_errors)),
                       failure_message=('\n'.join(setup_errors) or log)[-8000:], translation_exit=process.returncode,
                       translation_timeout=timeout)
        elif not raw:
            unfinished.append(cell)
            continue
        else:
            query_begin = next((e for e in raw if e['event'] == 'query_elaboration' and e['status'] == 'begin'), None)
            pipeline_begin = next((e for e in raw if e['event'] == 'pipeline' and e['status'] == 'begin'), None)
            if query_begin and pipeline_begin:
                row['query_elaboration_ms'] = pipeline_begin['mono_ms'] - query_begin['mono_ms']
            local_execution = dict(exit_code=process.returncode, wall_ms=None, observed_setup_ms=None,
                                   timeout=timeout if row['cell_id'] == active and timeout else None)
            common.collect_translation(row, local_execution, raw)
            if query_begin and not pipeline_begin:
                row.update(status='query_elaboration_timeout' if local_execution['timeout'] else 'query_elaboration_failed',
                           translation_status='timeout' if local_execution['timeout'] else 'failed',
                           failure_phase='query_elaboration', failure_message=cell_log[:8000],
                           failure_kind='wall_timeout' if local_execution['timeout'] else common.failure_kind(cell_log))
            # A completed query is valid only if no earlier unrelated command error occurred.
            unexpected = [text for line, error, text in messages if begin <= line <= end and error
                          and 'SYMBOLIC_BMC_EXTRACTION_COMPLETE' not in text]
            if row['translation_status'] == 'complete' and unexpected:
                row.update(status='query_elaboration_failed', translation_status='failed', failure_phase='query_elaboration',
                           failure_kind=common.failure_kind('\n'.join(unexpected)), failure_message='\n'.join(unexpected)[:8000])
        common.atomic_json(out / 'cells' / (row['cell_id'] + '.json'), cell)
        print(f'  {row["cell_id"]} {row["status"]} phase={row["failure_phase"]} kind={row["failure_kind"]} query_ms={row["query_total_ms"]}', flush=True)
    common.export(out)
    print(f'END {batch_id} wall={execution["wall_ms"]/1000:.1f}s setup={execution["setup_ms"]} timeout={timeout} remaining={len(unfinished)}', flush=True)
    if len(unfinished) == len(cells):
        raise RuntimeError(f'Batch made no progress: {batch_log}. Stop rather than restarting indefinitely.')
    return unfinished


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--manifest', type=Path, default=common.HERE / 'manifest.json')
    parser.add_argument('--out', type=Path, default=common.HERE / 'results')
    parser.add_argument('--models', nargs='+')
    parser.add_argument('--depths', nargs='+', type=int, default=[1,2,4,8,16,32])
    parser.add_argument('--variants', nargs='+', choices=['early','local'], default=['early','local'])
    parser.add_argument('--profile', choices=['default','recursion_only','relaxed'], default='default')
    parser.add_argument('--setup-timeout', type=float, default=60)
    parser.add_argument('--translation-timeout', type=float, default=60)
    parser.add_argument('--generate-only', action='store_true')
    args = parser.parse_args()
    repo, out = args.repo.resolve(), args.out.resolve()
    plugin = repo / '.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so'
    if not plugin.exists():
        parser.error(f'Missing native cvc5 plugin: {plugin}')
    for name in ['sources','solver-sources','events','logs','queries','cells','batch-sources','batch-logs','batch-events']:
        (out / name).mkdir(parents=True, exist_ok=True)
    models = json.loads(args.manifest.read_text())
    if args.models:
        models = [m for m in models if m['model'] in args.models]
    metadata = dict(repo=str(repo), commit=subprocess.check_output(['git','rev-parse','HEAD'], cwd=repo, text=True).strip(),
                    script_sha256=common.sha(__file__), common_script_sha256=common.sha(common.__file__),
                    manifest_sha256=common.sha(args.manifest), models=models, depths=args.depths, variants=args.variants,
                    selected_profile=args.profile, query_limits=dict(maxHeartbeats=common.profile_limits(args.profile)[0],
                    maxRecDepth=common.profile_limits(args.profile)[1], simp_maxSteps=100000),
                    setup_options='Preserved from model prefix; per-cell manifest records source options.',
                    query_trust=True, embedBool=False, finiteModelFind=True,
                    native_cvc5_plugin=str(plugin), native_cvc5_plugin_sha256=common.sha(plugin),
                    execution='One model setup per batch; independent trace commands and command budgets. Shared process/cache state; variant order alternates per depth/model. Timeout kills process group and restarts unstarted cells.',
                    setup_timeout_seconds=args.setup_timeout, query_elaboration_timeout_seconds=args.translation_timeout,
                    pipeline_timeout_seconds=args.translation_timeout, solver_timeout_seconds=10,
                    samples_per_cell=1, trace_semantics='exactly N actions; does not cover all lengths <= N',
                    timing='Completed stage sums exclude model setup, trace VC elaboration, event IO, UI/model reconstruction and kernel proof reconstruction. Process wall times live in batch-events/*.execution.json; do not sum shared setup once per cell.',
                    proof_status='Query-extraction declarations deliberately error; no sorry or claimed theorem. Results come from separate trusted solver replay.',
                    core_source_sha256=common.sha(repo/'Veil/Frontend/DSL/Tactic/Core.lean'),
                    core_olean_sha256=common.sha(repo/'.lake/build/lib/lean/Veil/Frontend/DSL/Tactic/Core.olean'))
    if not (out/'metadata.json').exists():
        common.atomic_json(out/'metadata.json', metadata)
    common.atomic_json(out/'latest-invocation.json', metadata)
    planned = []
    groups = []
    for mi, model in enumerate(models):
        cells = []
        for di, depth in enumerate(args.depths):
            variants = args.variants if (mi+di)%2==0 else list(reversed(args.variants))
            for variant in variants:
                row = common.blank_row(model, depth, variant, args.profile, out)
                path = out/'cells'/(row['cell_id']+'.json')
                if path.exists():
                    cell = json.loads(path.read_text())
                    if cell['model'] != model:
                        raise RuntimeError(f'Manifest changed for {row["cell_id"]}; use a fresh output directory')
                else:
                    cell = dict(row=row, model=model, original_sha256=common.sha(repo/model['path']),
                                inherited_setup_options=model.get('source_options', []))
                    common.atomic_json(path, cell)
                planned.append(row['cell_id'])
                if cell['row']['status']=='not_started':
                    cells.append(cell)
        groups.append((model,cells))
    common.atomic_json(out/'requested-cells.json', planned)
    common.export(out)
    if args.generate_only:
        return
    for model, cells in groups:
        attempt = 1
        while (out/'batch-events'/f'{model["model"]}__{args.profile}__batch{attempt}.execution.json').exists():
            attempt += 1
        while cells:
            print(f'BEGIN {model["model"]} batch{attempt} cells={len(cells)}', flush=True)
            cells = run_model_batch(repo, model, cells, out, args, attempt)
            attempt += 1


if __name__=='__main__':
    main()
