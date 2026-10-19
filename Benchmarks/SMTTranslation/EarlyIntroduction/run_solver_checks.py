#!/usr/bin/env python3
"""Generate example probes, solve their queries, then replay solvers sequentially."""
from pathlib import Path
import argparse, json, os, signal, subprocess, time
from make_solver_checks import MODELS, generate
from summarize import summarize

REPLAY_TEMPLATE = '''import Veil
set_option Elab.async false
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd liftTermElabM do
  let root := System.FilePath.mk __ROOT__
  let labels := __LABELS__
  let options := Smt.defaultSolverOptions ++ [("finite-model-find", "true"),
    ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  for label in labels do
    let path := root / (label ++ ".smt2")
    if ← path.pathExists then
      let query := (← IO.FS.readFile path).replace "(check-sat)" ""
      let start ← IO.monoMsNow
      let result ← Smt.solve query (some __TIMEOUT__) false options
      let status := match result with
        | .ok (.sat _) => "sat"
        | .ok (.unsat _ _) => "unsat"
        | .ok (.unknown reason) => "unknown:" ++ reason.toString
        | .error err => "error:" ++ err.toString
      IO.println s!"REPLAY_RESULT {label} status={status} solver_ms={(← IO.monoMsNow)-start} bytes={query.utf8ByteSize}"
    else
      IO.println s!"REPLAY_MISSING {label}"
'''

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--models', nargs='+', choices=[m[0] for m in MODELS], default=[m[0] for m in MODELS])
    parser.add_argument('--depths', nargs='+', type=int, default=[4, 8])
    parser.add_argument('--solver-timeout', type=int, default=10)
    parser.add_argument('--process-timeout', type=int, default=180)
    parser.add_argument('--replay-only', action='store_true')
    parser.add_argument('--generate-only', action='store_true')
    args = parser.parse_args()
    repo, output = args.repo.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    plugin = repo / '.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so'
    if not plugin.exists():
        parser.error(f'build Veil and its native cvc5 dependency first: missing {plugin}')
    if not args.replay_only:
        generate(repo, output, args.models, args.depths, args.solver_timeout)
    if args.generate_only:
        return
    models = json.loads((output / 'models.json').read_text())
    selected = [m[0] for m in models if m[0] in args.models]
    executions = []
    def run(name, source, timeout):
        start = time.monotonic()
        command = ['lake', 'env', 'lean', '--plugin=' + str(plugin), str(source)]
        with (output / (name + '.log')).open('w') as log:
            process = subprocess.Popen(command, cwd=repo, stdout=log,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            try:
                status = process.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                # lake can have a running Lean child; terminate the whole group.
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                status = 'process_timeout'
        executions.append(dict(name=name, status=status, wall_seconds=time.monotonic()-start))
        print(json.dumps(executions[-1]), flush=True)
    if not args.replay_only:
        for name in selected:
            run(name, output / (name + '.lean'), args.process_timeout)
    labels = [f'{name}_{mode}_{depth}' for name in selected for depth in args.depths for mode in ['old', 'early']]
    replay = REPLAY_TEMPLATE.replace('__ROOT__', json.dumps(str(output)))
    replay = replay.replace('__LABELS__', '#[' + ', '.join(json.dumps(label) for label in labels) + ']')
    replay = replay.replace('__TIMEOUT__', str(args.solver_timeout))
    (output / 'Replay.lean').write_text(replay)
    run('Replay', output / 'Replay.lean', max(args.process_timeout, len(labels) * (args.solver_timeout+2)))
    (output / 'execution.json').write_text(json.dumps(executions, indent=2) + '\n')
    summarize(output, args.depths)

if __name__ == '__main__':
    main()
