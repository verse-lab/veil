#!/usr/bin/env python3
"""LSP regression for prove_veil_invariant_goal.

Run after `lake build VeilTest.Regression.ProveInvariantGoal`:
  python3 scripts/tests/test-invariant-goal-incrementality.py [--deferred]

For the multi-module VC manager regression, first build
`VeilTest.Regression.ToFix.VCManagerMultiModuleIncrementality`, then run:
  python3 scripts/tests/test-invariant-goal-incrementality.py --multi-module

For the single-module VC manager regression, first build
`VeilTest.Regression.ToFix.VCManagerIncrementality`, then run:
  python3 scripts/tests/test-invariant-goal-incrementality.py --vc-manager

The --multi-module and --vc-manager modes currently fail because the global
VC manager is not restored with Lean's environment. The latter compares a
fresh open without a proof with incrementally deleting the same proof.

Edits a virtual document only. Counts actual tactic executions in a temporary
file, so replayed diagnostics cannot be mistaken for proof reuse. Evidence is
retained in the printed temporary directory.
"""
import json
import queue
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path

root = Path(__file__).resolve().parents[2]
deferred = '--deferred' in sys.argv[1:]
work = Path(tempfile.mkdtemp(prefix='veil-invariant-goal-'))
print('Evidence:', work, flush=True)
log = work / 'executions.txt'
log.write_text('')
err = (work / 'server.stderr').open('w')
proc = subprocess.Popen(['lake', 'serve'], cwd=root, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=err)
messages = queue.Queue()

def read_messages():
    while True:
        headers = {}
        while True:
            line = proc.stdout.readline()
            if not line:
                messages.put({'eof': True})
                return
            if line in (b'\r\n', b'\n'):
                break
            key, value = line.decode().split(':', 1)
            headers[key.lower()] = value.strip()
        messages.put(json.loads(proc.stdout.read(int(headers['content-length']))))

threading.Thread(target=read_messages, daemon=True).start()
next_id = 0
notifications = []

def send(method, params, request=False):
    global next_id
    msg = {'jsonrpc': '2.0', 'method': method, 'params': params}
    if request:
        next_id += 1
        msg['id'] = next_id
    data = json.dumps(msg).encode()
    proc.stdin.write(f'Content-Length: {len(data)}\r\n\r\n'.encode() + data)
    proc.stdin.flush()
    if not request:
        return
    while True:
        response = messages.get(timeout=180)
        if response.get('eof'):
            raise RuntimeError((work / 'server.stderr').read_text())
        if 'method' in response and 'id' in response:
            reply = json.dumps({'jsonrpc': '2.0', 'id': response['id'], 'result': None}).encode()
            proc.stdin.write(f'Content-Length: {len(reply)}\r\n\r\n'.encode() + reply)
            proc.stdin.flush()
            continue
        if response.get('id') == msg['id']:
            if 'error' in response:
                raise RuntimeError(response)
            return response.get('result')
        notifications.append(response)

uri = (root / 'VeilTest/Regression/ProveInvariantGoal.lean').as_uri()
source = '''module
public import Veil

open Lean Elab Tactic in
@[tactic Veil.veil_unveil] public meta def countedUnveil : Tactic := fun stx => do
  IO.FS.withFile LOG .append fun h => h.putStrLn "unveil"
  Veil.elabVeilTactics stx

veil module IncrementalInvariantGoal
individual x : Nat
after_init { x := 0 }
action step { require x < 10; x := x + 1 }
action more { require x < 9; x := x + 2 }
invariant [bounded] x ≤ 10
invariant [weaker] x ≤ 11
#gen_spec

prove_veil_invariant_goal step bounded using wp by
  run_tac IO.FS.withFile LOG .append fun h => h.putStrLn "prefix"
  skip
  grind

end IncrementalInvariantGoal
'''.replace('LOG', json.dumps(str(log)))
if deferred:
    source = source.replace('veil module IncrementalInvariantGoal',
                            'set_option veil.deferVCGeneration true\nveil module IncrementalInvariantGoal')
initial_source = source

def check(version, label, incomplete=False):
    send('textDocument/waitForDiagnostics', {'uri': uri, 'version': version}, True)
    (work / f'notifications-{version}.json').write_text(json.dumps(notifications, indent=2))
    ds = [n['params'] for n in notifications if n.get('method') == 'textDocument/publishDiagnostics' and n['params'].get('uri') == uri and n['params'].get('version') == version]
    diagnostics = ds[-1]['diagnostics'] if ds else []
    print(label, 'diagnostics:', json.dumps(diagnostics, ensure_ascii=False), flush=True)
    assert ds, 'missing diagnostics publication'
    problems = [d for d in diagnostics if d.get('severity') in (1, 2)]
    if incomplete:
        assert len(problems) == 1 and problems[0]['message'].startswith('unsolved goals'), problems
        assert 'FieldRepresentation' not in problems[0]['message'], problems
    else:
        assert not problems, problems
    print(label, 'executions:', log.read_text().splitlines(), flush=True)

def wait_for_execution(marker, count=1):
    deadline = time.monotonic() + 30
    while time.monotonic() < deadline:
        if log.read_text().splitlines().count(marker) >= count:
            return
        time.sleep(0.01)
    raise AssertionError(f'timed out waiting for {marker}: {log.read_text()}')

try:
    send('initialize', {'processId': None, 'rootUri': root.as_uri(), 'capabilities': {}}, True)
    send('initialized', {})
    if '--vc-manager' in sys.argv[1:]:
        fixture = root / 'VeilTest/Regression/ToFix/VCManagerIncrementality.lean'
        uri = fixture.as_uri()
        source = fixture.read_text()
        proof = 'prove_veil_invariant_goal step bounded using wp by\n  grind\n'
        assert source.count(proof) == 1, 'missing unique proof to delete'
        without_proof = source.replace(proof, '', 1)
        # Establish the fresh result first: #gen_theorems only adds successful
        # witnesses, so the absent manual proof does not itself cause an error.
        send('textDocument/didOpen', {'textDocument': {'uri': uri, 'languageId': 'lean4',
                                                     'version': 1, 'text': without_proof}})
        check(1, 'fresh file without proof')
        send('textDocument/didChange', {'textDocument': {'uri': uri, 'version': 2},
                                       'contentChanges': [{'text': source}]})
        check(2, 'insert proof')
        # Keep #gen_spec and the initializer proof unchanged, so Lean restores
        # a snapshot whose environment no longer contains step_bounded. The
        # manager must not reuse the successful witness registered in version 2.
        send('textDocument/didChange', {'textDocument': {'uri': uri, 'version': 3},
                                       'contentChanges': [{'text': without_proof}]})
        check(3, 'delete proof in one module')
        print('PASS; evidence:', work, flush=True)
        sys.exit(0)
    if '--multi-module' in sys.argv[1:]:
        # Resuming an earlier proof must not use the verifier state left behind
        # by a later Veil module. Leave this as a failing regression until the
        # manager's state follows Lean's incremental environment snapshots.
        fixture = root / 'VeilTest/Regression/ToFix/VCManagerMultiModuleIncrementality.lean'
        uri = fixture.as_uri()
        source = fixture.read_text()
        send('textDocument/didOpen', {'textDocument': {'uri': uri, 'languageId': 'lean4',
                                                     'version': 1, 'text': source}})
        check(1, 'fresh multi-module file')
        old = 'prove_veil_invariant_goal keep trivial using wp by\n  done'
        assert source.count(old) == 1, 'missing unique proof to edit in the multi-module regression'
        source = source.replace(old, old.replace('  done', '  skip\n  done'), 1)
        send('textDocument/didChange', {'textDocument': {'uri': uri, 'version': 2},
                                       'contentChanges': [{'text': source}]})
        check(2, 'edit proof in first module')
        print('PASS; evidence:', work, flush=True)
        sys.exit(0)
    send('textDocument/didOpen', {'textDocument': {'uri': uri, 'languageId': 'lean4', 'version': 1, 'text': source}})
    check(1, 'open')
    original = log.read_text()
    assert original.splitlines() == ['unveil', 'prefix']
    goal_line = source.splitlines().index('  skip')
    for line, character in [(goal_line, 2), (goal_line - 2, len(source.splitlines()[goal_line - 2]))]:
        goal = send('$/lean/plainGoal', {'textDocument': {'uri': uri}, 'position': {'line': line, 'character': character}}, True)
        print('goal:', goal, flush=True)
        assert goal and 'FieldRepresentation' not in goal['rendered'] and 'meetsSpecification' not in goal['rendered']
    for version, (old, new, label, expected) in enumerate([
        ('  grind', '  skip\n  grind', 'longer proof', []),
        ('  skip\n  grind', '  grind', 'shorter proof', []),
        ('h.putStrLn "prefix"', 'h.putStrLn "prefix2"', 'different proof prefix', ['prefix2']),
        ('step bounded using wp', 'step weaker using wp', 'different invariant', ['unveil', 'prefix2']),
        ('step weaker using wp', 'more weaker using wp', 'different action', ['unveil', 'prefix2']),
        ('more weaker using wp', 'more weaker using tr', 'different VC style', ['unveil', 'prefix2']),
        ('require x < 9', 'require x < 8', 'upstream action edit', ['unveil', 'prefix2']),
    ], 2):
        before = log.read_text()
        source = source.replace(old, new)
        send('textDocument/didChange', {'textDocument': {'uri': uri, 'version': version}, 'contentChanges': [{'text': source}]})
        check(version, label)
        after = log.read_text()
        assert after[len(before):].splitlines() == expected, (label, before, after)
    # An empty proof should report the simplified obligation, including at `by`.
    header = next(line for line in source.splitlines() if line.startswith('prove_veil_invariant_goal'))
    source = source[:source.index(header)] + header + '\n\nend IncrementalInvariantGoal\n'
    send('textDocument/didChange', {'textDocument': {'uri': uri, 'version': version + 1},
                                   'contentChanges': [{'text': source}]})
    check(version + 1, 'empty proof', incomplete=True)
    goal = send('$/lean/plainGoal', {'textDocument': {'uri': uri},
                                    'position': {'line': source.splitlines().index(header),
                                                 'character': len(header)}}, True)
    assert goal and 'FieldRepresentation' not in goal['rendered']
    assert 'meetsSpecification' not in goal['rendered']

    # Keep `unveil` in flight while editing a later tactic. The command wrapper
    # observes the new theorem's snapshot promise, so releasing the gate does
    # not depend on guessing how long deferred preparation or scheduling takes.
    release = work / 'release-unveil'
    blocked_unveil = '''  IO.FS.withFile LOG .append fun h => h.putStrLn "unveil-start"
  try
    while !(← System.FilePath.pathExists RELEASE) do
      Lean.Core.checkInterrupted
      IO.sleep 10
    Lean.Core.checkInterrupted
    Veil.elabVeilTactics stx
    IO.FS.withFile LOG .append fun h => h.putStrLn "unveil-finish"
  catch ex =>
    IO.FS.withFile LOG .append fun h => h.putStrLn "unveil-cancelled"
    throw ex

open Lean Elab Command in
@[command_elab Veil.proveVeilInvariantGoal, incremental]
public meta def observeInvariantGoal : CommandElab := fun stx => do
  if let some snap := (← read).snap? then
    let _ ← IO.asTask (prio := .dedicated) do
      if (← IO.wait snap.new.result?).isSome then
        IO.FS.withFile LOG .append fun h => h.putStrLn "theorem-snapshot"
    pure ()
  Veil.elabProveVeilInvariantGoal stx
'''.replace('LOG', json.dumps(str(log))).replace('RELEASE', json.dumps(str(release)))
    source = initial_source.replace(
        '  IO.FS.withFile ' + json.dumps(str(log)) + ' .append fun h => h.putStrLn "unveil"\n'
        '  Veil.elabVeilTactics stx\n', blocked_unveil)
    version += 2
    send('textDocument/didChange', {'textDocument': {'uri': uri, 'version': version},
                                   'contentChanges': [{'text': source}]})
    wait_for_execution('unveil-start')
    wait_for_execution('theorem-snapshot')
    assert 'unveil-finish' not in log.read_text().splitlines()
    source = source.replace('  grind', '  skip\n  grind')
    version += 1
    send('textDocument/didChange', {'textDocument': {'uri': uri, 'version': version},
                                   'contentChanges': [{'text': source}]})
    wait_for_execution('theorem-snapshot', count=2)
    release.write_text('continue')
    check(version, 'edit while unveil is running')
    executions = log.read_text().splitlines()
    assert executions.count('unveil-start') == 1, executions
    assert executions.count('unveil-finish') == 1, executions
    assert 'unveil-cancelled' not in executions, executions

    print('PASS; evidence:', work, flush=True)
finally:
    proc.terminate()
    proc.wait(timeout=15)
    err.close()
