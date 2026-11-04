#!/usr/bin/env python3
"""LSP regression for prove_veil_invariant_goal.

Run after `lake build VeilTest.Regression.ProveInvariantGoal`:
  python3 scripts/tests/test-invariant-goal-incrementality.py [--deferred]

For tactic reuse across two modules, also build
`VeilTest.Regression.ProveInvariantGoalMultiModule`, then run:
  python3 scripts/tests/test-invariant-goal-incrementality.py --multi-module [--deferred]

For proof insertion/deletion and multi-module manager regressions, run:
  python3 scripts/tests/test-vc-manager-incrementality.py --compact

Edits a virtual document only. Counts actual tactic executions in a temporary
file, so replayed diagnostics cannot be mistaken for proof reuse. Evidence is
retained in the printed temporary directory.
"""
import argparse
from collections import Counter
import json
import time

from lean_lsp import ROOT as root, LeanServer

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--deferred', action='store_true', help='defer VC generation until the proof command')
parser.add_argument('--multi-module', action='store_true', help='check tactic reuse across two Veil modules')
args = parser.parse_args()
deferred = args.deferred
label = 'invariant-goal-multi' if args.multi_module else 'invariant-goal'
server = LeanServer(label + ('-deferred' if deferred else ''))
work = server.work
log = work / 'executions.txt'
log.write_text('')
send = server.send

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
    if incomplete:
        diagnostics = server.diagnostics(uri, version, label)
        problems = [d for d in diagnostics if d.get('severity') in (1, 2)]
        assert len(problems) == 1 and problems[0]['message'].startswith('unsolved goals'), problems
        assert 'FieldRepresentation' not in problems[0]['message'], problems
    else:
        server.check(uri, version, label)
    print(label, 'executions:', log.read_text().splitlines(), flush=True)

def wait_for_execution(marker, count=1):
    deadline = time.monotonic() + 30
    while time.monotonic() < deadline:
        if log.read_text().splitlines().count(marker) >= count:
            return
        time.sleep(0.01)
    raise AssertionError(f'timed out waiting for {marker}: {log.read_text()}')

def run_multi_module():
    fixture = root / 'VeilTest/Regression/ProveInvariantGoalMultiModule.lean'
    uri = fixture.as_uri()
    instrumentation = '''
open Lean Elab Tactic in
@[tactic Veil.veil_unveil] public meta def countedUnveil : Tactic := fun stx => do
  let ns ← getCurrNamespace
  IO.FS.withFile LOG .append fun h => h.putStrLn s!"unveil:{ns}"
  Veil.elabVeilTactics stx
'''.replace('LOG', json.dumps(str(log)))
    source = fixture.read_text().replace('public import Veil\n', 'public import Veil\n' + instrumentation)
    if deferred:
        source = source.replace('veil module ProveInvariantGoalFirst',
                                'set_option veil.deferVCGeneration true\nveil module ProveInvariantGoalFirst')
    for which in ('first', 'second'):
        marker = f'  grind -- {which} proof'
        assert source.count(marker) == 1, f'missing unique {which} proof'
        prefix = f'  run_tac IO.FS.withFile {json.dumps(str(log))} .append fun h => h.putStrLn "prefix:{which}"\n'
        source = source.replace(marker, prefix + marker)
    first_unveil = 'unveil:ProveInvariantGoalFirst'
    second_unveil = 'unveil:ProveInvariantGoalSecond'

    def check_goals():
        lines = source.splitlines()
        headers = [i for i, line in enumerate(lines) if line.startswith('prove_veil_invariant_goal ')]
        assert len(headers) == 2, headers
        for line, bound in zip(headers, (10, 20)):
            goal = send('$/lean/plainGoal', {'textDocument': {'uri': uri},
                        'position': {'line': line, 'character': len(lines[line])}}, True)
            assert goal and f'hinv : st.x ≤ {bound}' in goal['rendered'], goal
            assert 'FieldRepresentation' not in goal['rendered'], goal

    server.open(uri, source)
    server.check(uri, 1, 'fresh two-module compact proofs')
    check_goals()
    assert Counter(log.read_text().splitlines()) == Counter({
        first_unveil: 1, 'prefix:first': 1, second_unveil: 1, 'prefix:second': 1,
    }), log.read_text()
    version = 1

    def edit(old, new, label):
        nonlocal source, version
        assert source.count(old) == 1, f'{label}: missing unique edit target'
        before = log.read_text().splitlines()
        source = source.replace(old, new, 1)
        version += 1
        server.change(uri, version, source)
        server.check(uri, version, label)
        check_goals()
        delta = Counter(log.read_text().splitlines()[len(before):])
        print(label, 'new executions:', dict(delta), flush=True)
        return delta

    delta = edit('  grind -- second proof', '  skip\n  grind -- second proof',
                 'edit second proof suffix')
    assert not delta, delta
    delta = edit('"prefix:second"', '"prefix:second2"', 'edit second proof prefix')
    assert delta == Counter({'prefix:second2': 1}), delta
    delta = edit('  grind -- first proof', '  skip\n  grind -- first proof',
                 'edit first proof after second module')
    # Later commands may legitimately re-elaborate when an earlier proof changes.
    # The first proof must reuse its own unchanged simplification and prefix.
    assert delta[first_unveil] == 0 and delta['prefix:first'] == 0, delta
    delta = edit('  skip\n  grind -- second proof', '  grind -- second proof',
                 'edit second proof after first-module edit')
    assert not delta, delta
    delta = edit('"prefix:first"', '"prefix:first2"', 'edit first proof prefix')
    assert delta[first_unveil] == 0 and delta['prefix:first2'] == 1, delta
    delta = edit('  grind -- second proof', '  skip\n  grind -- second proof',
                 'reuse second proof after first prefix change')
    assert not delta, delta
    print('PASS: multi-module tactic reuse; evidence:', work, flush=True)

try:
    send('initialize', {'processId': None, 'rootUri': root.as_uri(), 'capabilities': {}}, True)
    send('initialized', {})
    if args.multi_module:
        run_multi_module()
        raise SystemExit(0)
    server.open(uri, source)
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
        server.change(uri, version, source)
        check(version, label)
        after = log.read_text()
        assert after[len(before):].splitlines() == expected, (label, before, after)
    # An empty proof should report the simplified obligation, including at `by`.
    header = next(line for line in source.splitlines() if line.startswith('prove_veil_invariant_goal'))
    source = source[:source.index(header)] + header + '\n\nend IncrementalInvariantGoal\n'
    server.change(uri, version + 1, source)
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
    server.change(uri, version, source)
    wait_for_execution('unveil-start')
    wait_for_execution('theorem-snapshot')
    assert 'unveil-finish' not in log.read_text().splitlines()
    source = source.replace('  grind', '  skip\n  grind')
    version += 1
    server.change(uri, version, source)
    wait_for_execution('theorem-snapshot', count=2)
    release.write_text('continue')
    check(version, 'edit while unveil is running')
    executions = log.read_text().splitlines()
    assert executions.count('unveil-start') == 1, executions
    assert executions.count('unveil-finish') == 1, executions
    assert 'unveil-cancelled' not in executions, executions

    print('PASS; evidence:', work, flush=True)
finally:
    server.close()
