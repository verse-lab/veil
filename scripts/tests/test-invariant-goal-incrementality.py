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
from proof_reuse import (ProofDocument, check_edit_while_running, check_multi_module_reuse,
                         defer, main, replace_once)

SOURCE = '''module
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
'''


def run_single_module(server, deferred):
    doc = ProofDocument(server, 'VeilTest/Regression/ProveInvariantGoal.lean')
    initial = doc.logged(SOURCE)
    if deferred:
        initial = defer(initial, 'IncrementalInvariantGoal')
    assert doc.change(initial, 'open') == ['unveil', 'prefix'], doc.executions()
    lines = initial.splitlines()
    skip = lines.index('  skip')
    for line, character in [(skip, 2), (skip - 2, len(lines[skip - 2]))]:
        goal = doc.goal(line, character)
        assert 'FieldRepresentation' not in goal and 'meetsSpecification' not in goal, goal
    for label, replacements, expected in [
        ('longer proof', [('  grind', '  skip\n  grind')], []),
        ('shorter proof', [('  skip\n  grind', '  grind')], []),
        ('different proof prefix', [('h.putStrLn "prefix"', 'h.putStrLn "prefix2"')], ['prefix2']),
        ('different invariant', [('step bounded using wp', 'step weaker using wp')], ['unveil', 'prefix2']),
        ('different action', [('step weaker using wp', 'more weaker using wp')], ['unveil', 'prefix2']),
        ('different VC style', [('more weaker using wp', 'more weaker using tr')], ['unveil', 'prefix2']),
        ('upstream action edit', [('require x < 9', 'require x < 8')], ['unveil', 'prefix2']),
    ]:
        executions = doc.edit(label, *replacements)
        assert executions == expected, (label, executions)

    # An empty proof should report the simplified obligation, including at `by`.
    header = next(line for line in doc.source.splitlines() if line.startswith('prove_veil_invariant_goal'))
    source = doc.source[:doc.source.index(header)] + header + '\n\nend IncrementalInvariantGoal\n'

    def unsolved_goal(diagnostics):
        problems = [d for d in diagnostics if d.get('severity') in (1, 2)]
        assert len(problems) == 1 and problems[0]['message'].startswith('unsolved goals'), problems
        assert 'FieldRepresentation' not in problems[0]['message'], problems
    doc.change(source, 'empty proof', check=unsolved_goal)
    goal = doc.goal(source.splitlines().index(header), len(header))
    assert 'FieldRepresentation' not in goal and 'meetsSpecification' not in goal, goal

    # Keep `unveil` in flight while editing a later tactic.
    unveil = doc.logged('  IO.FS.withFile LOG .append fun h => h.putStrLn "unveil"\n'
                        '  Veil.elabVeilTactics stx\n')
    gated = doc.gate('unveil', body='Veil.elabVeilTactics stx')
    observer = doc.observer('Veil.proveVeilInvariantGoal', 'Veil.elabProveVeilInvariantGoal')
    check_edit_while_running(doc, replace_once(initial, unveil, gated + '\n' + observer),
                             'unveil', ('  grind', '  skip\n  grind'))


def run_multi_module(server, deferred):
    doc = ProofDocument(server, 'VeilTest/Regression/ProveInvariantGoalMultiModule.lean')
    instrumentation = doc.logged('''
open Lean Elab Tactic in
@[tactic Veil.veil_unveil] public meta def countedUnveil : Tactic := fun stx => do
  let ns ← getCurrNamespace
  IO.FS.withFile LOG .append fun h => h.putStrLn s!"unveil:{ns}"
  Veil.elabVeilTactics stx
''')
    source = replace_once(doc.path.read_text(), 'public import Veil\n', 'public import Veil\n' + instrumentation)
    if deferred:
        source = defer(source, 'ProveInvariantGoalFirst')

    def check_goals():
        lines = doc.source.splitlines()
        headers = [i for i, line in enumerate(lines) if line.startswith('prove_veil_invariant_goal ')]
        assert len(headers) == 2, headers
        for line, bound in zip(headers, (10, 20)):
            goal = doc.goal(line, len(lines[line]))
            assert f'hinv : st.x ≤ {bound}' in goal, goal
            assert 'FieldRepresentation' not in goal, goal

    # The start of each proof is its `unveil`.
    check_multi_module_reuse(doc, source, 'grind', check_goals, start={
        'first': 'unveil:ProveInvariantGoalFirst', 'second': 'unveil:ProveInvariantGoalSecond'})


if __name__ == '__main__':
    main(__doc__, 'invariant-goal', run_single_module, run_multi_module)
