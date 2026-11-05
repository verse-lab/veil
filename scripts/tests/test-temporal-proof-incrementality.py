#!/usr/bin/env python3
"""LSP regression for prove_temporal_by.

Run after `lake build VeilTest.Regression.TemporalBasic`:
  python3 scripts/tests/test-temporal-proof-incrementality.py [--deferred]

For tactic reuse across two modules, also build
`VeilTest.Regression.ProveTemporalMultiModule`, then run:
  python3 scripts/tests/test-temporal-proof-incrementality.py --multi-module [--deferred]

Edits a virtual document only. Counts actual tactic executions in a temporary
file, so replayed diagnostics cannot be mistaken for proof reuse. Evidence is
retained in the printed temporary directory.
"""
from proof_reuse import (ProofDocument, check_edit_while_running, check_multi_module_reuse,
                         defer, main, replace_once)

# `countedStart` logs each run of the prelude's `tstart`, then leaves it to Lentil.
# The properties are declared before `#gen_spec`, so that under deferred VC
# generation `prove_temporal_by` is the command that prepares verification.
SOURCE = '''module
public import Veil
public import Veil.Liveness

open Lean Elab Tactic in
@[tactic Lentil.ProofMode.tlStartTac] public meta def countedStart : Tactic := fun _ => do
  IO.FS.withFile LOG .append fun h => h.putStrLn "prelude"
  throwUnsupportedSyntax

open Lentil

veil module IncrementalTemporal
individual x : Nat
after_init { x := 0 }
action step { require x < 10; x := x + 1 }
action more { require x < 9; x := x + 2 }
invariant [bounded] x ≤ 10
temporal (only := verify) [selfImplied] (⌜ x ≤ 10 ⌝ → ⌜ x ≤ 10 ⌝) ∧ (⌜ x < 11 ⌝ → ⌜ x < 11 ⌝)
temporal (only := verify) [otherSelfImplied] (⌜ x ≤ 11 ⌝ → ⌜ x ≤ 11 ⌝) ∧ (⌜ x < 12 ⌝ → ⌜ x < 12 ⌝)
#gen_spec

prove_temporal_by [selfImplied]
  run_tac IO.FS.withFile LOG .append fun h => h.putStrLn "prefix"
  tclear hInit hNext hInv
  tsplit_ands
  run_tac IO.FS.withFile LOG .append fun h => h.putStrLn "split"
  all_goals (tintro h; tassumption)

end IncrementalTemporal
'''


def run_single_module(server, deferred):
    doc = ProofDocument(server, 'VeilTest/Regression/TemporalBasic.lean')
    initial = doc.logged(SOURCE)
    if deferred:
        initial = defer(initial, 'IncrementalTemporal')
    assert doc.change(initial, 'open') == ['prelude', 'prefix', 'split'], doc.executions()
    # The goal after the prelude, at the end of the header and at the first tactic,
    # and both conjuncts after `tsplit_ands`
    lines = initial.splitlines()
    header = lines.index('prove_temporal_by [selfImplied]')
    for line, character in [(header, len(lines[header])), (header + 1, 2)]:
        goal = doc.goal(line, character)
        assert 'hInit' in goal and 'x ≤ 10' in goal and 'selfImplied' not in goal, goal
    goal = doc.goal(next(i for i, line in enumerate(lines) if '"split"' in line), 2)
    assert 'x ≤ 10' in goal and 'x < 11' in goal, goal
    for label, replacements, expected in [
        ('longer proof', [('  all_goals', '  skip\n  all_goals')], []),
        ('shorter proof', [('  skip\n  all_goals', '  all_goals')], []),
        ('different proof after tsplit_ands', [('"split"', '"split2"')], ['split2']),
        ('different proof prefix', [('"prefix"', '"prefix2"')], ['prefix2', 'split2']),
        ('different property', [('prove_temporal_by [selfImplied]', 'prove_temporal_by [otherSelfImplied]')],
         ['prelude', 'prefix2', 'split2']),
        ('upstream action edit', [('require x < 9', 'require x < 8')], ['prelude', 'prefix2', 'split2']),
    ]:
        executions = doc.edit(label, *replacements)
        assert executions == expected, (label, executions)

    # Keep the first tactic in flight while editing a later one.
    gated = '  run_tac do\n' + doc.gate('prefix', indent='    ')
    observer = doc.observer('Veil.proveTemporalBy', 'Veil.elabProveTemporalBy')
    source = replace_once(initial, doc.counted('prefix'), gated)
    source = replace_once(source, 'open Lentil\n', observer + '\nopen Lentil\n')
    executions = check_edit_while_running(doc, source, 'prefix', ('  all_goals', '  skip\n  all_goals'))
    # The prelude and the tactics between the gate and the edit are reused as well.
    assert executions.count('prelude') == 1 and executions.count('split') == 1, executions


def run_multi_module(server, deferred):
    doc = ProofDocument(server, 'VeilTest/Regression/ProveTemporalMultiModule.lean')
    instrumentation = doc.logged('''
open Lean Elab Tactic in
@[tactic Lentil.ProofMode.tlStartTac] public meta def countedStart : Tactic := fun _ => do
  let ns ← getCurrNamespace
  IO.FS.withFile LOG .append fun h => h.putStrLn s!"prelude:{ns}"
  throwUnsupportedSyntax
''')
    header = 'public import Veil.Liveness\n'
    source = replace_once(doc.path.read_text(), header, header + instrumentation)
    if deferred:
        source = defer(source, 'ProveTemporalFirst')

    def check_goals():
        lines = doc.source.splitlines()
        proofs = [i for i, line in enumerate(lines) if line.endswith(' proof')]
        assert len(proofs) == 2, proofs
        for line, bound in zip(proofs, (10, 20)):
            goal = doc.goal(line, 2)
            assert f'x ≤ {bound}' in goal and '|-tl-' in goal, goal

    # The start of each proof is its prelude, run in the namespace of `stable._proof`.
    check_multi_module_reuse(doc, source, 'tassumption', check_goals, start={
        'first': 'prelude:ProveTemporalFirst.stable', 'second': 'prelude:ProveTemporalSecond.stable'})


if __name__ == '__main__':
    main(__doc__, 'temporal-proof', run_single_module, run_multi_module)
