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

# The properties are declared before `#gen_spec`, so that under deferred VC
# generation `prove_temporal_by` is the command that prepares verification.
SOURCE = '''module
public import Veil
public import Veil.Liveness

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
  tstart hInit hNext hInv
  tclear hInit hNext hInv
  tdsimp only [selfImplied]
  tsplit_ands
  run_tac IO.FS.withFile LOG .append fun h => h.putStrLn "split"
  all_goals (tintro h; tassumption)

end IncrementalTemporal
'''


def rename(old, new):
    return [(f'prove_temporal_by [{old}]', f'prove_temporal_by [{new}]'),
            (f'tdsimp only [{old}]', f'tdsimp only [{new}]')]


def run_single_module(server, deferred):
    doc = ProofDocument(server, 'VeilTest/Regression/TemporalBasic.lean')
    initial = doc.logged(SOURCE)
    if deferred:
        initial = defer(initial, 'IncrementalTemporal')
    assert doc.change(initial, 'open') == ['prefix', 'split'], doc.executions()
    # The whole obligation at the first tactic, and both conjuncts after `tsplit_ands`
    lines = initial.splitlines()
    goal = doc.goal(lines.index('prove_temporal_by [selfImplied]') + 1, 2)
    assert '|-tl-' in goal and 'selfImplied' in goal, goal
    goal = doc.goal(next(i for i, line in enumerate(lines) if '"split"' in line), 2)
    assert 'x ≤ 10' in goal and 'x < 11' in goal, goal
    for label, replacements, expected in [
        ('longer proof', [('  all_goals', '  skip\n  all_goals')], []),
        ('shorter proof', [('  skip\n  all_goals', '  all_goals')], []),
        ('different proof after tsplit_ands', [('"split"', '"split2"')], ['split2']),
        ('different proof prefix', [('"prefix"', '"prefix2"')], ['prefix2', 'split2']),
        ('different property', rename('selfImplied', 'otherSelfImplied'), ['prefix2', 'split2']),
        ('upstream action edit', [('require x < 9', 'require x < 8')], ['prefix2', 'split2']),
    ]:
        executions = doc.edit(label, *replacements)
        assert executions == expected, (label, executions)

    # Keep the first tactic in flight while editing a later one.
    gated = '  run_tac do\n' + doc.gate('prefix', indent='    ')
    observer = doc.observer('Veil.proveTemporalBy', 'Veil.elabProveTemporalBy')
    source = replace_once(initial, doc.counted('prefix'), gated)
    source = replace_once(source, 'open Lentil\n', observer + '\nopen Lentil\n')
    executions = check_edit_while_running(doc, source, 'prefix', ('  all_goals', '  skip\n  all_goals'))
    # The tactics between the gate and the edit are reused as well.
    assert executions.count('split') == 1, executions


def run_multi_module(server, deferred):
    doc = ProofDocument(server, 'VeilTest/Regression/ProveTemporalMultiModule.lean')
    source = doc.path.read_text()
    if deferred:
        source = defer(source, 'ProveTemporalFirst')
    # Count the first tactic of each proof as its start.
    header = 'prove_temporal_by [stable]\n'
    for which in ('first', 'second'):
        start = source.rindex(header, 0, source.index(f'  tassumption -- {which} proof')) + len(header)
        source = source[:start] + doc.counted(f'start:{which}') + source[start:]

    def check_goals():
        lines = doc.source.splitlines()
        proofs = [i for i, line in enumerate(lines) if line.endswith(' proof')]
        assert len(proofs) == 2, proofs
        for line, bound in zip(proofs, (10, 20)):
            goal = doc.goal(line, 2)
            assert f'x ≤ {bound}' in goal and '|-tl-' in goal, goal

    check_multi_module_reuse(doc, source, 'tassumption', check_goals,
                             start={'first': 'start:first', 'second': 'start:second'})


if __name__ == '__main__':
    main(__doc__, 'temporal-proof', run_single_module, run_multi_module)
