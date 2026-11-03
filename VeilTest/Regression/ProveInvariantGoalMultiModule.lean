module

public import Veil

/-! Both modules deliberately reuse the action and invariant names, with different
obligations. The LSP test instruments the marked proofs to count tactic execution:
  python3 scripts/tests/test-invariant-goal-incrementality.py --multi-module
Add `--deferred` to also exercise deferred VC generation in both modules. -/

veil module ProveInvariantGoalFirst

individual x : Nat
after_init { x := 0 }
action step { require x < 10; x := x + 1 }
invariant [bounded] x ≤ 10
#gen_spec

prove_veil_invariant_goal step bounded using wp by
  grind -- first proof

end ProveInvariantGoalFirst

veil module ProveInvariantGoalSecond

individual x : Nat
after_init { x := 0 }
action step { require x < 19; x := x + 2 }
invariant [bounded] x ≤ 20
#gen_spec

prove_veil_invariant_goal step bounded using wp by
  grind -- second proof

end ProveInvariantGoalSecond

-- Both generated theorems remain available after switching modules.
example := @ProveInvariantGoalFirst.step_bounded
example := @ProveInvariantGoalSecond.step_bounded
