module

public import Veil

-- Exercise the actual failure suggestion, without relying on solver timeouts.
veil module ProveInvariantGoalSuggestion
individual x : Nat
after_init { x := 0 }
action step { require x < 10; x := x + 1 }
invariant [bounded] x ≤ 10

-- No custom solver is installed, so the arithmetic invariant VCs fail.
set_option veil.solver "custom"
#gen_spec

-- Ignore the expected solver errors and check the complete insertion suggestion.
/--
info: Insert theorem stubs for undischarged verification conditions:

  [apply] #check_invariants
  ⏎
  prove_veil_invariant_goal initializer bounded using wp by
    sorry
  ⏎
  prove_veil_invariant_goal step bounded using wp by
    sorry
-/
#guard_msgs (drop error, all, whitespace := exact) in
#check_invariants

end ProveInvariantGoalSuggestion
