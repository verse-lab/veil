module

public import VeilTest.GenReachableInvariants

public section

set_option veil.smt.trust false
set_option veil.printCounterexamples false
set_option linter.unusedVariables false

veil module ReachableParameters

type node
param n : Nat
param selected : node
instantiate tot : TotalOrder node
open TotalOrder

relation marked : node → Bool
individual index : Nat
#gen_state
after_init {
  marked N := true
  index := n
}
-- The action parameter must not shadow the generated induction's state binder.
action keep (s : node) {
  require le s selected
  marked s := true
  index := n
}
invariant [all_marked] marked N = true
invariant [selected_index] index = n
#gen_spec
#gen_theorems

run_cmd checkReachableTheorems `ReachableParameters #[`Invariants.is_inv, `all_marked.is_inv, `selected_index.is_inv, `Safeties.is_inv]

end ReachableParameters

veil module ReachableExceptionalAction

relation marked : Bool
#gen_state
after_init { marked := true }
action failing { assert False }
invariant [all_marked] marked
/-- error: This assertion might fail when called from failing -/
#guard_msgs in
#gen_spec
#gen_theorems

-- The relational system describes successful transitions. Exception freedom
-- is a separate property and is not needed for invariance on this system.
run_cmd checkReachableTheorems `ReachableExceptionalAction #[`Invariants.is_inv, `all_marked.is_inv, `Safeties.is_inv]
run_cmd checkReachableTheorems `ReachableExceptionalAction #[`failing_doesNotThrow] false

end ReachableExceptionalAction
