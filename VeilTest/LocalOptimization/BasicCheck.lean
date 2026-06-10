import Veil

/-! ## Test: Existence of Local Optimization Theorems

Checks that the local optimization infrastructure generates the expected theorems. -/

set_option linter.unusedVariables false

veil module LocalOptBasicCheck

type node

relation r : node → node → Bool
individual x : node

#gen_state

after_init {
  r N M := false
  x := *
}

action act (n m : node) {
  require r n m
  r n m := false
  x := n
}

transition tr_act (n : node) {
  (∀ M, r' n M = false) ∧ x' = n
}

invariant [inv] x = x

#gen_spec

-- wp_local_eq should exist for the initializer and the action (not for transition)
#check @initializer.ext.wp_local_eq
#check @act.ext.wp_local_eq

#check _transitionWeakeningLemma

-- tr_abstract should exist for the initializer, the action, and the transition
#check @initializer.ext.tr_abstract
#check @act.ext.tr_abstract
#check @tr_act.ext.tr_abstract

-- core_simplified_eq should exist for the invariant
#check Assumptions.core_simplified_eq
#check Invariants.core_simplified_eq

-- local helper theorem for the WP tactic should exist
#check __veil_meetsSpecificationIfSuccessfulAssuming_local

end LocalOptBasicCheck
