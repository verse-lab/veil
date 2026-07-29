import Veil

set_option linter.unusedVariables false

veil module Ring

type node

instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

relation leader : node -> Bool
relation pending : node -> node -> Bool

#gen_state

after_init {
  leader N := false
  pending M N := false
}

action skip {
  pure ()
}

invariant False

set_option veil.printCounterexamples false

#gen_spec

/--
error: Initialization must establish the invariant:
  doesNotThrow ... ✅
  inv_0 ... ❌
The following set of actions must preserve the invariant and successfully terminate:
  skip
    doesNotThrow ... ✅
    inv_0 ... ✅
-/
#guard_msgs in
#check_invariants

end Ring
