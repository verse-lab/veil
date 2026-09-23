module

public import Veil

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
#gen_theorems

run_cmd do
  let env ← Lean.getEnv
  for name in #[`Ring.initializer_inv_0, `Ring.initializer_inv_0_tr,
      `Ring.Invariants.is_inv, `Ring.inv_0.is_inv, `Ring.Safeties.is_inv] do
    if env.contains name then
      throwError "failed verification condition was published: {name}"
  for name in #[`Ring.initializer_doesNotThrow, `Ring.skip_inv_0, `Ring.skip_inv_0_tr] do
    unless env.contains name do
      throwError "successful verification condition was not published: {name}"

end Ring
