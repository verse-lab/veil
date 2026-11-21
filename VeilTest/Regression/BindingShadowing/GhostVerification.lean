module

public import Veil

/-! Regression for #180. A step may move strictly above zero but below the theory field `r1`. -/

veil module GhostParameterVerification

type round
instantiate tot : TotalOrderWithZero round
open TotalOrderWithZero

immutable individual r1 : round
individual cur : round

ghost relation lt (r1 r2 : round) := le r1 r2 ∧ r1 ≠ r2

after_init { cur := zero }
action step (next : round) {
  require lt cur next
  cur := next
}

assumption [r1_pos] r1 ≠ zero
invariant [above_r1] cur = zero ∨ le r1 cur

#gen_spec

set_option veil.printCounterexamples false

/--
error: Initialization must establish the invariant:
  doesNotThrow ... ✅
  above_r1 ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  step
    doesNotThrow ... ✅
    above_r1 ... ❌
-/
#guard_msgs (drop warning, all) in
#check_invariants

/-- info: ✅ Satisfying trace found -/
#guard_msgs (substring := true) in
sat trace {
  step
  assert (cur = r1)
}

end GhostParameterVerification
