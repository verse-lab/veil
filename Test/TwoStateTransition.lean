import Veil.DSL

veil module TwoStateTransitionTest

type address
variable (is_byz : address → Prop)

relation initial_msg (originator : address) (dst : address) (r : address) (v : address)

#gen_state

after_init {
  initial_msg O D R V := False
}

#guard_msgs in
internal transition byz = {
  (∀ (src dst : address) (r : address) (v : address),
    (¬ is_byz src ∧ (initial_msg src dst r v ↔ initial_msg' src dst r v)) ∨
    (is_byz src ∧ (initial_msg src dst r v → initial_msg' src dst r v)))
}

#guard_msgs in
internal transition withargs (r : address) = {
  (∀ (src dst : address) (v : address),
    (¬ is_byz src ∧ (initial_msg src dst r v ↔ initial_msg' src dst r v)) ∨
    (is_byz src ∧ (initial_msg src dst r v → initial_msg' src dst r v)))
}

invariant True

#gen_spec

/--
info: Initialization must establish the invariant:
  inv_0 ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  byz
    termination ... ✅
    inv_0 ... ✅
  withargs
    termination ... ✅
    inv_0 ... ✅
-/
#guard_msgs in
#check_invariants

end TwoStateTransitionTest
