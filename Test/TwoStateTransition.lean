import Veil.DSL

veil module TwoStateTransitionTest


type address
variable (is_byz : address → Prop)

relation initial_msg (originator : address) (dst : address) (r : address) (v : address)

#gen_state

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

end TwoStateTransitionTest
