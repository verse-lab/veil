import Veil.DSL

namespace TwoStateTransitionTest
open Classical

type address
variable (is_byz : address → Prop)

relation initial_msg (originator : address) (dst : address) (r : address) (v : address)

#gen_state

#guard_msgs in
internal transition byz = fun st st' =>
  (∀ (src dst : address) (r : address) (v : address),
    (¬ is_byz src ∧ (st.initial_msg src dst r v ↔ st'.initial_msg src dst r v)) ∨
    (is_byz src ∧ (st.initial_msg src dst r v → st'.initial_msg src dst r v)))

#guard_msgs in
internal transition withargs (r : address) = fun st st' =>
  (∀ (src dst : address) (v : address),
    (¬ is_byz src ∧ (st.initial_msg src dst r v ↔ st'.initial_msg src dst r v)) ∨
    (is_byz src ∧ (st.initial_msg src dst r v → st'.initial_msg src dst r v)))

end TwoStateTransitionTest
