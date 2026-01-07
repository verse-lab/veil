import Veil

veil module ExecuteTransition

type address

relation initial_msg (originator : address) (r : address) (v : address)
relation is_byz : address → Bool

#gen_state

after_init {
  initial_msg O R V := false
  is_byz := *
}

#guard_msgs in
transition byz {
  (∀ (src : address) (r : address) (v : address),
    (¬ is_byz src ∧ (initial_msg src r v ↔ initial_msg' src r v)) ∨
    (is_byz src ∧ (initial_msg src r v → initial_msg' src r v)))
}

#gen_spec

#model_check interpreted { address := Fin 2 }

end ExecuteTransition
