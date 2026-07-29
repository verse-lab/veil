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

/--
warning: you have not defined any invariants for this specification; did you forget?
-/
#guard_msgs in
#gen_spec

/--
warning: Explicit state model checking of transitions is SLOW!

The current implementation enumerates all possible states and filters those satisfying the transition relation. Your specification has 1 transition: byz

Consider encoding transitions as imperative actions where possible.
-/
#guard_msgs(error, warning) in
#model_check interpreted { address := Fin 2 } {} (parallelCfg := some { numSubTasks := 4 })

end ExecuteTransition
