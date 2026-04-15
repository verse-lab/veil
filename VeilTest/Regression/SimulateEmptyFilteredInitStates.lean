import Veil

veil module SimulateEmptyFilteredInitStates

after_init {
  pure ()
}

invariant true

state_constraint [no_initial_states] False

/--
warning: you have not defined any actions for this specification; did you forget?
-/
#guard_msgs in
#gen_spec

/--
info: ✅ No violation in 0 traces
Seed: 1
-/
#guard_msgs in
#simulate interpreted {} {} (seed := 1) (maxTraces := 5) (maxSteps := 1)

end SimulateEmptyFilteredInitStates
