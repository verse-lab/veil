import Veil

veil module SimulateEmptySpec

after_init {
  pure ()
}

invariant true

/--
warning: you have not defined any actions for this specification; did you forget?
-/
#guard_msgs in
#gen_spec

/--
info: ✅ No violation in 1 traces
Seed: 1
-/
#guard_msgs in
#simulate interpreted { } {} (seed := 1) (maxTraces := 1) (maxSteps := 1)

end SimulateEmptySpec
