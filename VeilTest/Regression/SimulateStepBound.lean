import Veil

/-!
# `#simulate` respects the per-trace step budget

Exactly one action is enabled in each reachable state, so the random walk is
forced and the result does not depend on the seed: the violation needs two steps,
so `maxSteps := 1` can never reach it and `maxSteps := 2` always does.

The `maxSteps := 1` case also pins down the trace loop: all `numTraces` traces are
run and `tracesRun` is reported as the configured budget.
-/

veil module SimulateStepBound

individual a : Bool
individual b : Bool

#gen_state

after_init {
  a := false
  b := false
}

action step_a {
  require !a
  a := true
}

action step_b {
  require a
  b := true
}

invariant [safe] ¬ b

#gen_spec

/--
info: ✅ No violation in 4 traces
Trace depths: 1x4
Seed: 1
-/
#guard_msgs in
#simulate interpreted {} {} (seed := 1) (numTraces := 4) (maxSteps := 1)

/--
error: ❌ Violation: safety_failure (violates: safe)
  State 0 (via init):
    a = false
    b = false
  State 1 (via step_a):
    a = true
    b = false
  State 2 (via step_b):
    a = true
    b = true
Seed: 1
-/
#guard_msgs in
#simulate interpreted {} {} (seed := 1) (numTraces := 4) (maxSteps := 2)

end SimulateStepBound
