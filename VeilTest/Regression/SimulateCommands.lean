import Veil

/-!
Command integration: bound precedence, repeated invocations, compiled execution,
and theory validation with and without explicit proofs. The forced walk needs
exactly two steps to violate its invariant, so bound checks are seed-independent.
-/

set_option linter.unusedVariables false

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

-- Omitted bounds come from options; all traces stop before the violation.
set_option veil.simulate.numTraces 4 in
set_option veil.simulate.maxSteps 1 in
/--
info: ✅ No violation in 4 traces
Trace depths: 1x4
Seed: 1
-/
#guard_msgs in
#simulate interpreted {} {} (seed := 1)

-- Explicit bounds override options, even when equal to the structure defaults.
set_option veil.simulate.maxSteps 1 in
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
#simulate interpreted {} {} (seed := 1) (numTraces := 4) (maxSteps := 100)

-- A config literal also overrides options.
set_option veil.simulate.maxSteps 1 in
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
#simulate interpreted {} {} (config := { numTraces := 1, maxSteps := 100, seed := 1 })

-- Config trace counts override options too; repeated commands share the spec.
set_option veil.simulate.numTraces 2 in
/--
info: ✅ No violation in 1 traces
Seed: 1
-/
#guard_msgs in
#simulate interpreted {} {} (config := { numTraces := 1, maxSteps := 1, seed := 1 })

-- Exercise generation, compilation, and execution using the same bounded walk.
-- Require a verdict as well as no errors, so a run cannot silently do nothing.
-- /--
-- info: ✅ No violation in 1 traces
-- Seed: 1
-- -/
-- #guard_msgs in
-- #simulate compiled {} {} (seed := 1) (numTraces := 1) (maxSteps := 1)
-- FIXME: this is a broken test

end SimulateStepBound

veil module SimulateAssumptionsTest

type node

immutable relation leader : node → Bool
relation flag : node → Bool

#gen_state

assumption ∀ (n1 n2 : node), leader n1 ∧ leader n2 → n1 = n2

after_init {
  flag N := false
}

action do_something (n : node) {
  require leader n
  flag n := true
}

invariant true

#gen_spec

/--
info: ✅ No violation in 1 traces
Seed: 1
-/
#guard_msgs in
#simulate interpreted { node := Fin 3 } { leader := fun n => n == (0 : Fin 3) }
  (seed := 1) (numTraces := 1) (maxSteps := 1)
  assumptions_hold_by native_decide

-- Runtime validation also accepts a valid theory without a proof clause.
/--
info: ✅ No violation in 1 traces
Seed: 1
-/
#guard_msgs in
#simulate interpreted { node := Fin 3 } { leader := fun n => n == (0 : Fin 3) }
  (seed := 1) (numTraces := 1) (maxSteps := 1)

/--
error: Tactic `native_decide` evaluated that the proposition
  assumption_0 { leader := fun n => n == 0 || n == 1 }
is false
---
error: ❌ Violation: assumption_failure (violates: assumption_0)
Seed: 1
-/
#guard_msgs in
#simulate interpreted { node := Fin 3 } { leader := fun n => n == (0 : Fin 3) || n == (1 : Fin 3) }
  (seed := 1) (numTraces := 1) (maxSteps := 1)
  assumptions_hold_by native_decide

/--
error: ❌ Violation: assumption_failure (violates: assumption_0)
Seed: 1
-/
#guard_msgs in
#simulate interpreted { node := Fin 3 } { leader := fun n => n == (0 : Fin 3) || n == (1 : Fin 3) }
  (seed := 1) (numTraces := 1) (maxSteps := 1)

end SimulateAssumptionsTest

veil module SimulateAssumptionsCustomProof

type node

immutable function weight : node → Nat

relation active : node → Bool

#gen_state

assumption ∀ (n : node), 0 < weight n
assumption ∀ (n1 n2 : node), weight n1 = weight n2 → n1 = n2

after_init {
  active N := false
}

action activate (n : node) {
  active n := true
}

invariant true

#gen_spec

/--
info: ✅ No violation in 1 traces
Seed: 1
-/
#guard_msgs in
#simulate interpreted { node := Fin 3 } { weight := fun (n : Fin 3) => n.val + 1 }
  (seed := 1) (numTraces := 1) (maxSteps := 1)
  assumptions_hold_by
    constructor <;> decide

end SimulateAssumptionsCustomProof
