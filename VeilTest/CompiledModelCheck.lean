module

public import Veil.Core

veil module CompiledStateConstraint

type node
relation active : node → Bool

#gen_state

after_init { active N := false }

action activate (n : node) { active n := true }
action deactivate (n : node) { active n := false }

invariant true
state_constraint [at_most_one_active] active M ∧ active N → M = N

#gen_spec

-- The compiled check must see definitions elaborated after #gen_spec.
abbrev nodeCount : Nat := 3

/-- info: ✅ No violation (explored 4 states) -/
#guard_msgs in
#model_check compiled { node := Fin nodeCount } {} (sequential := true)

/-- info: ✅ No violation (explored 3 states) -/
#guard_msgs in
#model_check compiled { node := Fin 2 } {}
  (parallelCfg := some { numSubTasks := 2, thresholdToParallel := 1, numSubSteps := 2 })

/-- info: ✅ No violation (explored 4 states) -/
#guard_msgs in
#model_check { node := Fin nodeCount } {} (sequential := true)

end CompiledStateConstraint

veil module CompiledAssertionFailure

individual active : Bool

#gen_state

after_init { active := false }

action fail {
  assert false
}

invariant true

#gen_spec

/--
error: ❌ Violation: assertion_failure
  State 0 (via init):
    active = false
  State 1 (via fail):
    active = false
-/
#guard_msgs in
#model_check compiled {} {} (sequential := true)

end CompiledAssertionFailure

-- Generated entry points must not reserve `main` in the user's environment.
def main : IO Unit := pure ()
