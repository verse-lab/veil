module

public import Veil

/-! Command integration: all execution modes, repeated calls, quantifiers, theory
validation, state constraints, and both state and edge atoms. -/

veil module LivenessWorkflow
type node
immutable relation leader : node → Bool
relation active : node → Bool

assumption [hasLeader] ∃ n, leader n
after_init { active N := false }
action activate (n : node) { active n := true }
action idle { active N := active N }

temporal [alwaysTrue] □ ⊤
temporal (only := check) [enabled] □ E(activate)
temporal (only := check) [step] □ (T(activate) ∨ T(idle))
temporal (only := check) [fairProgress] (□ ◇ T(activate)) → ◇ ⌜ ∃ n, active n ⌝

invariant true
#gen_spec

/-- info: ✅ No liveness violation (checked 4 properties, explored 15 product states) -/
#guard_msgs in
#liveness_check interpreted { node := Fin 2 } { leader := fun _ => true }
  assumptions_hold_by native_decide
/-- info: ✅ No liveness violation (checked 4 properties, explored 15 product states) -/
#guard_msgs in
#liveness_check compiled { node := Fin 2 } { leader := fun _ => true }
/-- info: ✅ No liveness violation (checked 4 properties, explored 15 product states) -/
#guard_msgs in
#liveness_check { node := Fin 2 } { leader := fun _ => true }

/-- error: ❌ Violation: assumption_failure (violates: hasLeader) -/
#guard_msgs in
#liveness_check interpreted { node := Fin 2 } { leader := fun _ => false }
/-- error: ❌ Violation: assumption_failure (violates: hasLeader) -/
#guard_msgs in
#liveness_check compiled { node := Fin 2 } { leader := fun _ => false }
end LivenessWorkflow

veil module LivenessCounterexample
individual flag : Bool
after_init { flag := false }
action idle { flag := flag }
temporal [trivial] □ ⊤
temporal [eventuallyFlag] ◇ ⌜ flag ⌝
invariant true
#gen_spec

-- Omitted theory and a second property failing after the first one passed.
/--
error: ❌ Violation: liveness_failure (violates: eventuallyFlag)
  Stem:
    State 0:
      flag = false
  Loop (repeats):
    State 0:
      flag = false
-/
#guard_msgs in
#liveness_check interpreted {}
/--
error: ❌ Violation: liveness_failure (violates: eventuallyFlag)
  Stem:
    State 0:
      flag = false
  Loop (repeats):
    State 0:
      flag = false
-/
#guard_msgs in
#liveness_check compiled {}
set_option veil.violationIsError false in
/--
info: ❌ Violation: liveness_failure (violates: eventuallyFlag)
  Stem:
    State 0:
      flag = false
  Loop (repeats):
    State 0:
      flag = false
-/
#guard_msgs in
#liveness_check {}
end LivenessCounterexample

veil module LivenessConstraint
individual flag : Bool
after_init { flag := false }
action toggle { flag := !flag }
action idle { flag := flag }
state_constraint [unflagged] ¬ flag
temporal [alwaysUnflagged] □ ⌜ ¬ flag ⌝
-- Negating this places an edge atom in a hoisted FG region, exercising crossing.
temporal (only := check) [fairIdle] (□ ◇ E(idle)) → (□ ◇ T(idle))
invariant true
#gen_spec
/-- info: ✅ No liveness violation (checked 2 properties, explored 1 product states) -/
#guard_msgs in
#liveness_check interpreted {}
/-- info: ✅ No liveness violation (checked 2 properties, explored 1 product states) -/
#guard_msgs in
#liveness_check compiled {}
end LivenessConstraint

veil module NoLiveness
individual flag : Bool
after_init { flag := false }
action idle { flag := flag }
invariant true
#gen_spec
/--
error: No temporal property of this module is model checked. Declare one with `temporal` (without `only := verify`) first.
-/
#guard_msgs in
#liveness_check interpreted {}
end NoLiveness

-- Temporary native entry points must not pollute the elaboration environment.
def main : IO Unit := pure ()

veil module LivenessCompilationFailure
individual flag : Bool
after_init { flag := false }
action idle { flag := flag }
invariant true
temporal [trivial] □ ⊤
#gen_spec

/--
error: Cannot compile #liveness_check: the file already declares `main`, which the generated binary needs as its entry point. Move the `main` declaration into another file, or use `#liveness_check interpreted`.
-/
#guard_msgs in
#liveness_check compiled {}

-- A background compilation failure must preserve the interpreted verdict.
/--
info: ✅ No liveness violation (checked 1 properties, explored 1 product states)
---
warning: Cannot compile #liveness_check: the file already declares `main`, which the generated binary needs as its entry point. Move the `main` declaration into another file, or use `#liveness_check interpreted`.
-/
#guard_msgs (ordering := sorted) in
#liveness_check {}

end LivenessCompilationFailure

/-! ## Route selection -/

veil module LivenessRoutes
individual flag : Bool
individual other : Bool
after_init { flag := false; other := false }
action set { flag := true }
action idle { other := other }
temporal [fairFlag] (□ ◇ ⌜ ¬ flag ⌝) → □ ◇ ⌜ ¬ flag ⌝
temporal (only := check) [eventuallyFlag] (□ ◇ T(set)) → ◇ ⌜ flag ⌝
invariant true
#gen_spec

/-- info: ✅ No liveness violation (checked 2 properties, explored 5 product states) -/
#guard_msgs in
#liveness_check interpreted {} {} (route := .fair)
/-- info: ✅ No liveness violation (checked 2 properties, explored 5 product states) -/
#guard_msgs in
#liveness_check interpreted {} {} (route := .prune)
/-- info: ✅ No liveness violation (checked 2 properties, explored 5 product states) -/
#guard_msgs in
#liveness_check interpreted {} {} (route := .patOnly)
/-- info: ✅ No liveness violation (checked 2 properties, explored 2 product states) -/
#guard_msgs in
#liveness_check interpreted {} {} (route := .crossing)
/-- info: ✅ No liveness violation (checked 2 properties, explored 5 product states) -/
#guard_msgs in
#liveness_check interpreted {} {} (route := .dijkstra)
/-- info: ✅ No liveness violation (checked 2 properties, explored 6 product states) -/
#guard_msgs in
#liveness_check interpreted {} {} (route := .ndfs) finite_reach_by native_decide
/--
error: `(route := .ndfs)` needs a `finite_reach_by` clause, e.g. `finite_reach_by native_decide`.
-/
#guard_msgs in
#liveness_check interpreted {} {} (route := .ndfs)
/-- error: `(route := .fair)` does not take a `finite_reach_by` clause. -/
#guard_msgs in
#liveness_check interpreted {} {} (route := .fair) finite_reach_by native_decide

/-! ### Selecting properties -/

/-- info: ✅ No liveness violation (checked 1 properties, explored 3 product states) -/
#guard_msgs in
#liveness_check [fairFlag] interpreted {}
/-- info: ✅ No liveness violation (checked 1 properties, explored 2 product states) -/
#guard_msgs in
#liveness_check [eventuallyFlag] interpreted {}
-- Checked in declaration order.
/-- info: ✅ No liveness violation (checked 2 properties, explored 5 product states) -/
#guard_msgs in
#liveness_check [eventuallyFlag] [fairFlag] interpreted {}
/-- info: ✅ No liveness violation (checked 1 properties, explored 3 product states) -/
#guard_msgs in
#liveness_check [fairFlag] interpreted {} {} (route := .dijkstra)
/--
error: `noSuchProperty` is not a model-checked temporal property of this module. Model checked: fairFlag, eventuallyFlag
-/
#guard_msgs in
#liveness_check [noSuchProperty] interpreted {}
/-- error: `fairFlag` is named twice. -/
#guard_msgs in
#liveness_check [fairFlag] [fairFlag] interpreted {}
end LivenessRoutes
