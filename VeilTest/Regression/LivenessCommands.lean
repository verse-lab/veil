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

liveness [alwaysTrue] □ ⊤
liveness [enabled] □ E(activate)
liveness [step] □ (T(activate) ∨ T(idle))
liveness [fairProgress] (□ ◇ T(activate)) → ◇ ⌜ ∃ n, active n ⌝

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
liveness [trivial] □ ⊤
liveness [eventuallyFlag] ◇ ⌜ flag ⌝
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
    State 1:
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
    State 1:
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
    State 1:
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
liveness [alwaysUnflagged] □ ⌜ ¬ flag ⌝
-- Negating this places an edge atom in a hoisted FG region, exercising crossing.
liveness [fairIdle] (□ ◇ E(idle)) → (□ ◇ T(idle))
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
/-- error: No liveness properties declared in this module. Declare a `liveness` property first. -/
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
liveness [trivial] □ ⊤
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

/-! ## Route selection

`(route := …)` picks which of LTLLib's searches runs. All of them must reach the same verdict;
what legitimately differs is how many product states they touch, which is the point of the
ablation, so the expected messages below differ only in that number. `crossing` reports fewer here
because its per-disjunct feasibility pre-pass settles this question on the system graph without
ever building the product, and `ndfs` reports more because it degeneralizes the automaton first.

Only the interpreted mode is exercised: the route is baked into the generated program, so the
compiled path is the one the `main`-declaring tests above already cover, and this file cannot
compile anything after them. -/

veil module LivenessRoutes
individual flag : Bool
individual other : Bool
after_init { flag := false; other := false }
action set { flag := true }
action idle { other := other }
liveness [fairFlag] (□ ◇ ⌜ ¬ flag ⌝) → □ ◇ ⌜ ¬ flag ⌝
liveness [eventuallyFlag] (□ ◇ T(set)) → ◇ ⌜ flag ⌝
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
-- `ndfs` is the one route that has to be handed a `FiniteReach` certificate. `native_decide`
-- discharges it by exploring the state space during elaboration, which is why a benchmark
-- measuring this route writes `sorry` instead and carries the `sorryAx` in its own file.
/-- info: ✅ No liveness violation (checked 2 properties, explored 6 product states) -/
#guard_msgs in
#liveness_check interpreted {} {} (route := .ndfs) finite_reach_by native_decide
/--
error: `(route := .ndfs)` needs a `FiniteReach` certificate: it is the one route whose search recurses on one. Add a `finite_reach_by` clause -- `finite_reach_by native_decide` proves it by exploring the whole state space at elaboration time, which a measurement of this route will not want to pay.
-/
#guard_msgs in
#liveness_check interpreted {} {} (route := .ndfs)
/--
error: `(route := .fair)` needs no `FiniteReach` certificate, so `finite_reach_by` would prove nothing. Remove the clause.
-/
#guard_msgs in
#liveness_check interpreted {} {} (route := .fair) finite_reach_by native_decide

/-! ### Selecting properties

Naming properties in brackets checks only those, and the per-property counts sum to the
module-wide total above (3 + 2 = 5). That is what makes this worth having: an ablation can measure
one question at a time against one model, and a property that fails no longer hides the ones
declared after it. -/

/-- info: ✅ No liveness violation (checked 1 properties, explored 3 product states) -/
#guard_msgs in
#liveness_check [fairFlag] interpreted {}
/-- info: ✅ No liveness violation (checked 1 properties, explored 2 product states) -/
#guard_msgs in
#liveness_check [eventuallyFlag] interpreted {}
-- Named out of declaration order, and still checked in declaration order: the command's contract
-- is that properties are checked in order and stop at the first counterexample, and selecting a
-- subset must not quietly change that.
/-- info: ✅ No liveness violation (checked 2 properties, explored 5 product states) -/
#guard_msgs in
#liveness_check [eventuallyFlag] [fairFlag] interpreted {}
-- The selection composes with the route.
/-- info: ✅ No liveness violation (checked 1 properties, explored 3 product states) -/
#guard_msgs in
#liveness_check [fairFlag] interpreted {} {} (route := .dijkstra)
/--
error: `noSuchProperty` is not a liveness property of this module. Declared: fairFlag, eventuallyFlag
-/
#guard_msgs in
#liveness_check [noSuchProperty] interpreted {}
/-- error: `fairFlag` is named twice; each property is checked once. -/
#guard_msgs in
#liveness_check [fairFlag] [fairFlag] interpreted {}
end LivenessRoutes
