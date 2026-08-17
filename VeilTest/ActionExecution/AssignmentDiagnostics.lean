import VeilTest.ActionExecution

set_option linter.unusedVariables false

open VeilTest.ActionExecution

veil module ActionExecutionAssignmentDiagnostics

individual x : Nat
relation r : Bool → Bool
relation r2 : Bool → Bool → Bool
-- The explicit binder keeps the function-valued codomain out of the field's
-- represented domain, exercising assignment's codomain-residue path.
function table (key : Bool) : Bool → Nat

veil_set_field_representation relation Veil.CanonicalField
veil_set_field_representation function Veil.CanonicalField

#gen_state

procedure index_effect {
  return true
}

/--
error: Error in action reject_arrow_fallback: fallback branches are not supported on Veil state arrow assignments
-/
#guard_msgs(error, drop warning) in
procedure reject_arrow_fallback {
  r true ← pure true | pure ()
}

/--
error: Error in action reject_wrong_state_ascription: state assignment type `Int` does not match the declared type `Nat` of component `x`
-/
#guard_msgs(error, drop warning) in
procedure reject_wrong_state_ascription {
  x : Int := 0
}

/--
error: Error in action reject_qualified_state_write: qualified state assignments are not supported; assign through an unqualified state component name
-/
#guard_msgs(error, drop warning) in
procedure reject_qualified_state_write {
  child.x := 1
}

/--
error: Error in action reject_effectful_target_index: effects are not supported in state-update target indices
-/
#guard_msgs(error, drop warning) in
procedure reject_effectful_target_index {
  r (← index_effect) := true
}

/- A fixed (non-capitalized) index is elaborated at statement scope, where the
universal `N` does not exist. It must NOT be captured by the `fun N` binder the
capital generates, which would silently turn the universal update into a
diagonal one. -/
/--
error: Error in action reject_capital_in_fixed_index: Unknown identifier `N`
-/
#guard_msgs(error, drop warning) in
procedure reject_capital_in_fixed_index {
  r2 N (not N) := true
}

/- The sharper variant: a codomain-residue index occurs ONLY in the replacement
body, directly under the generated `fun N` binder — exactly where an unpinned
index would be captured silently instead of failing to elaborate. -/
/--
error: Error in action reject_capital_in_codomain_index: Unknown identifier `N`
-/
#guard_msgs(error, drop warning) in
procedure reject_capital_in_codomain_index {
  table N (not N) := 5
}

-- Contrast: the right-hand side deliberately IS evaluated under the universal
-- binder, so `N` there refers to each updated index.
procedure capital_in_rhs {
  r2 N true := N
}

/- Havoc resolves its target under the same local-precedence rule as `:=`.
Previously it looked the name up in the module signature directly, silently
havocking the shadowed state component while every read resolved to the
local. Now the LOCAL is havocked and the component is untouched. -/
#guard_msgs(drop warning) in
procedure shadowed_havoc_hits_local {
  let mut r := fun _ : Bool => false
  r true := *
  return r true
}

/--
error: Error in action reject_immutable_local_havoc: this local is immutable; only variables declared with `let mut` can be assigned
-/
#guard_msgs(error, drop warning) in
procedure reject_immutable_local_havoc {
  let m := fun _ : Bool => false
  m true := *
}

/--
error: Error in action reject_over_indexed_local_havoc: cannot havoc `v`: its type
  Bool
does not accept this many index arguments
-/
#guard_msgs(error, drop warning) in
procedure reject_over_indexed_local_havoc {
  let mut v := false
  v true := *
}

/--
error: Error in action reject_unknown_havoc: assignment target `nosuch` is not a mutable state component or a `let mut` local
-/
#guard_msgs(error, drop warning) in
procedure reject_unknown_havoc {
  nosuch := *
}

procedure accept_matching_state_ascription {
  x : Nat := 4
  return x
}

def initial : State FieldConcreteType :=
  { x := 0, r := fun _ => false, r2 := fun _ _ => false, table := fun _ _ => 0 }
def matchingAscriptionResult :=
  __veil_exec_action% {} {} initial accept_matching_state_ascription
#guard exactlyOneSuccess matchingAscriptionResult fun value state =>
  value == 4 && state.x == 4

def capitalRhsResult :=
  __veil_exec_action% {} {} initial capital_in_rhs
#guard exactlyOneSuccess capitalRhsResult fun _ state =>
  (state.r2 true true : Bool) && !(state.r2 false true : Bool) &&
  !(state.r2 true false : Bool) && !(state.r2 false false : Bool)

-- The local is havocked (two alternatives); the component keeps its initial
-- all-false value in both.
def shadowedHavocResult :=
  __veil_exec_action% {} {} initial shadowed_havoc_hits_local
#guard exactlyNSuccesses 2 shadowedHavocResult fun _ state =>
  !(state.r : Bool → Bool) true && !(state.r : Bool → Bool) false
#guard hasSuccess shadowedHavocResult fun value _ => value
#guard hasSuccess shadowedHavocResult fun value _ => !value

end ActionExecutionAssignmentDiagnostics
