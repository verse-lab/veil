import VeilTest.ActionExecution

set_option linter.unusedVariables false

open VeilTest.ActionExecution

def ACK : Bool := true

inductive CapitalIndex where
  | Zero
  | One
deriving DecidableEq

open CapitalIndex

veil module ActionExecutionShadowWarnings

immutable individual bias : Nat
individual X : Bool
relation r : Bool → Bool
relation q : CapitalIndex → Bool

veil_set_field_representation relation Veil.CanonicalField

#gen_state

theory ghost relation theory_bias_is_five := bias = 5
ghost relation state_X_is_false := X = false
ghost relation state_X_is_true := X = true

procedure set_X_true {
  X := true
}

/--
warning: parameter `bias` shadows immutable theory component `bias`; references to this name resolve to the parameter
-/
#guard_msgs(warning) in
procedure parameter_shadows_theory (bias : Nat) {
  return bias
}

/--
warning: local `bias` shadows immutable theory component `bias`; references to this name resolve to the local
-/
#guard_msgs(warning) in
procedure local_shadows_theory {
  let bias := 11
  return bias
}

/- The shadowing parameter is deliberately inconsistent with the ghost
relation.  Ghost defaults must use the actual theory/state bindings rather
than accidentally reconstructing them from the same-named parameter. -/
/--
warning: parameter `bias` shadows immutable theory component `bias`; references to this name resolve to the parameter
-/
#guard_msgs(warning) in
procedure theory_ghost_under_parameter_shadow (bias : Nat) {
  require theory_bias_is_five
  return bias
}

/--
warning: local `bias` shadows immutable theory component `bias`; references to this name resolve to the local
-/
#guard_msgs(warning) in
procedure theory_ghost_under_local_shadow {
  let bias := 23
  require theory_bias_is_five
  return bias
}

/--
warning: parameter `X` shadows mutable state component `X`; references to this name resolve to the parameter
-/
#guard_msgs(warning) in
procedure state_ghost_under_parameter_shadow (X : Bool) {
  require state_X_is_false
  return X
}

/- The call mutates the real state while the same-named parameter remains
unchanged.  The ghost relation must receive the fresh post-call state view. -/
/--
warning: parameter `X` shadows mutable state component `X`; references to this name resolve to the parameter
-/
#guard_msgs(warning) in
procedure state_ghost_after_call_under_parameter_shadow (X : Bool) {
  set_X_true
  require state_X_is_true
  return X
}

/--
warning: local `X` shadows mutable state component `X`; references to this name resolve to the local
-/
#guard_msgs(warning) in
procedure state_ghost_under_local_shadow {
  let X := true
  require state_X_is_false
  return X
}

/--
warning: capitalized index `X` resolves to mutable state component `X`; this is a point update, not a universal update
-/
#guard_msgs(warning) in
procedure capital_component_is_point_update {
  r X := true
}

/--
warning: capitalized index `N` resolves to parameter `N`; this is a point update, not a universal update
-/
#guard_msgs(warning) in
procedure capital_parameter_is_point_update (N : Bool) {
  r N := true
}

/--
warning: capitalized index `N` resolves to local `N`; this is a point update, not a universal update
-/
#guard_msgs(warning) in
procedure capital_local_is_point_update {
  let N := false
  r N := true
}

/- A Lean global never captures a bare capital: semantics must not depend on
imports. The shadowing is warned about. -/
/--
warning: capitalized index `ACK` is a universal index and shadows the Lean declaration `ACK`; to use the declaration as a point index, bind it to a non-capitalized local first
-/
#guard_msgs(warning) in
procedure capital_global_is_universal {
  r ACK := true
}

/- Havoc used to run the capital analysis twice — once itself and once in the
assignment it delegates to — duplicating this warning. The guard requires it
exactly once. -/
/--
warning: capitalized index `N` resolves to parameter `N`; this is a point update, not a universal update
-/
#guard_msgs(warning) in
procedure havoc_capital_warns_once (N : Bool) {
  r N := *
}

/--
warning: local `bias` shadows immutable theory component `bias`; references to this name resolve to the local
-/
#guard_msgs(warning) in
procedure theory_shadow_scope_restores {
  if true then
    let bias := 19
    let _ := bias
  return bias
}

def background : Theory := { bias := 5 }
def initial : State FieldConcreteType := {
  X := false
  r := fun _ => false
  q := fun _ => false
}

def parameterShadowResult :=
  __veil_exec_action% {} background initial (parameter_shadows_theory 17)
#guard exactlyOneSuccess parameterShadowResult fun value state =>
  value == 17 && !state.X

def localShadowResult :=
  __veil_exec_action% {} background initial local_shadows_theory
#guard exactlyOneSuccess localShadowResult fun value state =>
  value == 11 && !state.X

def theoryGhostShadowResult :=
  __veil_exec_action% {} background initial
    (theory_ghost_under_parameter_shadow 17)
#guard exactlyOneSuccess theoryGhostShadowResult fun value state =>
  value == 17 && !state.X

def theoryGhostLocalShadowResult :=
  __veil_exec_action% {} background initial theory_ghost_under_local_shadow
#guard exactlyOneSuccess theoryGhostLocalShadowResult fun value state =>
  value == 23 && !state.X

def stateGhostShadowResult :=
  __veil_exec_action% {} background initial
    (state_ghost_under_parameter_shadow true)
#guard exactlyOneSuccess stateGhostShadowResult fun value state =>
  value && !state.X

def stateGhostLocalShadowResult :=
  __veil_exec_action% {} background initial state_ghost_under_local_shadow
#guard exactlyOneSuccess stateGhostLocalShadowResult fun value state =>
  value && !state.X

def stateGhostAfterCallShadowResult :=
  __veil_exec_action% {} background initial
    (state_ghost_after_call_under_parameter_shadow false)
#guard exactlyOneSuccess stateGhostAfterCallShadowResult fun value state =>
  !value && state.X

def componentResult :=
  __veil_exec_action% {} background initial capital_component_is_point_update
#guard exactlyOneSuccess componentResult fun _ state =>
  (state.r : Bool → Bool) false && !(state.r : Bool → Bool) true

def parameterResult :=
  __veil_exec_action% {} background initial (capital_parameter_is_point_update true)
#guard exactlyOneSuccess parameterResult fun _ state =>
  !(state.r : Bool → Bool) false && (state.r : Bool → Bool) true

def localCapitalResult :=
  __veil_exec_action% {} background initial capital_local_is_point_update
#guard exactlyOneSuccess localCapitalResult fun _ state =>
  (state.r : Bool → Bool) false && !(state.r : Bool → Bool) true

def globalResult :=
  __veil_exec_action% {} background initial capital_global_is_universal
#guard exactlyOneSuccess globalResult fun _ state =>
  (state.r : Bool → Bool) false && (state.r : Bool → Bool) true

def restoredTheoryResult :=
  __veil_exec_action% {} background initial theory_shadow_scope_restores
#guard exactlyOneSuccess restoredTheoryResult fun value state =>
  value == 5 && !state.X

end ActionExecutionShadowWarnings
