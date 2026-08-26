import VeilTest.ActionExecution

/-!
Gap coverage for the extensible-`do` frontend, complementing the suites in
this directory: sequential read-after-write semantics, existential `if`
(else branch, multiple witnesses, typed and typed-tuple witnesses), typed
`let :| `, cross-action calls whose `require` fails or whose results are
destructured, `veil_let` binder forms, function-typed `veil_var`, and
dependent `if h :`. Every behavior is observed through concrete execution.
-/

set_option linter.unusedVariables false

open VeilTest.ActionExecution

veil module FrontendSemantics

individual counter : Nat
individual flag : Bool
individual mirror : Bool
relation link : Bool → Bool

veil_set_field_representation relation Veil.CanonicalField

#gen_state

open scoped FrontendSemantics

/-! ### Sequential read-after-write -/

procedure increment_twice {
  counter := counter + 1
  counter := counter + 1
  return counter
}

/- Statements see the writes of earlier statements: the second copy reads the
first write's value, not the pre-state (assignments are sequential, not
simultaneous). -/
procedure sequential_copy {
  flag := mirror
  mirror := flag
  return (flag, mirror)
}

procedure self_referential_indexed_update {
  link true := !(link true)
  return link true
}

/-! ### Existential `if` -/

procedure existential_if_else_branch {
  if w :| w = true ∧ w = false then
    flag := w
  else
    counter := 5
  return counter
}

/- Both booleans satisfy the predicate, so the bound witness branches over
both of them. -/
procedure existential_if_multi_witness {
  if w : Bool :| w = w then
    flag := w
  return flag
}

procedure typed_existential_if {
  if w : Bool :| w = false then
    mirror := w
  return mirror
}

procedure typed_tuple_existential_if {
  if (a, b) : Bool × Bool :| a = true ∧ b = false then
    flag := a
    mirror := b
  return (flag, mirror)
}

procedure typed_let_pick {
  let w : Bool :| w = false
  mirror := w
  return w
}

/-! ### Cross-action calls -/

action guarded_step (ok : Bool) {
  require ok = true
  counter := counter + 1
  return counter
}

procedure call_with_failing_require {
  let n ← guarded_step false
  return n
}

procedure call_with_passing_require {
  let n ← guarded_step true
  counter := n + 10
  return n
}

procedure pair_producer {
  return (!flag, counter + 1)
}

procedure destructuring_bind {
  let (b, n) ← pair_producer
  flag := b
  counter := n
  return (b, n)
}

/-! ### `veil_let` binder forms -/

procedure veil_let_tuple_pattern {
  veil_let (a, b) := (flag, !flag)
  flag := b
  mirror := a
  return (a, b)
}

/-! ### Function-typed `veil_var` -/

procedure veil_var_function_update {
  veil_var table : Bool → Bool
  table := fun _ => false
  table true := true
  return (table false, table true)
}

/-! ### Dependent `if h :` -/

procedure dependent_if_hypothesis {
  if h : counter = 0 then
    flag := decide (counter = 0)
  else
    flag := false
  return flag
}

def initial : State FieldConcreteType := {
  counter := 0
  flag := true
  mirror := false
  link := fun _ => false
}

def incrementResult := __veil_exec_action% {} {} initial increment_twice
#guard exactlyOneSuccess incrementResult fun value state =>
  value == 2 && state.counter == 2

def sequentialCopyResult := __veil_exec_action% {} {} initial sequential_copy
#guard exactlyOneSuccess sequentialCopyResult fun value state =>
  value == (false, false) && !state.flag && !state.mirror

def selfReferentialResult :=
  __veil_exec_action% {} {} initial self_referential_indexed_update
#guard exactlyOneSuccess selfReferentialResult fun value state =>
  value && (state.link : Bool → Bool) true && !(state.link : Bool → Bool) false

def elseBranchResult :=
  __veil_exec_action% {} {} initial existential_if_else_branch
#guard exactlyOneSuccess elseBranchResult fun value state =>
  value == 5 && state.counter == 5 && state.flag

def multiWitnessResult :=
  __veil_exec_action% {} {} initial existential_if_multi_witness
#guard exactlyNSuccesses 2 multiWitnessResult fun value state =>
  state.flag == value && state.counter == 0
#guard hasSuccess multiWitnessResult fun value _ => value
#guard hasSuccess multiWitnessResult fun value _ => !value

def typedExistentialResult :=
  __veil_exec_action% {} {} initial typed_existential_if
#guard exactlyOneSuccess typedExistentialResult fun value state =>
  !value && !state.mirror && state.flag

def typedTupleResult :=
  __veil_exec_action% {} {} initial typed_tuple_existential_if
#guard exactlyOneSuccess typedTupleResult fun value state =>
  value == (true, false) && state.flag && !state.mirror

def typedLetPickResult := __veil_exec_action% {} {} initial typed_let_pick
#guard exactlyOneSuccess typedLetPickResult fun value state =>
  !value && !state.mirror

def failingRequireResult :=
  __veil_exec_action% {} {} initial call_with_failing_require
#guard failingRequireResult.length == 1
#guard hasAssertionFailure failingRequireResult fun _ state =>
  state.counter == 0

def passingRequireResult :=
  __veil_exec_action% {} {} initial call_with_passing_require
#guard exactlyOneSuccess passingRequireResult fun value state =>
  value == 1 && state.counter == 11

def destructuringResult := __veil_exec_action% {} {} initial destructuring_bind
#guard exactlyOneSuccess destructuringResult fun value state =>
  value == (false, 1) && !state.flag && state.counter == 1

def veilLetTupleResult :=
  __veil_exec_action% {} {} initial veil_let_tuple_pattern
#guard exactlyOneSuccess veilLetTupleResult fun value state =>
  value == (true, false) && !state.flag && state.mirror

def veilVarFunctionResult :=
  __veil_exec_action% {} {} initial veil_var_function_update
#guard exactlyNSuccesses 4 veilVarFunctionResult fun value state =>
  value == (false, true) && state.counter == 0

def dependentIfResult :=
  __veil_exec_action% {} {} initial dependent_if_hypothesis
#guard exactlyOneSuccess dependentIfResult fun value state =>
  value && state.flag

/-! ### Regressions: stale state views in assignment paths -/

procedure set_mirror_true_return_true {
  mirror := true
  return true
}

/- The index of an indexed local arrow-assignment must read post-call state:
the callee flips `mirror` to `true`, so the write lands at index `true`. -/
procedure indexed_local_arrow_post_call_index {
  let mut m := fun _ : Bool => false
  m mirror ← set_mirror_true_return_true
  return (m false, m true)
}

def postCallIndexResult :=
  __veil_exec_action% {} {} initial indexed_local_arrow_post_call_index
#guard exactlyOneSuccess postCallIndexResult fun value state =>
  value == (false, true) && state.mirror

/- A tuple reassignment elaborates through Lean's builtin, but its right-hand
side must still see this statement's fresh state views, not the previous
statement's pre-call snapshot. -/
procedure tuple_reassign_post_call_state {
  let mut a := false
  let mut b := false
  let _ ← set_mirror_true_return_true
  (a, b) := (mirror, mirror)
  return (a, b)
}

def tupleReassignPostCallResult :=
  __veil_exec_action% {} {} initial tuple_reassign_post_call_state
#guard exactlyOneSuccess tupleReassignPostCallResult fun value state =>
  value == (true, true) && state.mirror

/-! ### Fallback arrow-binds on local reassignment defer to Lean's diagnostic
(Lean itself rejects reassignment fallbacks; Veil must not mask that with a
state-assignment error for targets that are plain mutable locals.) -/

/--
error: Error in action local_tuple_fallback_bind: reassignment with `|` (i.e., "else clause") is not supported
-/
#guard_msgs(error, drop warning) in
procedure local_tuple_fallback_bind {
  let mut a := false
  let mut b := false
  (a, b) ← pure (true, true) | pure ()
  return (a, b)
}

/-! ### Dependent `if h :`: the hypothesis is a usable proof in both branches -/

procedure dependent_if_proof_both (k : Nat) {
  let n := k
  if h : n = 0 then
    let _ : n = 0 := h
    flag := true
  else
    let _ : ¬ n = 0 := h
    flag := false
  return flag
}

def dependentIfProofTrueResult :=
  __veil_exec_action% {} {} initial (dependent_if_proof_both 0)
#guard exactlyOneSuccess dependentIfProofTrueResult fun value state =>
  value && state.flag

def dependentIfProofFalseResult :=
  __veil_exec_action% {} {} initial (dependent_if_proof_both 1)
#guard exactlyOneSuccess dependentIfProofFalseResult fun value state =>
  !value && !state.flag

/-! ### Dependent-`if` hypotheses get shadow warnings, `else` or not -/

/--
warning: local `flag` shadows mutable state component `flag`; references to this name resolve to the local
-/
#guard_msgs(warning) in
procedure dependent_if_hypothesis_shadow_warns {
  if flag : counter = 0 then
    mirror := true
}

def dependentIfShadowResult :=
  __veil_exec_action% {} {} initial dependent_if_hypothesis_shadow_warns
#guard exactlyOneSuccess dependentIfShadowResult fun _ state =>
  state.mirror && state.flag

/-! ### The legacy existential-`if` spelling is linted, never silent -/

/--
warning: Veil's existential `if` is now spelled `if w :| p`; this `if w : p` parses as Lean's dependent `if`, so the condition tests the existing binding of `w` instead of introducing a witness — rename the hypothesis if the dependent `if` is intended
-/
#guard_msgs(warning, substring := true) in
procedure legacy_existential_if_warns (w : Bool) {
  if w : link w then
    flag := true
}

end FrontendSemantics

/-! ### Diagnostics: immutable writes and `for` loops -/

veil module FrontendSemanticsDiagnostics

immutable individual frozen : Bool
individual scratch : Bool

#gen_state

/--
error: Error in action reject_immutable_write: individual frozen in module FrontendSemanticsDiagnostics was declared immutable, but trying to assign to it!
-/
#guard_msgs(error, drop warning) in
action reject_immutable_write {
  frozen := true
}

/--
error: Error in action reject_for: `for` loops are not supported in Veil actions
-/
#guard_msgs(error, drop warning) in
action reject_for {
  for _i in [true] do
    scratch := true
}

/--
error: Error in action reject_indexed_local_fallback: fallback branches are not supported on indexed Veil assignments
-/
#guard_msgs(error, drop warning) in
action reject_indexed_local_fallback {
  let mut m := fun _ : Bool => false
  m true ← pure true | pure ()
}

/--
error: `useFieldRepTC := false` is no longer supported; the action elaborator always uses the field-representation typeclass
-/
#guard_msgs in
veil_set_option useFieldRepTC false

end FrontendSemanticsDiagnostics
