module

public import VeilTest.ActionExecution
public meta import VeilTest.ActionExecution

/-!
Proof binders at statement boundaries: lifted calls run once, subsequent
statements see their writes, proof scopes restore component names, and a
failed assertion keeps its own ID and stops the continuation. These exercise
the new syntax against the old action-elaboration regressions, independently
of the state-opening counts and pick logs in their owning test modules.
-/

set_option linter.unusedVariables false

open VeilTest.ActionExecution

veil module ProofBinderBoundaries

immutable individual limit : Nat
individual bound : Nat
individual chosen : Nat
individual calls : Nat

#gen_state

procedure advance {
  bound := bound + 1
  calls := calls + 1
  return bound
}

procedure require_after_call {
  require h : (← advance) = bound
  chosen := bound
}

procedure assert_after_call {
  assert h : (← advance) = bound
  chosen := bound
}

procedure assume_after_call {
  assume h : (← advance) = bound
  chosen := bound
}

procedure pick_type_after_call {
  let i : Fin (← advance) :| h : i.val < bound
  chosen := i.val
}

-- The witness type itself mentions mutable state; the generated subtype
-- bind must not put it outside the type metavariable's creation context.
procedure state_dependent_witness {
  let i : { i : Fin 3 // i.val < bound } :| h : i.val.val < limit
  chosen := i.val.val
}

procedure branch_mutation (take : Bool) {
  let mut result := 0
  if take then
    require h : True
    assert h' : True
    assume h'' : True
    result := 1
  else
    result := 2
  return result
}

/--
warning: local `bound` shadows mutable state component `bound`; references to this name resolve to the local
-/
#guard_msgs(warning) in
procedure require_shadow_scope (take : Bool) {
  if take then
    require bound : True
    have : True := bound
  chosen := bound
}

/--
warning: local `bound` shadows mutable state component `bound`; references to this name resolve to the local
-/
#guard_msgs(warning) in
procedure assert_shadow_scope (take : Bool) {
  if take then
    assert bound : True
    have : True := bound
  chosen := bound
}

/--
warning: local `limit` shadows immutable theory component `limit`; references to this name resolve to the local
-/
#guard_msgs(warning) in
procedure assume_shadow_scope (take : Bool) {
  if take then
    assume limit : True
    have : True := limit
  return limit
}

/--
warning: local `limit` shadows immutable theory component `limit`; references to this name resolve to the local
-/
#guard_msgs(warning) in
procedure pick_shadow_scope (take : Bool) {
  if take then
    let b : Bool :| limit : b = true
    have : b = true := limit
  return limit
}

-- Both branches of a native dependent `if` must get the corresponding
-- proof, including the negative one, and preserve local mutations.
procedure dependent_if (n : Nat) {
  let mut result := 0
  if h : n = 0 then
    have : n = 0 := h
    result := 10
  else
    have : n ≠ 0 := h
    result := 20
  return result
}

procedure first_failure (first : Bool) {
  bound := bound + 1
  assert h : first = false
  bound := bound + 1
  require h' : False
  bound := 100
}

def background : Theory := { limit := 3 }
def initial : State FieldConcreteType := { bound := 1, chosen := 0, calls := 0 }

#guard exactlyOneSuccess (__veil_exec_action% {} background initial require_after_call) fun _ st =>
  st.bound == 2 && st.chosen == 2 && st.calls == 1
#guard exactlyOneSuccess (__veil_exec_action% {} background initial assert_after_call) fun _ st =>
  st.bound == 2 && st.chosen == 2 && st.calls == 1
#guard exactlyOneSuccess (__veil_exec_action% {} background initial assume_after_call) fun _ st =>
  st.bound == 2 && st.chosen == 2 && st.calls == 1

#guard exactlyNSuccesses 2 (__veil_exec_action% {} background initial pick_type_after_call) fun _ st =>
  st.bound == 2 && st.chosen < 2 && st.calls == 1
#guard exactlyOneSuccess (__veil_exec_action% {} background initial state_dependent_witness) fun _ st =>
  st.chosen == 0 && st.bound == 1

#guard [false, true].all fun take =>
  exactlyOneSuccess (__veil_exec_action% {} background initial (branch_mutation take)) fun n st =>
    n == (if take then 1 else 2) && st.bound == 1
#guard [false, true].all fun take =>
  exactlyOneSuccess (__veil_exec_action% {} background initial (require_shadow_scope take)) fun _ st =>
    st.chosen == 1
#guard [false, true].all fun take =>
  exactlyOneSuccess (__veil_exec_action% {} background initial (assert_shadow_scope take)) fun _ st =>
    st.chosen == 1
#guard [false, true].all fun take =>
  exactlyOneSuccess (__veil_exec_action% {} background initial (assume_shadow_scope take)) fun n _ =>
    n == 3
#guard [false, true].all fun take =>
  exactlyOneSuccess (__veil_exec_action% {} background initial (pick_shadow_scope take)) fun n _ =>
    n == 3

#guard exactlyOneSuccess (__veil_exec_action% {} background initial (dependent_if 0)) fun n _ => n == 10
#guard exactlyOneSuccess (__veil_exec_action% {} background initial (dependent_if 1)) fun n _ => n == 20

def failFirst := __veil_exec_action% {} background initial (first_failure true)
def failSecond := __veil_exec_action% {} background initial (first_failure false)
#guard match failFirst, failSecond with
  | [.assertionFailure ex₁ st₁], [.assertionFailure ex₂ st₂] =>
    ex₁ != ex₂ && st₁.bound == 2 && st₂.bound == 3
  | _, _ => false

/- Binding a proof or a witness is a statement returning Unit, even if its
underlying monadic operation returns a subtype. It cannot supply a branch's
Nat result. -/
/--
error: Error in action reject_require_value: Type mismatch. The `do` element has monadic result type
  Unit
but the rest of the `do` block has monadic result type
  Nat
-/
#guard_msgs in
procedure reject_require_value (take : Bool) {
  if take then return (1 : Nat) else require h : True
}

/--
error: Error in action reject_assert_value: Type mismatch. The `do` element has monadic result type
  Unit
but the rest of the `do` block has monadic result type
  Nat
-/
#guard_msgs in
procedure reject_assert_value (take : Bool) {
  if take then return (1 : Nat) else assert h : True
}

/--
error: Error in action reject_assume_value: Type mismatch. The `do` element has monadic result type
  Unit
but the rest of the `do` block has monadic result type
  Nat
-/
#guard_msgs in
procedure reject_assume_value (take : Bool) {
  if take then return (1 : Nat) else assume h : True
}

/--
error: Error in action reject_pick_value: Type mismatch. The `do` element has monadic result type
  Unit
but the rest of the `do` block has monadic result type
  Nat
-/
#guard_msgs in
procedure reject_pick_value (take : Bool) {
  if take then return (1 : Nat) else let b : Bool :| h : b
}

-- Test the proof's scope independently of the witness's scope.
/-- error: Error in action reject_proof_in_else: Unknown identifier `h` -/
#guard_msgs in
procedure reject_proof_in_else {
  if b : Bool :| h : b then
    pure ()
  else
    have : True := by exact h
}

/-- error: Error in action reject_proof_after_if: Unknown identifier `h` -/
#guard_msgs in
procedure reject_proof_after_if {
  if b : Bool :| h : b then
    pure ()
  have : True := by exact h
}

end ProofBinderBoundaries
