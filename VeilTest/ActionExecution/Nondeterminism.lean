import VeilTest.ActionExecution

/-!
Concrete tests for nondeterministic statements, logical sharing, assumptions,
and the distinction between external and internal failure behavior.
-/

set_option linter.unusedVariables false

open VeilTest.ActionExecution

veil module ActionExecutionEffects

individual observed : Bool
individual touched : Bool

#gen_state

procedure pick_bool {
  let value ← pick Bool
  observed := value
  return value
}

procedure constrained_pick {
  let value : Bool :| value = true
  observed := value
  return value
}

procedure mutable_veil_var {
  veil_var value : Bool
  value := !value
  observed := value
  return value
}

procedure logical_let {
  veil_let value := !observed
  observed := value
  return value
}

procedure existential_if {
  if value :| value = true then
    observed := value
  else
    observed := false
  return observed
}

procedure havoc_bool {
  observed := *
  return observed
}

procedure local_havoc {
  let mut value := false
  value := *
  observed := value
  return value
}

-- A fixed index havocs a single entry of the local; the picked type is the
-- entry type, not the whole function.
procedure local_indexed_havoc {
  let mut m := fun _ : Bool => false
  m true := *
  return (m false, m true)
}

-- A capitalized index havocs every entry independently: the pick is a
-- function over that dimension.
procedure local_universal_havoc {
  let mut m := fun _ : Bool => false
  m N := *
  return (m false, m true)
}

/- The outer indexed arrow assignment and the havoc in its RHS have separate
control-info handlers. Both mutable locals must be threaded through the
surrounding branch join. -/
procedure havoc_inside_arrow_rhs {
  let mut value := false
  let mut target := fun _ : Bool => false
  if true then
    target true ← do
      value := *
      pure true
  return (value, target true)
}

procedure assume_value (allowed : Bool) {
  assume allowed = true
  touched := true
}

procedure assert_after_write (allowed : Bool) {
  observed := true
  assert allowed = true
  touched := true
  return observed
}

action require_after_write (allowed : Bool) {
  observed := true
  require allowed = true
  touched := true
  return observed
}

def initial : State FieldConcreteType := { observed := false, touched := false }

def pickResult := __veil_exec_action% {} {} initial pick_bool
#guard exactlyNSuccesses 2 pickResult fun value state =>
  state.observed == value && !state.touched
#guard hasSuccess pickResult fun value state => !value && !state.observed
#guard hasSuccess pickResult fun value state => value && state.observed

def constrainedResult := __veil_exec_action% {} {} initial constrained_pick
#guard exactlyOneSuccess constrainedResult fun value state =>
  value && state.observed && !state.touched

def veilVarResult := __veil_exec_action% {} {} initial mutable_veil_var
#guard exactlyNSuccesses 2 veilVarResult fun value state =>
  state.observed == value && !state.touched
#guard hasSuccess veilVarResult fun value state => !value && !state.observed
#guard hasSuccess veilVarResult fun value state => value && state.observed

def logicalLetResult := __veil_exec_action% {} {} initial logical_let
#guard exactlyOneSuccess logicalLetResult fun value state =>
  value && state.observed && !state.touched

def existentialResult := __veil_exec_action% {} {} initial existential_if
#guard exactlyOneSuccess existentialResult fun value state =>
  value && state.observed && !state.touched

def havocResult := __veil_exec_action% {} {} initial havoc_bool
#guard exactlyNSuccesses 2 havocResult fun value state =>
  state.observed == value && !state.touched
#guard hasSuccess havocResult fun value state => !value && !state.observed
#guard hasSuccess havocResult fun value state => value && state.observed

def localHavocResult := __veil_exec_action% {} {} initial local_havoc
#guard exactlyNSuccesses 2 localHavocResult fun value state =>
  state.observed == value && !state.touched
#guard hasSuccess localHavocResult fun value _ => value
#guard hasSuccess localHavocResult fun value _ => !value

def localIndexedHavocResult :=
  __veil_exec_action% {} {} initial local_indexed_havoc
#guard exactlyNSuccesses 2 localIndexedHavocResult fun value state =>
  value.1 == false && !state.observed && !state.touched
#guard hasSuccess localIndexedHavocResult fun value _ => value == (false, true)
#guard hasSuccess localIndexedHavocResult fun value _ => value == (false, false)

def localUniversalHavocResult :=
  __veil_exec_action% {} {} initial local_universal_havoc
#guard exactlyNSuccesses 4 localUniversalHavocResult fun _ state =>
  !state.observed && !state.touched
#guard hasSuccess localUniversalHavocResult fun value _ => value == (false, false)
#guard hasSuccess localUniversalHavocResult fun value _ => value == (false, true)
#guard hasSuccess localUniversalHavocResult fun value _ => value == (true, false)
#guard hasSuccess localUniversalHavocResult fun value _ => value == (true, true)

def rhsHavocResult := __veil_exec_action% {} {} initial havoc_inside_arrow_rhs
#guard exactlyNSuccesses 2 rhsHavocResult fun value state =>
  value.2 && !state.observed && !state.touched
#guard hasSuccess rhsHavocResult fun value _ => value == (false, true)
#guard hasSuccess rhsHavocResult fun value _ => value == (true, true)

def assumeTrueResult := __veil_exec_action% {} {} initial (assume_value true)
#guard exactlyOneSuccess assumeTrueResult fun _ state =>
  !state.observed && state.touched

def assumeFalseResult := __veil_exec_action% {} {} initial (assume_value false)
#guard hasNoExecutions assumeFalseResult

def assertTrueResult := __veil_exec_action% {} {} initial (assert_after_write true)
#guard exactlyOneSuccess assertTrueResult fun value state =>
  value && state.observed && state.touched

def assertFalseResult := __veil_exec_action% {} {} initial (assert_after_write false)
#guard assertFalseResult.length == 1
#guard hasAssertionFailure assertFalseResult fun _ state =>
  state.observed && !state.touched

-- External `require` is an assumption and therefore discards the execution.
def externalRequireFalseResult :=
  __veil_exec_action% {} {} initial (require_after_write.ext false)
#guard hasNoExecutions externalRequireFalseResult

-- Internal `require` is a caller obligation and therefore reports failure.
def internalRequireFalseResult :=
  __veil_exec_action% {} {} initial (require_after_write false)
#guard internalRequireFalseResult.length == 1
#guard hasAssertionFailure internalRequireFalseResult fun _ state =>
  state.observed && !state.touched

def externalRequireTrueResult :=
  __veil_exec_action% {} {} initial (require_after_write.ext true)
#guard exactlyOneSuccess externalRequireTrueResult fun value state =>
  value == () && state.observed && state.touched

end ActionExecutionEffects
