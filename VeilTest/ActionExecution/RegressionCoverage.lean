import VeilTest.ActionExecution

/-!
Concrete regressions found while reviewing the extensible-`do` port.  Every
action is executed from an explicit state so successful elaboration alone
cannot hide an extraction or state-update bug.
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

open Lean Elab Term Meta
open VeilTest.ActionExecution

veil module ActionExecutionRegressionCoverage

individual x : Bool
individual y : Nat
individual tmp : Nat
relation r : Bool → Bool

veil_set_field_representation relation Veil.CanonicalField

#gen_state

macro "set_r_true" : doElem => `(doElem| r true := true)

macro "update_hygienic_tmp" : doElem =>
  `(doElem| do
    let mut tmp := 1
    tmp := 2)

procedure match_state_field {
  match x with
  | true => y := 1
  | false => y := 2
  return y
}

procedure match_local_derived_from_state {
  let localX := x
  match localX with
  | true => y := 3
  | false => y := 4
  return y
}

procedure macro_generated_write {
  if true then
    set_r_true
  return r true
}

procedure macro_generated_write_straight {
  set_r_true
  return r true
}

procedure macro_local_reassignment_is_hygienic {
  update_hygienic_tmp
  return y
}

procedure tuple_reassignment {
  let mut a := 1
  let mut b := 2
  (a, b) := (b, a)
  return (a, b)
}

procedure local_function_point_update {
  let mut m := fun _ : Bool => false
  m true := true
  return (m false, m true)
}

procedure local_function_point_arrow_update {
  let mut m := fun _ : Bool => false
  m true ← pure true
  return (m false, m true)
}

/- Indexed writes to a local `let mut` are hidden behind the assignment
wrapper, whose ControlInfo once claimed `reassigns = {}`. Lean threads mutable
locals through branch joins from that set, so the branch's write was silently
discarded after the `if`. These variants place the write inside a branch. -/
procedure branch_local_indexed_update {
  let mut m := fun _ : Bool => false
  if x then
    m true := true
  return (m false, m true)
}

procedure branch_local_indexed_arrow_update {
  let mut m := fun _ : Bool => false
  if x then
    m true ← pure true
  return (m false, m true)
}

/- The arrow target and the mutation in its RHS are both application-shaped,
so control-info inference recursively crosses two assignment wrappers. -/
procedure nested_wrapped_mutation_inside_arrow_rhs {
  let mut outer := fun _ : Bool => false
  let mut inner := fun _ : Bool => false
  if x then
    outer true ← do
      inner true := true
      pure true
  return (outer false, outer true, inner false, inner true)
}

/- Havoc of a local is a reassignment, so the havoc statement's ControlInfo
must report it, or the branch's havoc is lost at the join (as above). -/
procedure branch_local_havoc {
  let mut v := false
  if x then
    v := *
  return v
}

procedure quoted_assignment_is_untouched {
  let _ : True := by
    run_tac
      let quoted ← `(doElem| r true := true)
      unless quoted.raw.getKind == ``Lean.Parser.Term.doReassign do
        throwError "Veil rewrote reassignment syntax inside a quotation"
      let quotedDo ← `(term| do pure ())
      unless quotedDo.raw.getKind == ``Lean.Parser.Term.do do
        throwError "Veil rejected or rewrote a term-level `do` inside a quotation"
    trivial
  return true
}

procedure assertion_allocation_probe (input : Option Bool) {
  match input with
  | some value => assert value = value
  | none => assert True
  assert x = x
  return y
}

def initial : State FieldConcreteType := {
  x := true
  y := 0
  tmp := 9
  r := fun _ => false
}

def matchResult := __veil_exec_action% {} {} initial match_state_field
#guard exactlyOneSuccess matchResult fun value state =>
  value == 1 && state.x && state.y == 1 && !(state.r : Bool → Bool) true

def localMatchResult :=
  __veil_exec_action% {} {} initial match_local_derived_from_state
#guard exactlyOneSuccess localMatchResult fun value state =>
  value == 3 && state.x && state.y == 3 && !(state.r : Bool → Bool) true

def macroResult := __veil_exec_action% {} {} initial macro_generated_write
#guard exactlyOneSuccess macroResult fun value state =>
  value && (state.r : Bool → Bool) true && state.x && state.y == 0

def straightMacroResult :=
  __veil_exec_action% {} {} initial macro_generated_write_straight
#guard exactlyOneSuccess straightMacroResult fun value state =>
  value && (state.r : Bool → Bool) true && state.x && state.y == 0

def macroLocalResult :=
  __veil_exec_action% {} {} initial macro_local_reassignment_is_hygienic
#guard exactlyOneSuccess macroLocalResult fun value state =>
  value == 0 && state.x && state.y == 0 && state.tmp == 9 &&
    !(state.r : Bool → Bool) true

def tupleResult := __veil_exec_action% {} {} initial tuple_reassignment
#guard exactlyOneSuccess tupleResult fun value state =>
  value == (2, 1) && state.x && state.y == 0

def localFunctionResult :=
  __veil_exec_action% {} {} initial local_function_point_update
#guard exactlyOneSuccess localFunctionResult fun value state =>
  value == (false, true) && state.x && state.y == 0

def localFunctionArrowResult :=
  __veil_exec_action% {} {} initial local_function_point_arrow_update
#guard exactlyOneSuccess localFunctionArrowResult fun value state =>
  value == (false, true) && state.x && state.y == 0

def branchLocalFunctionResult :=
  __veil_exec_action% {} {} initial branch_local_indexed_update
#guard exactlyOneSuccess branchLocalFunctionResult fun value state =>
  value == (false, true) && state.x && state.y == 0

def branchLocalFunctionArrowResult :=
  __veil_exec_action% {} {} initial branch_local_indexed_arrow_update
#guard exactlyOneSuccess branchLocalFunctionArrowResult fun value state =>
  value == (false, true) && state.x && state.y == 0

def nestedWrappedMutationResult :=
  __veil_exec_action% {} {} initial nested_wrapped_mutation_inside_arrow_rhs
#guard exactlyOneSuccess nestedWrappedMutationResult fun value state =>
  value == (false, true, false, true) && state.x && state.y == 0

def branchLocalHavocResult :=
  __veil_exec_action% {} {} initial branch_local_havoc
#guard exactlyNSuccesses 2 branchLocalHavocResult fun _ state =>
  state.x && state.y == 0
#guard hasSuccess branchLocalHavocResult fun value _ => value
#guard hasSuccess branchLocalHavocResult fun value _ => !value

def quotationResult :=
  __veil_exec_action% {} {} initial quoted_assignment_is_untouched
#guard exactlyOneSuccess quotationResult fun value state =>
  value && state.x && state.y == 0

/- Simulate a postponed action continuation resuming while an unrelated
action's dynamic context is installed. Its lexical action marker must win. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let mod ← Veil.getCurrentModule
  let actionCtx : Veil.Action.DoElab.Context := {
    mod
    proc := `context_recovery_probe
    monad := mkConst ``Id
  }
  Veil.Action.DoElab.withVeilDoContext actionCtx do
    let actionLCtx ← getLCtx
    let actionInstances ← getLocalInstances
    let unrelatedCtx : Veil.Action.DoElab.Context := {
      mod
      proc := `unrelated_action
      monad := mkConst ``Id
    }
    Veil.Action.DoElab.withVeilDoContext unrelatedCtx do
      withLCtx actionLCtx actionInstances do
        let some recovered ← Veil.Action.DoElab.currentVeilControlContext?
          | throwError "failed to recover the lexical Veil action context"
        unless recovered.proc == actionCtx.proc do
          throwError "an unrelated dynamic context overrode the lexical action continuation"

/- Match elaboration duplicates/postpones continuations.  Assertion allocation
must nevertheless leave exactly one source record for each source statement. -/
run_cmd do
  let assertions := (← Veil.globalEnv.get).assertions
  let mut probeAssertions : Array Veil.Assertion := #[]
  for (_, assertion) in assertions.find do
    if assertion.ctx.module == `ActionExecutionRegressionCoverage &&
        assertion.ctx.procedure == `assertion_allocation_probe then
      probeAssertions := probeAssertions.push assertion
  unless probeAssertions.size == 3 do
    throwError "expected three stable assertion IDs, found {probeAssertions.size}"
  let positions := probeAssertions.filterMap (·.ctx.stx.getPos?)
  unless positions.size == 3 && positions[0]! != positions[1]! &&
      positions[0]! != positions[2]! && positions[1]! != positions[2]! do
    throwError "assertion retry/postponement duplicated a source location"

end ActionExecutionRegressionCoverage
