import VeilTest.ActionExecution

/-!
Concrete tests for the state-assignment compiler.  The observations include
untouched entries, so these tests catch updates that accidentally replace a
whole field instead of just the selected slice.
-/

set_option linter.unusedVariables false

open VeilTest.ActionExecution

veil module ActionExecutionUpdates

relation rel : Bool → Bool → Bool
function funField : Bool → Bool
-- The explicit binder keeps the function-valued codomain out of the field's
-- represented domain, exercising assignment's codomain-residue path.
function table (key : Bool) : Bool → Nat
individual marker : Bool

veil_set_field_representation relation Veil.CanonicalField
veil_set_field_representation function Veil.CanonicalField

#gen_state

open scoped ActionExecutionUpdates

procedure whole_component_write {
  rel := fun a b => a && b
  funField := fun a => !a
}

procedure indexed_write {
  rel true false := true
  funField false := true
}

procedure universal_write {
  rel true N := N
}

procedure write_function_residue {
  table true false := 9
  return table true false
}

procedure produce_for_arrow {
  marker := true
  return false
}

procedure arrow_write_then_read {
  funField true ← produce_for_arrow
  rel true false := marker
  return funField true
}

procedure fixed_havoc {
  rel true false := *
  return rel true false
}

-- Omitted dimensions are part of the function selected by havoc.
procedure omitted_dimension_havoc {
  rel true := *
}

-- An explicit capitalized dimension has the same narrowed pick domain.
procedure universal_dimension_havoc {
  rel true N := *
}

def initial : State FieldConcreteType := {
  rel := fun a b => a && !b
  funField := fun a => a
  table := fun a b => if a then (if b then 3 else 2) else (if b then 1 else 0)
  marker := false
}

def readRel (state : State FieldConcreteType) : Bool → Bool → Bool :=
  (state.rel : Bool → Bool → Bool)

def readFunField (state : State FieldConcreteType) : Bool → Bool :=
  (state.funField : Bool → Bool)

def readTable (state : State FieldConcreteType) : Bool → Bool → Nat :=
  (state.table : Bool → Bool → Nat)

def wholeResult := __veil_exec_action% {} {} initial whole_component_write
#guard exactlyOneSuccess wholeResult fun _ state =>
  let rel := readRel state
  let funField := readFunField state
  let table := readTable state
  !rel false false && !rel false true &&
  !rel true false && rel true true &&
  funField false && !funField true &&
  table false false == 0 && table false true == 1 &&
  table true false == 2 && table true true == 3 && !state.marker

def indexedResult := __veil_exec_action% {} {} initial indexed_write
#guard exactlyOneSuccess indexedResult fun _ state =>
  let rel := readRel state
  let initialRel := readRel initial
  let funField := readFunField state
  let initialFunField := readFunField initial
  rel false false == initialRel false false &&
  rel false true == initialRel false true &&
  rel true false && rel true true == initialRel true true &&
  funField false && funField true == initialFunField true &&
  readTable state false false == readTable initial false false &&
  readTable state true true == readTable initial true true

def universalResult := __veil_exec_action% {} {} initial universal_write
#guard exactlyOneSuccess universalResult fun _ state =>
  let rel := readRel state
  let initialRel := readRel initial
  rel false false == initialRel false false &&
  rel false true == initialRel false true &&
  !rel true false && rel true true

def residueResult := __veil_exec_action% {} {} initial write_function_residue
#guard exactlyOneSuccess residueResult fun value state =>
  let table := readTable state
  value == 9 && table true false == 9 && table true true == 3 &&
  table false false == 0 && table false true == 1 &&
  readRel state false false == readRel initial false false

def arrowResult := __veil_exec_action% {} {} initial arrow_write_then_read
#guard exactlyOneSuccess arrowResult fun value state =>
  !value && state.marker && !readFunField state true &&
  readFunField state false == readFunField initial false &&
  readRel state true false

def fixedHavocResult := __veil_exec_action% {} {} initial fixed_havoc
#guard exactlyNSuccesses 2 fixedHavocResult fun value state =>
  let rel := readRel state
  value == rel true false && rel true true == readRel initial true true &&
  rel false false == readRel initial false false &&
  rel false true == readRel initial false true
#guard hasSuccess fixedHavocResult fun value state =>
  !value && !readRel state true false
#guard hasSuccess fixedHavocResult fun value state =>
  value && readRel state true false

def omittedHavocResult :=
  __veil_exec_action% {} {} initial omitted_dimension_havoc
#guard exactlyNSuccesses 4 omittedHavocResult fun _ state =>
  readRel state false false == readRel initial false false &&
  readRel state false true == readRel initial false true
#guard hasSuccess omittedHavocResult fun _ state =>
  !readRel state true false && !readRel state true true
#guard hasSuccess omittedHavocResult fun _ state =>
  !readRel state true false && readRel state true true
#guard hasSuccess omittedHavocResult fun _ state =>
  readRel state true false && !readRel state true true
#guard hasSuccess omittedHavocResult fun _ state =>
  readRel state true false && readRel state true true

def universalHavocResult :=
  __veil_exec_action% {} {} initial universal_dimension_havoc
#guard exactlyNSuccesses 4 universalHavocResult fun _ state =>
  readRel state false false == readRel initial false false &&
  readRel state false true == readRel initial false true
#guard hasSuccess universalHavocResult fun _ state =>
  !readRel state true false && !readRel state true true
#guard hasSuccess universalHavocResult fun _ state =>
  !readRel state true false && readRel state true true
#guard hasSuccess universalHavocResult fun _ state =>
  readRel state true false && !readRel state true true
#guard hasSuccess universalHavocResult fun _ state =>
  readRel state true false && readRel state true true

end ActionExecutionUpdates

/-!
The same indexed/universal update behavior through the default concrete field
representation.  Assertions observe the abstract relation via
`FieldRepresentation.get`, not the backing tree-set representation.
-/

veil module ActionExecutionDefaultRepresentation

relation rel : Bool → Bool → Bool
individual marker : Bool
individual atFF : Bool
individual atFT : Bool
individual atTF : Bool
individual atTT : Bool

#gen_state

open scoped ActionExecutionDefaultRepresentation

procedure update_default_representation {
  rel true false := true
  rel false N := N
  marker := rel true false
  atFF := rel false false
  atFT := rel false true
  atTF := rel true false
  atTT := rel true true
}

def initial : State FieldConcreteType := default
def result := __veil_exec_action% {} {} initial update_default_representation

#guard exactlyOneSuccess result fun _ state =>
  state.marker && !state.atFF && state.atFT && state.atTF && !state.atTT

end ActionExecutionDefaultRepresentation
