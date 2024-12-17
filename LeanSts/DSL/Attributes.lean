import Lean
import LeanSts.DSL.StateExtensions

open Lean

/-! ## Attributes

  If you have an existing Lean specification that is not defined in our
  DSL, but would like to make it legible to the DSL (e.g. to run
  `#check_invariants` or use the `unsat trace` bounded model checking
  functionality), you can annotate the relevant parts of your
  specification with the following attributes to make it inter-operable
  with our DSL functionality.

  These attributes populate that our `LocalSpecificationCtx` and
  `GlobalSpecificationCtx` with the relevant information extracted from
  your non-DSL specification.
 -/

syntax (name:= state) "stateDef" : attr
initialize registerBuiltinAttribute {
  name := `state
  descr := "This is the state type"
  add := fun declName _ _ => do
    let stsTp := (<- localSpecCtx.get).spec.stateType
    unless stsTp == default do
      throwError "State type has already been declared: {stsTp}"
    let ty := mkConst declName
    localSpecCtx.modify (fun s => { s with spec := {s.spec with stateType := ty }})
}

syntax (name:= initial) "initDef" : attr
initialize registerBuiltinAttribute {
  name := `initial
  descr := "This is the initial state predicate"
  add := fun declName _ _ => do
    let intTp := (<- localSpecCtx.get).spec.init
    unless intTp == default do
      throwError "Initial state predicate has already been declared!"
    let init := { name := declName, lang := none, expr := mkConst declName }
    localSpecCtx.modify (fun s => { s with spec := {s.spec with init := init }})
}

syntax (name:= internalActDef) "internalActDef" : attr
syntax (name:= inputActDef) "inputActDef" : attr
syntax (name:= outputActDef) "outputActDef" : attr

open Lean.Parser.Term in
def toActionAttribute (type : IOAutomata.ActionType) : AttrM (TSyntax `Lean.Parser.Term.attrInstance) :=
  match type with
  | .internal => `(attrInstance|internalActDef)
  | .input => `(attrInstance|inputActDef)
  | .output => `(attrInstance|outputActDef)

def addAction (type : IOAutomata.ActionType) (declName : Name) : Syntax → AttributeKind → AttrM Unit :=
  fun _ _ => do
    let spec := ActionSpecification.mkPlain type declName (mkConst declName)
    localSpecCtx.modify (fun s => { s with spec := {s.spec with transitions := s.spec.transitions.push spec }})

initialize registerBuiltinAttribute {
  name := `internalActDef
  descr := "This is an internal transition"
  add := addAction .internal
}
initialize registerBuiltinAttribute {
  name := `inputActDef
  descr := "This is an input transition"
  add := addAction .input
}

initialize registerBuiltinAttribute {
  name := `outputActDef
  descr := "This is an output transition"
  add := addAction .output
}

syntax (name:= inv) "invDef" : attr
initialize registerBuiltinAttribute {
  name := `inv
  descr := "This is an invariant clause"
  add := fun declName _ _ => do
    let prop := { kind := .invariant, name := declName, term := none, expr := mkConst declName }
    localSpecCtx.modify (fun s => { s with spec := {s.spec with invariants := s.spec.invariants.push prop}})
}

syntax (name:= safe) "safeDef" : attr
initialize registerBuiltinAttribute {
  name := `safe
  descr := "This is a safety property"
  add := fun declName _ _ => do
    let prop := { kind := .safety, name := declName, term := none, expr := mkConst declName }
    localSpecCtx.modify (fun s => { s with spec := {s.spec with invariants := s.spec.invariants.push prop}})
}

/- For `solve_by_elim` -/
syntax (name := invProof) "invProof" : attr

initialize registerBuiltinAttribute {
  name := `invProof
  descr := "This is a proof that an invariant clause is preserved by an
  action assuming the conjunction of all invariant clauses"
  add := fun declName _ _ => do
    localSpecCtx.modify (fun s => { s with establishedClauses := s.establishedClauses ++ [declName]})
}
