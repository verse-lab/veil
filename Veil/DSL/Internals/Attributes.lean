import Lean
import Veil.DSL.Internals.StateExtensions

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
    let stsTp := (<- localSpecCtx.get).spec.generic.stateType
    unless stsTp == default do
      throwError "State type has already been declared: {stsTp}"
    let ty := mkConst declName
    localSpecCtx.modify (fun s => { s with spec.generic := {s.spec.generic with stateType := ty }})
}

syntax (name:= reader) "readerDef" : attr
initialize registerBuiltinAttribute {
  name := `reader
  descr := "This is the reader type"
  add := fun declName _ _ => do
    let rdsTp := (<- localSpecCtx.get).spec.generic.readerType
    unless rdsTp == default do
      throwError "Reader type has already been declared: {rdsTp}"
    let ty := mkConst declName
    localSpecCtx.modify (fun s => { s with spec.generic := {s.spec.generic with readerType := ty }})
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
def toActionAttribute (type : ActionKind) : AttrM (TSyntax `Lean.Parser.Term.attrInstance) :=
  match type with
  | .internal => `(attrInstance|internalActDef)
  | .input => `(attrInstance|inputActDef)
  | .output => `(attrInstance|outputActDef)

open Lean.Parser.Term in
def toActionAttribute' (type : ActionKind) : Lean.Elab.Attribute :=
  match type with
  | .internal => {name := `internalActDef}
  | .input => {name := `inputActDef}
  | .output => {name := `outputActDef}

def declareProcedure [Monad m] [MonadEnv m] [MonadError m] (actT : Option ActionKind)  (declName : Name) : m Unit := do
  let procedureExists := (← localSpecCtx.get).spec.procedures.any fun t => t.name == declName
  if procedureExists then
    throwError "A procedure or action named {declName} has already been declared!"
  let spec := match actT with
    | some actT => ActionSpecification.mkPlain actT declName (mkConst declName)
    | none => ProcedureSpecification.mkPlain declName (mkConst declName)
  localSpecCtx.modify (fun s => { s with spec := {s.spec with procedures := s.spec.procedures.push spec }})

syntax (name:= assumption) "assumptionDef" : attr
initialize registerBuiltinAttribute {
  name := `assumption
  descr := "This is an assumption clause"
  add := fun declName _ _ => do
    let prop := { kind := .assumption, name := declName, term := none, expr := mkConst declName }
    localSpecCtx.modify (fun s => { s with spec := {s.spec with assumptions := s.spec.assumptions.push prop}})
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
