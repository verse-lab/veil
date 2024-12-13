import Lean
import LeanSts.IOAutomata
import LeanSts.DSL.Lang
import LeanSts.MetaUtil

open Lean Parser

inductive StateComponentKind where
  | individual
  | relation
  | function
deriving Inhabited

instance : ToString StateComponentKind where
  toString
    | StateComponentKind.individual => "individual"
    | StateComponentKind.relation => "relation"
    | StateComponentKind.function => "function"

inductive StateComponentType where
  /-- e.g. `Int -> vertex -> Prop` -/
  | simple (t : TSyntax ``Command.structSimpleBinder)
  /-- e.g. `(r : Int) (v : vertex)` and `Prop` -/
  | complex (binders : TSyntaxArray ``Term.bracketedBinder) (dom : TSyntax `term)
deriving Inhabited

instance : ToString StateComponentType where
  toString
    | StateComponentType.simple t => toString t
    | StateComponentType.complex b d  => s!"{b} : {d}"

structure StateComponent where
  /-- Is this an `individual`, a `relation`, or ` function`?-/
  kind : StateComponentKind
  name : Name
  /-- The Lean syntax that declares the type of this state component -/
  type : StateComponentType
deriving Inhabited

instance : ToString StateComponent where
  toString sc := s!"{sc.kind} {sc.name} {sc.type}"

def StateComponent.getSimpleBinder (sc : StateComponent) : CoreM (TSyntax ``Command.structSimpleBinder) := do
  match sc.type with
  | .simple t => return t
  | .complex b d => return ← complexBinderToSimpleBinder (mkIdent sc.name) b d

def StateComponent.stx (sc : StateComponent) : CoreM Syntax := sc.getSimpleBinder

structure StateSpecification where
  name : Name
  /-- DSL expression for this predicate -/
  lang : Option (TSyntax `lang)
  /-- Lean `Expr` for this predicate; this is usually a constant in the
  environment, *without* having applied the section variables. -/
  expr : Expr
deriving Inhabited, BEq

instance : ToString StateSpecification where
  toString sp := match sp.lang with
    | some lang => s!"{sp.name} : {lang}"
    | none => s!"{sp.name} : {sp.expr}"

structure ActionSpecification where
  decl : IOAutomata.ActionDeclaration
  /-- DSL expression for this action -/
  lang : Option (TSyntax `lang)
  /-- Lean `Expr` for this predicate; this is usually a constant in the
  environment, *without* having applied the section variables. -/
  expr : Expr
deriving Inhabited, BEq

instance : ToString ActionSpecification where
  toString a := match a.lang with
    | some lang => s!"{a.decl.type} {a.decl.name} [defined via lang] {lang}"
    | none => s!"{a.decl.type} {a.decl.name} [defined via expr] {a.expr}"

/-- Make an action specification without any DSL-specific information. -/
def ActionSpecification.mkPlain (type : IOAutomata.ActionType) (name : Name) (expr : Expr) : ActionSpecification := {
  decl := { type := type, name := name, ctor := none },
  lang := none,
  expr := expr
}

/-- Enhance a given `ActionSpecification` with DSL-specific information. -/
def ActionSpecification.addDSLInfo (a : ActionSpecification) (lang : TSyntax `lang) (ctor : TSyntax `Lean.Parser.Command.ctor) : ActionSpecification :=
  { a with lang := some lang, decl := { a.decl with ctor := some ctor } }

def ActionSpecification.name (a : ActionSpecification) : Name := a.decl.name
def ActionSpecification.label (a : ActionSpecification) : IOAutomata.ActionLabel Name := a.decl.label

/-- These mean the same thing, but `safety` is as a convention used to
denote the main, top-level properties of the system, whereas `invariant`
clauses are supporting the main safety property. -/
inductive StateAssertionKind
  | invariant
  | safety
deriving BEq

instance : Inhabited StateAssertionKind where
  default := StateAssertionKind.invariant

instance : ToString StateAssertionKind where
  toString
    | StateAssertionKind.invariant => "invariant"
    | StateAssertionKind.safety => "safety"

structure StateAssertion where
  kind : StateAssertionKind
  name : Name
  /-- Lean term for this predicate -/
  term : Option (TSyntax `term)
  /-- Lean `Expr` for this predicate; this is usually a constant in the
  environment, *without* having applied the section variables. -/
  expr : Expr
deriving Inhabited, BEq

instance : ToString StateAssertion where
  toString sa := match sa.term with
    | some term => s!"{sa.kind} [{sa.name}] {term}"
    | none => s!"{sa.kind} [{sa.name}] {sa.expr}"

/-- A cleaned-up version of `StsState`, this gets generated on `#gen_spec` and stored in the global state. -/
structure DSLSpecification where
  /-- Name of the specification -/
  name        : Name
  /-- Expression representing the type of the transition system state,
  *without* having applied the section variables. -/
  stateType   : Expr
  /-- Signatures of all constants, relations, and functions that compose
  the state. This basically defines a FOL signature. -/
  signature  : Array StateComponent
  /-- Initial state predicate -/
  init        : StateSpecification
  /-- Transitions of the system -/
  transitions : Array ActionSpecification
  /-- Invariants -/
  invariants  : Array StateAssertion
deriving Inhabited

/-- Every DSL-specified transition gets a 'constructor' that corresponds
to the transition's signature. This is used to build up a `Label` type
for this specification, which encodes its IO Automata signature. -/
def DSLSpecification.transitionCtors (spec : DSLSpecification) : CoreM (Array (TSyntax `Lean.Parser.Command.ctor)) := do
  spec.transitions.mapM (fun t => do match t.decl.ctor with
    | some ctor => return ctor
    | none => throwError "DSL: missing constructor for transition {t.decl.name}")

instance : ToString DSLSpecification where
  toString spec := s!"DSLSpecification {spec.name}"
