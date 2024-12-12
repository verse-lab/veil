import Lean
import LeanSts.MetaUtil
import LeanSts.DSL.Lang

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

structure StatePredicate where
  name : Name
  /-- DSL expression for this predicate -/
  lang : Option (TSyntax `lang)
  /-- Lean `Expr` for this predicate; this is usually a constant in the
  environment, *without* having applied the section variables. -/
  expr : Expr
deriving Inhabited, BEq

instance : ToString StatePredicate where
  toString sp := match sp.lang with
    | some lang => s!"{sp.name} : {lang}"
    | none => s!"{sp.name} : {sp.expr}"

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
  init       : StatePredicate
deriving Inhabited

#check DSLSpecification
