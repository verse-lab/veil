module

public meta import Veil.Frontend.DSL.Module.Util

public meta section
namespace Veil
open Lean Elab Term Meta

/-- Generated connectives must resolve to global constants even when a query
binds a name such as `And`, `Or`, `True`, or `False`. -/
def combineTraceTerms (op neutral : Name) (operands : Array Term) : TermElabM Term := do
  if operands.isEmpty then return ⟨(mkCIdent neutral).raw⟩
  let last := operands.size - 1
  operands[0:last].foldrM (init := operands[last]!) fun operand acc =>
    `(term| $(mkCIdent op) $operand $acc)

open Lean.Parser.Term in
/-- Convert a bracketed binder to an explicit binder for use in existential quantification -/
def toExplicitBindersForExists (stx : TSyntax `Lean.Parser.Term.bracketedBinder)
    : TermElabM (TSyntax `Lean.bracketedExplicitBinders) := do
  match stx with
  | `(bracketedBinder| ($id:ident : $tp)) | `(bracketedBinder| {$id:ident : $tp})
  | `(bracketedBinder| [$id:ident : $tp]) =>
    `(bracketedExplicitBinders| ($(identToBinderIdent id) : $tp))
  | `(bracketedBinder| [$tp]) =>
    let freshId := mkIdent (← mkFreshUserName `inst)
    `(bracketedExplicitBinders| ($(identToBinderIdent freshId) : $tp))
  | _ => throwError s!"toExplicitBindersForExists: unexpected syntax: {stx}"

/-- A pair of bracketed and explicit binders that are always created together -/
abbrev BinderPair := TSyntax `Lean.Parser.Term.bracketedBinder × TSyntax `Lean.bracketedExplicitBinders

/-- Create both bracketed and explicit binders for an identifier with type -/
def mkBinderPair (id : Ident) (ty : Term) : TermElabM BinderPair := do
  return (← `(bracketedBinder| ($id : $ty)),
          ← `(bracketedExplicitBinders| ($(identToBinderIdent id) : $ty)))

/-- Instantiate a parameter type with its preceding telescope. Application
arguments stay outside the telescope's scope, even when a query variable has
the same name as an action parameter. -/
def instantiateParamType (ty : Term) (params : Array Parameter)
    (args : Array Term) : TermElabM Term := do
  if params.isEmpty then return ty
  let binders ← params.mapM fun p => p.binder >>= bracketedBinderToFunBinder
  let fn ← mkFunSyntax binders ty
  `(term| ($fn) $args*)

/-- Create parameter binders with unique names for a transition. -/
def mkParamBinders (params : Array Parameter) (prefix_ : String)
    : TermElabM (Array Ident × Array BinderPair) := do
  let mut args : Array Term := #[]
  let mut ids := #[]
  let mut binders := #[]
  for idx in [:params.size] do
    let p := params[idx]!
    let uniqueId := mkIdent $ Name.mkSimple s!"{prefix_}_arg{idx}_{p.name}"
    let ty ← instantiateParamType p.type (params.extract 0 idx) args
    binders := binders.push (← mkBinderPair uniqueId ty)
    ids := ids.push uniqueId
    args := args.push (← `(term| $uniqueId))
  return (ids, binders)

/-- Build the transition expression: `tag = tagMember ∧ rts.tr th st label st'` -/
def mkTransitionExpr (rtsExpr theoryId currState nextState : TSyntax `term)
    (tagId : Ident) (actionName : Name) (args : Array Term) : TermElabM (TSyntax `term) := do
  let actionTagMember := mkIdent $ actionTagEnumInstName ++ actionName
  let labelConstructor := mkIdent $ labelTypeName ++ actionName
  let labelExpr ← `(term| ($labelConstructor $args*))
  let trExpr ← `(term| (($rtsExpr).$(mkIdent `tr) $theoryId $currState $labelExpr $nextState))
  `(term| ($tagId = $actionTagMember ∧ $trExpr))

/-- Build a disjunction representing any action transition with ActionTag constraint -/
def mkAnyActionDisjunction (mod : Module) (rtsExpr theoryId currState nextState : TSyntax `term)
    (tagId : Ident) (trIdx : Nat) (prefix_ : Option String := none) : TermElabM (TSyntax `term × Array BinderPair) := do
  let results ← mod.actions.mapM fun act => do
    let (_, specificParams) ← mod.declarationAllParams act.name act.declarationKind
    let (argIdents, binders) ← mkParamBinders specificParams s!"{prefix_.getD s!"_tr{trIdx}_act"}_{act.name}"
    return (← mkTransitionExpr rtsExpr theoryId currState nextState tagId act.name (argIdents.map (⟨·.raw⟩)), binders)
  return (← combineTraceTerms ``Or ``False (results.map (·.1)), results.flatMap (·.2))

/-- Collect module-level binders (sorts, user parameters, sort assumptions, user-defined typeclasses) -/
def collectModuleBinders (mod : Module) : TermElabM (Array BinderPair) := do
  let sortBinders ← mod.uninterpretedParamBinders
  let typeclassParams := mod.parameters.filter fun p =>
    match p.kind with
    | .moduleTypeclass .sortAssumption | .moduleTypeclass .userDefined => true
    | _ => false
  let typeclassBinders ← typeclassParams.mapM (·.binder)
  let allBinders := sortBinders ++ typeclassBinders
  allBinders.mapM fun b => do return (b, ← toExplicitBindersForExists b)

/-- Create ActionTag type and enum binders -/
def mkActionTagBinders : TermElabM (Array BinderPair) := do
  let typePair ← mkBinderPair actionTagType (← `(term| Type))
  let actionTagEnumClass := Ident.toEnumClass actionTagType
  let enumBinder ← `(bracketedBinder| ($actionTagEnumInst : $actionTagEnumClass $actionTagType))
  let enumExplicit ← `(bracketedExplicitBinders| ($(identToBinderIdent actionTagEnumInst) : $actionTagEnumClass $actionTagType))
  return #[typePair, (enumBinder, enumExplicit)]


end Veil
