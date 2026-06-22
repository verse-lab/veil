import Lean
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Names
import Veil.Frontend.DSL.Module.Syntax
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Frontend.DSL.Module.Util.Basic

namespace Veil

open Lean Meta Elab

private partial def Module.findDeclarationPrefix? (mod : Module) (name : Name) : Option (Name × DeclarationKind) :=
  match mod._declarations[name]? with
  | some k => some (name, k)
  | none =>
    match name with
    | .anonymous => none
    | .str parent _ => mod.findDeclarationPrefix? parent
    | .num parent _ => mod.findDeclarationPrefix? parent

private def Module.stripNamespacePrefix (mod : Module) (name : Name) : Name :=
  if mod.name.isPrefixOf name then
    name.replacePrefix mod.name .anonymous
  else
    name

/-
TODO: Replace this temporary ambient-theory path with a proper declaration
parameter-layout query. `veil_term%` currently looks in the local context for a
theory value, tries to elaborate `@decl moduleArgs* th`, and falls back to
`@decl moduleArgs*`; the delaborator mirrors this by recognizing the hidden
argument from the fvar/type shape. This should instead be driven by the
declaration's parameter layout, including generated `.theoryArg`/`.stateArg`
binders for assertions, temporal properties, and assembled definitions.
-/
open Term in
private def findAmbientTheoryIdent? : TermElabM (Option Ident) := do
  let theoryTy ← instantiateMVars (← elabTerm (mkIdent environmentTheoryName) none)
  let mut candidates := #[]
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then
      continue
    let s ← saveState
    let ok ← try
      Meta.isDefEq (← instantiateMVars ldecl.type) theoryTy
    catch _ =>
      pure false
    s.restore
    if ok then
      let id := mkIdent ldecl.userName
      if ldecl.userName == `th then
        return some id
      candidates := candidates.push id
  if candidates.size == 1 then
    return candidates[0]?
  return none

open Term in
private def elabVeilTermWithOptionalTheory
    (id : Ident)
    (modArgs : Array Term)
    (expectedType : Option Expr) : TermElabM Expr := do
  let baseTerm ← `(@$id $modArgs*)
  let start ← saveState
  if let some thId ← findAmbientTheoryIdent? then
    let theoryTerm ← `(@$id $modArgs* $thId)
    try
      return ← elabTerm theoryTerm expectedType
    catch _ =>
      start.restore
  elabTerm baseTerm expectedType

open Term in
/-- Elaborate `veil_term% decl` by resolving `decl` in the current Veil module,
inserting hidden module parameters, and trying the ambient theory value when
the declaration accepts one. -/
@[term_elab kw_veil_term]
def elabVeilTerm : TermElab := fun stx expectedType => do
  let mod ← getCurrentModule (errMsg := "veil_term% must be inside a Veil module!")
  let id ← match stx with
    | `(veil_term% $i:ident) => pure i
    | _ => throwUnsupportedSyntax
  let name := id.getId.eraseMacroScopes
  let (paramSourceName, declarationKind) ← match mod.findDeclarationPrefix? name with
    | some found => pure found
    | none => throwError "veil_term%: declaration {name} was not found in module {mod.name}"
  let ((_, modArgs), _) ← mod.declarationSplitBindersArgs paramSourceName declarationKind
  elabVeilTermWithOptionalTheory id modArgs expectedType

/-- Expand `veil_tr% act` to the ordinary `veil_term% act.ext.tr` form. -/
macro_rules
  | `(veil_tr% $i:ident) => do
    let trId := mkIdent <| toTransitionName <| toExtName i.getId.eraseMacroScopes
    `(veil_term% $trId:ident)

open PrettyPrinter.Delaborator SubExpr in
private def isAmbientTheoryArg (arg : Expr) : DelabM Bool := do
  let .fvar argFVarId := arg
    | return false
  let argDecl ← argFVarId.getDecl
  let .fvar typeFVarId := argDecl.type
    | return false
  let typeDecl ← typeFVarId.getDecl
  return typeDecl.userName == environmentTheoryName

private def transitionActionName? : Name → Option Name
  | .str (.str act "ext") "tr" => some act
  | _ => none

open PrettyPrinter.Delaborator SubExpr in
/-- Delaborate Veil module declarations back to `veil_term% decl`, hiding module
parameters and an ambient theory argument. Transition definitions of the shape
`act.ext.tr` are printed as `veil_tr% act`. -/
@[delab app]
def delabVeilTerm : Delab := do
  let some mod := (← localEnv.get).currentModule
    | failure
  let e ← getExpr
  let .const fullName _ := e.getAppFn
    | failure
  let name := mod.stripNamespacePrefix fullName.eraseMacroScopes
  let (paramSourceName, declarationKind) ← match mod.findDeclarationPrefix? name with
    | some found => pure found
    | none => failure
  let ((_, modArgs), _) ← mod.declarationSplitBindersArgs paramSourceName declarationKind
  let args := e.getAppArgs
  unless modArgs.size ≤ args.size do
    failure
  let head ← match transitionActionName? name with
    | some act => `(veil_tr% $(mkIdent act))
    | none => `(veil_term% $(mkIdent name))
  let mut argStxs := #[]
  for i in [modArgs.size:args.size] do
    if i == modArgs.size && (← isAmbientTheoryArg args[i]!) then
      continue
    argStxs := argStxs.push (← withNaryArg i delab)
  annotateTermInfo <| Syntax.mkApp head argStxs

end Veil
