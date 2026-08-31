import Lean.Elab.BuiltinDo
import Veil.Frontend.DSL.Action.Semantics.WP
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Frontend.DSL.Module.Util

open Lean Elab Term Meta Lean.Parser
open Lean.Elab.Do

/-! ## Action identity and handler gating -/

namespace Veil
namespace Action.DoElab

/-- Scoped information needed by Veil's extensible-`do` handlers.

This cannot be threaded as a `ReaderT Context` layer: the handlers are
invoked by Lean's `do`-elaborator through globally registered attributes
(`@[doElem_elab]`, `@[doElem_control_info]`) whose signatures fix the monad,
and Lean postpones parts of the body as synthetic metavariables that resume
*after* the entry point has returned, outliving any reader scope. Hence the
two mechanisms below: a rollback-safe environment extension for the dynamic
scope, and a lexical local-context marker that survives inside captured
continuations. -/
structure Context where
  mod : Module
  proc : Name
  monad : Expr
  parameters : FVarIdSet := {}

initialize contextExt : SimpleScopedEnvExtension (Option Context) (Option Context) ←
  registerSimpleScopedEnvExtension {
    initial := none
    addEntry := fun _ new => new
  }

private def actionBodyMarkerPrefix : Name := `__veil_action_body

private def actionBodyMarker (proc : Name) : Name :=
  Name.append actionBodyMarkerPrefix proc

private def withContextEntry (ctx : Context) (x : TermElabM α) : TermElabM α := do
  let old ← contextExt.get
  contextExt.modify fun _ => some ctx
  try x
  finally contextExt.modify fun _ => old

/-- Install a Veil action context while preserving environment changes made by
the elaboration itself (notably assertion allocation). -/
def withVeilDoContext (ctx : Context) (x : TermElabM α) : TermElabM α := do
  /- The environment entry is rollback-safe, while the lexical marker remains
  in the local context captured by continuations that Lean postpones until
  after this call has returned. -/
  withLocalDecl (actionBodyMarker ctx.proc) .default (mkConst ``Unit)
      (kind := .implDetail) fun _ => do
    withContextEntry ctx x

def currentVeilDoContext [Monad m] [MonadEnv m] : m (Option Context) :=
  contextExt.get

/-- The procedure name recorded by the innermost action-body marker in the
local context, if any. -/
private def lexicalProcName? [Monad m] [MonadLCtx m] : m (Option Name) := do
  let marker? : Option (Option Name) := (← getLCtx).findDeclRev? fun decl =>
    let name := decl.userName
    if actionBodyMarkerPrefix.isPrefixOf name && name != actionBodyMarkerPrefix then
      some (some (name.replacePrefix actionBodyMarkerPrefix .anonymous))
    else
      none
  return marker?.join

private def recoverVeilContext? [Monad m] [MonadEnv m] [MonadLCtx m] [MonadError m]
    (fallbackMonad : m Expr) : m (Option Context) := do
  let dynamic? ← currentVeilDoContext
  let some proc ← lexicalProcName? | return dynamic?
  if let some ctx := dynamic? then if ctx.proc == proc then return some ctx
  let mod ← getCurrentModule
    (errMsg := "internal error: a Veil action continuation escaped its module")
  /- The recovered context has empty `parameters`; they only refine the
  wording of capitalized-index warnings, which is acceptable to lose here. -/
  return some { mod, proc, monad := ← fallbackMonad }

/-- Action identity available while Lean computes statement control-flow
information, where there is no `DoElabM` monad value to inspect. -/
def currentVeilControlContext? : TermElabM (Option Context) :=
  recoverVeilContext? (pure <| mkConst ``Unit)

/-- Recover the context of a postponed continuation from its lexical marker.
The monad is deliberately taken from the continuation itself and is checked
below before a Veil handler is allowed to run. -/
def effectiveVeilDoContext? : Lean.Elab.Do.DoElabM (Option Context) := do
  recoverVeilContext? (return (← read).monadInfo.m)

private def monadIsVeilM (ctx : Context) : Lean.Elab.Do.DoElabM Bool := do
  let monad := (← read).monadInfo.m
  let monad ← instantiateMVars monad
  let expectedMonad ← instantiateMVars ctx.monad
  if monad.hasMVar || expectedMonad.hasMVar then
    return false
  unless monad.isAppOfArity' ``VeilM 3 && expectedMonad.isAppOfArity' ``VeilM 3 do
    return false
  withNewMCtxDepth do isDefEq monad expectedMonad

/-- Cheap handler bail-out used before scanning lexical markers.  This keeps
Veil's globally registered handlers essentially free in ordinary Lean `do`
blocks.  Like `monadIsVeilM` above, it requires a literal `VeilM` head;
reducible aliases of `VeilM` are deliberately not treated as Veil actions. -/
private def currentMonadCouldBeVeilM : Lean.Elab.Do.DoElabM Bool := do
  let monad ← instantiateMVars (← read).monadInfo.m
  if monad.hasMVar then return false
  return monad.consumeMData.getAppFn.constName? == some ``VeilM

private def activeVeilContext? : Lean.Elab.Do.DoElabM (Option Context) := do
  unless ← currentMonadCouldBeVeilM do return none
  let some ctx ← effectiveVeilDoContext? | return none
  unless ← monadIsVeilM ctx do return none
  return some ctx

/-- Gate a Veil handler. Falling through uses Lean's ordinary handler and its
saved elaborator state. -/
def requireVeilDoBlock : Lean.Elab.Do.DoElabM Context := do
  let some ctx ← activeVeilContext? | throwUnsupportedSyntax
  pure ctx


/-! ## State and theory openings -/

private def concreteFieldName (nm : Name) : Name :=
  mkVeilImplementationDetailName <| nm.appendAfter "_conc"

/-- Is there a user declaration of `name` underneath any generated field
views? -/
def findUserLocal? (name : Name) : TermElabM (Option LocalDecl) := do
  (← getLCtx).findDeclRevM? fun decl =>
    if decl.userName == name && decl.kind != .implDetail then
      return some decl
    else
      return none

def isUserShadowed (name : Name) : TermElabM Bool :=
  return (← findUserLocal? name).isSome

/-- Fold over the user-visible (non-implementation-detail) local
declarations. -/
def foldUserLocals (init : α) (f : α → LocalDecl → α) : TermElabM α :=
  return (← getLCtx).foldl
    (fun acc decl => if decl.kind == .implDetail then acc else f acc decl) init

private def userLocalNames : TermElabM NameSet :=
  foldUserLocals {} fun names decl => names.insert decl.userName

/-- Bind the logical value of a component under its implementation-detail
name, such as `__veil_X`, then elaborate `k` with that value in scope. -/
private def bindImplementationDetailField (fieldName : Name) (ty value : Expr)
    (k : Expr → DoElabM Expr) : DoElabM Expr :=
  mapLetDecl (mkVeilImplementationDetailName fieldName) ty value (kind := .implDetail) k

/-- Elaborate `k`, the remainder of the action, with the value also available
under the plain component name, unless that name is shadowed by a user
declaration. -/
private def bindUserFacingField (shadowed : NameSet) (fieldName : Name)
    (ty value : Expr) (k : DoElabM Expr) : DoElabM Expr :=
  if shadowed.contains fieldName then
    k
  else
    mapLetDecl fieldName ty value (kind := .implDetail) fun _ => k

/-- Elaborate the concrete value stored for `field` in the current state.
Returns its implementation-detail `_conc` name, inferred type, and value. -/
private def elabConcreteField (stateName : Name) (field : StateComponent) :
    DoElabM (Name × Expr × Expr) := do
  let concreteName := concreteFieldName field.name
  let concreteStx ← `($(mkIdent stateName).$(mkIdent field.name))
  let concrete ← Term.elabTerm concreteStx none
  return (concreteName, ← inferType concrete, concrete)

/-- Elaborate the logical value exposed for `field` by applying its
`FieldRepresentation.get` operation to the concrete `_conc` binding. -/
private def elabAbstractField (field : StateComponent) (concreteName : Name) :
    DoElabM (Expr × Expr) := do
  let declaredTy ← Term.elabType (← field.typeStx)
  let abstractStx ←
    `(($fieldRepresentation _).$(mkIdent `get) $(mkIdent concreteName))
  let abstract ← Term.elabTermEnsuringType abstractStx declaredTy
  return (declaredTy, abstract)

/- Field openings always bind a component's logical value under an
implementation-detail name and then, if unshadowed, alias the plain field name
to it. Mutable fields have one additional binding for their concrete stored
representation. For example, opening mutable `X` around `k` produces:

    let __veil_X_conc := currentState.X
    let __veil_X := fieldRepresentation.get __veil_X_conc
    let X := __veil_X  -- omitted when a user declaration shadows `X`
    k

An immutable theory field has the same two logical bindings but no `_conc`
binding. Theory fields are opened once because the reader is immutable. State
fields are rebuilt from a fresh monadic `get` around every statement, so a
newer `__veil_X_conc` shadows the previous snapshot before the next statement
is elaborated.

All generated bindings are `.implDetail`. They are therefore ignored by
`findUserLocal?`/`foldUserLocals`, do not trigger shadow warnings, and never
count as user shadowing when the next state opening is built. -/

private def bindTheoryFields (shadowed : NameSet) (theoryName : Name)
    (fields : Array StateComponent) (k : DoElabM Expr) : DoElabM Expr :=
  fields.foldr (init := k) fun field rest => do
    let ty ← Term.elabType (← field.typeStx)
    let valueStx ← `($(mkIdent theoryName).$(mkIdent field.name))
    let value ← Term.elabTermEnsuringType valueStx ty
    bindImplementationDetailField field.name ty value fun implementationValue =>
      bindUserFacingField shadowed field.name ty implementationValue rest

private def bindStateFields (shadowed : NameSet) (stateName : Name)
    (fields : Array StateComponent) (k : DoElabM Expr) : DoElabM Expr :=
  fields.foldr (init := k) fun field rest => do
    let (concreteName, concreteTy, concrete) ← elabConcreteField stateName field
    mapLetDecl concreteName concreteTy concrete (kind := .implDetail) fun _ => do
      let (declaredTy, abstract) ← elabAbstractField field concreteName
      bindImplementationDetailField field.name declaredTy abstract fun implementationValue =>
        bindUserFacingField shadowed field.name declaredTy implementationValue rest

/-- Internal element used by openings so the generated `read`/`get` does not
redispatch through the user-statement wrapper. -/
syntax (name := internalExpr) "veil_do_internal_expr% " term : doElem

@[doElem_elab internalExpr]
def elabInternalExpr : DoElab := fun stx dec => do
  let `(doElem| veil_do_internal_expr% $rhs:term) := stx
    | throwUnsupportedSyntax
  Lean.Elab.Do.elabDoExpr (← `(doElem| $rhs:term)) dec

private def bindInternalResult (ref : Syntax) (hint operation : Name)
    (k : Name → DoElabM Expr) : DoElabM Expr := do
  let name ← mkFreshUserName (mkVeilImplementationDetailName hint)
  let rhs ← `(doElem| veil_do_internal_expr% $(mkIdent operation):term)
  elabDoIdDecl (mkIdentFrom ref name) none rhs (k name)

syntax (name := theoryOpen) "veil_do_open_theory%" : doElem

@[doElem_control_info theoryOpen]
def theoryOpenControlInfo : ControlInfoHandler := fun _ =>
  return ControlInfo.pure

@[doElem_elab theoryOpen]
def elabTheoryOpen : DoElab := fun stx dec => do
  let `(doElem| veil_do_open_theory%) := stx | throwUnsupportedSyntax
  let ctx ← requireVeilDoBlock
  let dec ← dec.ensureUnitAt stx
  let shadowed ← userLocalNames
  bindInternalResult stx `theory ``read fun theoryName =>
    bindTheoryFields shadowed theoryName ctx.mod.immutableComponents
      dec.continueWithUnit

/-- Reopen all unshadowed mutable fields from a fresh monadic `get`, then run
the statement elaborator directly. -/
def openStateAround (mod : Module) (k : DoElabM Expr) : DoElabM Expr := do
  let ref ← getRef
  let shadowed ← userLocalNames
  bindInternalResult ref `state ``get fun stateName =>
    bindStateFields shadowed stateName mod.mutableComponents k

/-- Inline generated field views, and ordinary local lets derived from them,
when an expression's outer shape must be visible to a later consumer. -/
def zetaFieldDerivedLets (mod : Module) (e : Expr) : DoElabM Expr := do
  let isGeneratedFieldView (decl : LocalDecl) : Bool :=
    decl.kind == .implDetail && mod.signature.any fun field =>
      decl.userName == field.name ||
      decl.userName == mkVeilImplementationDetailName field.name ||
      decl.userName == concreteFieldName field.name
  let derived := (← getLCtx).foldl (init := #[]) fun (derived : Array FVarId) decl =>
    let dependsOnFieldView (value : Expr) : Bool :=
      (Lean.collectFVars {} value).fvarIds.any derived.contains
    if decl.value?.any fun value => isGeneratedFieldView decl || dependsOnFieldView value then
      derived.push decl.fvarId
    else
      derived
  zetaDeltaFVars e derived

def currentConcreteFieldIdent (field : Name) : Ident :=
  mkIdent (concreteFieldName field)

end Action.DoElab
end Veil
