module

public meta import Lean.Elab.BuiltinDo
public meta import Veil.Frontend.DSL.Action.Semantics.WP
public meta import Veil.Frontend.DSL.Infra.EnvExtensions
public meta import Veil.Frontend.DSL.Module.Util

public meta section

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

/-- The *concrete* value of mutable `field` in the current state: a projection
of the newest `currentStateBindingName` binding, which `openStateAround`
introduces for every statement. Lean resolves the dotted identifier
`__veil_state.field` as that local followed by the projection `.field`. -/
def currentStateField (field : Name) : Ident :=
  mkIdent (currentStateBindingName ++ field)

/-- Elaborate the logical value of mutable `field` in the current state, by
applying its `FieldRepresentation.get` operation to the concrete value.
Returns the field's declared type and the value. -/
private def elabStateFieldView (field : StateComponent) : DoElabM (Expr × Expr) := do
  let declaredTy ← Term.elabType (← field.typeStx)
  let viewStx ←
    `(($fieldRepresentation _).$(mkIdent `get) $(currentStateField field.name))
  let view ← Term.elabTermEnsuringType viewStx declaredTy
  return (declaredTy, view)

/- Opening the state binds the state itself, from a fresh monadic `get`, and
then the logical value of each mutable field under the plain field name,
unless a user declaration shadows it. For example, opening a state with
mutable `X` around `k` produces:

    let __veil_state ← get
    let X := fieldRepresentation.get __veil_state.X  -- omitted when shadowed
    k

Nothing else depends on the field views: a write reads the concrete value it
updates as `__veil_state.X` (`currentStateField`), and `veil_exact_state`
rebuilds the current state from the same projections. State openings are
rebuilt around every statement, and the newer `__veil_state` and views shadow
the previous ones.

An immutable theory field is bound twice: under its implementation-detail
name `__veil_X`, which `veil_exact_theory` finds even when a user declaration
shadows `X`, and, if unshadowed, under `X`. Theory fields are opened once,
because the reader is immutable.

The views of one state opening are abstracted with a single `mkLetFVars`
once the rest of the action has been elaborated; see `bindStateFields` for
why.

All generated views are `.implDetail`. They are therefore ignored by
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

/-- Bind the view of every unshadowed field in `fields` (see
`elabStateFieldView`), elaborate `k`, the remainder of the action, and
abstract all views of this opening at once. The views only read
`__veil_state`, not each other, so they are all elaborated before any of them
is bound. -/
private def bindStateFields (shadowed : NameSet) (fields : Array StateComponent)
    (k : DoElabM Expr) : DoElabM Expr := do
  let views ← (fields.filter (!shadowed.contains ·.name)).mapM fun field => do
    let (ty, value) ← elabStateFieldView field
    return (field.name, ty, value)
  bindAll views 0 #[]
where
  /-- Bind `views[i:]` as `let`s, then elaborate `k` and abstract all of
  `fvars` with one `mkLetFVars`. -/
  bindAll (views : Array (Name × Expr × Expr)) (i : Nat) (fvars : Array Expr) :
      DoElabM Expr := do
    if h : i < views.size then
      let (name, ty, value) := views[i]
      withLetDecl name ty value (kind := .implDetail) fun x =>
        bindAll views (i + 1) (fvars.push x)
    else
      /- One `mkLetFVars` for all views, rather than one per view as nested
      `mapLetDecl`s would do. `k` returns the rest of the action, and every
      `mkLetFVars` traverses it twice: `elimMVarDeps` replaces each pending
      metavariable whose local context contains the abstracted variables with
      a new auxiliary metavariable connected by a delayed assignment, and
      `abstractRange` turns the variables into bound ones. Abstracting the
      views one at a time repeats both traversals once per view and chains one
      delayed assignment per view onto every pending metavariable, which made
      an opening cost (number of fields) × (size of the rest of the action).
      Abstracting them together does each traversal once and yields the same
      term. -/
      mkLetFVars fvars (← k) (usedLetOnly := true) (generalizeNondepLet := false)
  termination_by views.size - i

/-- Internal element used by openings so the generated `read`/`get` does not
redispatch through the user-statement wrapper. The right-hand side of a Veil
`let x ← rhs` is marked the same way, to stay under the statement's opening. -/
syntax (name := internalExpr) "veil_do_internal_expr% " term : doElem

/- Behaves like a plain `doExpr`. Registered because an internal element can
now stand in for the right-hand side of `let x ← rhs`, a position that Lean's
control-info inference recurses into. -/
@[doElem_control_info internalExpr]
def internalExprControlInfo : ControlInfoHandler := fun _ =>
  return ControlInfo.pure

@[doElem_elab internalExpr]
def elabInternalExpr : DoElab := fun stx dec => do
  let `(doElem| veil_do_internal_expr% $rhs:term) := stx
    | throwUnsupportedSyntax
  Lean.Elab.Do.elabDoExpr (← `(doElem| $rhs:term)) dec

/-- The head of an expression statement: `f` in `f x y`, or the identifier
itself. -/
private def doExprHeadName? (stx : DoElem) : Option Name :=
  match stx with
  | `(Lean.Parser.Term.doExpr| $term:term) =>
    if term.raw.isIdent then
      some term.raw.getId
    else
      term.isApp?.map (fun (head, _) => head.getId)
  | _ => none

def rejectDirectRecursion (ctx : Context) (stx : DoElem) : DoElabM Unit := do
  if doExprHeadName? stx == some ctx.proc &&
      (← findUserLocal? ctx.proc).isNone then
    throwErrorAt stx
      "recursive Veil action calls are not supported; action bodies must terminate structurally"

/-- If `rhs` is a plain expression, mark it internal, so that it is elaborated
under the enclosing statement's opening rather than through `elabVeilExpr`,
which would open the state **once more** for the same program point. Direct
recursion is rejected here, as `elabVeilExpr` would have done. Other
right-hand sides (`if`, `match`, nested `do`) are left alone: their handlers
open the state for themselves. -/
def internalIfPlainTerm? (ctx : Context) (rhs : DoElem) : DoElabM (Option DoElem) := do
  let `(doElem| $e:term) := rhs | return none
  rejectDirectRecursion ctx rhs
  some <$> withRef rhs `(doElem| veil_do_internal_expr% $e)

/-- Bind the result of the monadic `operation` under `name`, then elaborate `k`. -/
private def bindInternalResultAs (ref : Syntax) (name operation : Name)
    (k : DoElabM Expr) : DoElabM Expr := do
  let rhs ← `(doElem| veil_do_internal_expr% $(mkIdent operation):term)
  elabDoIdDecl (mkIdentFrom ref name) none rhs k

/-- Bind the result of the monadic `operation` under a fresh
implementation-detail name derived from `hint`, then elaborate `k` with that
name. -/
private def bindInternalResult (ref : Syntax) (hint operation : Name)
    (k : Name → DoElabM Expr) : DoElabM Expr := do
  let name ← mkFreshUserName (mkVeilImplementationDetailName hint)
  bindInternalResultAs ref name operation (k name)

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

/-- Bind the current state from a fresh monadic `get` under
`currentStateBindingName`, reopen all unshadowed mutable fields from it, then
run the statement elaborator directly. -/
def openStateAround (mod : Module) (k : DoElabM Expr) : DoElabM Expr := do
  let ref ← getRef
  let shadowed ← userLocalNames
  bindInternalResultAs ref currentStateBindingName ``get <|
    bindStateFields shadowed mod.mutableComponents k

/-- Inline generated field views, and ordinary local lets derived from them,
when an expression's outer shape must be visible to a later consumer. -/
def zetaFieldDerivedLets (mod : Module) (e : Expr) : DoElabM Expr := do
  let isGeneratedFieldView (decl : LocalDecl) : Bool :=
    decl.kind == .implDetail && mod.signature.any fun field =>
      decl.userName == field.name ||
      decl.userName == mkVeilImplementationDetailName field.name
  let derived := (← getLCtx).foldl (init := #[]) fun (derived : Array FVarId) decl =>
    let dependsOnFieldView (value : Expr) : Bool :=
      (Lean.collectFVars {} value).fvarIds.any derived.contains
    if decl.value?.any fun value => isGeneratedFieldView decl || dependsOnFieldView value then
      derived.push decl.fvarId
    else
      derived
  zetaDeltaFVars e derived

end Action.DoElab
end Veil
