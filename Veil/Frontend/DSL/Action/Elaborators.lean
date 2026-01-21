import Lean
import Veil.Frontend.DSL.Action.Syntax
import Veil.Frontend.DSL.Action.DoNotation
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Util
import Veil.Util.Meta

open Lean Elab Command Term

/-! # Elaborators for Veil actions

  This file contains the elaborators for Veil actions. Every `action`
  declaration in a Veil `module` elaborates into a plethora of
  inter-related Lean definitions. For an action named `act`:

  1. First of all, we have to elaborate the `veil_do` notation of the
  `action`. We elaborate it generic in the mode as `act.do` (see
  `Semantics/Definitions.lean`), and then, based on `act.do`, define:
    - `act` — the `internal` mode of the action, which is what gets
    called by other actions; this has a return value
    - `act.ext` - the `external` mode of the action; always returning
    `Unit` (the environment does not care about the return value)

  2. Then, from `act`/`act.ext`, we derive `act.wp`/`act.ext.wp`, their
  WP parameterised by a set of exceptions IDs `ExId → Prop` which we
  DON'T care about (assertion failures are treated as exceptions, and
  each assertion has its unique ID).
-/

namespace Veil

abbrev FullyQualifiedName := Name
/-- Get the fully qualified name of an _existing_ definition. -/
def getFullyQualifiedName [Monad m] [MonadResolveName m] [MonadEnv m] [MonadOptions m] [MonadLog m] [AddMessageContext m] [MonadError m] (name : Name) : m FullyQualifiedName := do
  resolveGlobalConstNoOverload (mkIdent name)

/-- If `mode?` is `none`, the name is the `.do`-definition of the action, i.e.
the one that is parametric in `mode`. -/
def ProcedureInfo.nameInMode (pi : ProcedureInfo) (mode? : Option Mode) : Name :=
  match mode? with
  | .none => toDoName pi.name
  | .some mode => toActName pi.name mode

/-- `[unchanged|s| id1 id2 ...]` expands to
`id1 = id1s ∧ id2 = id2s ∧ ...`, where `idxs` is the name `idx` with `s` appended. -/
macro_rules
  | `([unchanged|$s:str| $id:ident]) => `($id = $(mkIdent <| id.getId.appendAfter s.getString))
  | `([unchanged|$s| $id $ids*]) => `([unchanged|$s| $id] ∧ [unchanged|$s| $ids*])
  | `([unchanged|$_|]) => `(True)

/-! ## Auxiliary definitions-/
namespace AuxiliaryDefinitions
open Veil Veil.Simp

def Argument := Term
def SyntaxTemplate := Array Argument → TermElabM Term

/-- Template for defining the WP of an action. -/
private def wpTemplate (sourceAction : Name) : SyntaxTemplate :=
  let (handler, post) := (mkVeilImplementationDetailIdent `handler, mkVeilImplementationDetailIdent `post)
  (fun args : Array Term =>
    `(fun $handler $post => [IgnoreEx $handler| $(mkIdent ``wp) (@$(mkIdent sourceAction) $args*) $post]))

/-- Template for defining the transition version of an action, based on its WP. -/
private def transitionTemplate (sourceWpFqn : Name) : SyntaxTemplate :=
  (fun args : Array Term =>
    `($(mkIdent ``VeilSpecM.toTransitionDerived) (@$(mkIdent sourceWpFqn) $args* (fun _ => $(mkIdent ``True)))))

/-- Template for `VeilM.toTransitionDerived` applied to an action. -/
private def derivedTransitionTemplate (sourceAction : Name) : SyntaxTemplate :=
  (fun args : Array Term =>
    `($(mkIdent ``VeilM.toTransitionDerived) (@$(mkIdent sourceAction) $args*)))

/-- Elaborate `simp` theorems that are given as `term`s and add them
into `ctx`, assuming all those `simp` theorems are `pre` and `→`. -/
private def elabSimpArgForTerms (ctx : Meta.Simp.Context) (simps : Array (TSyntax `term × Name)) : TermElabM Meta.Simp.Context := do
  -- the following manipulation is adapted from `elabSimpArgs` in `Lean/Elab/Tactic/Simp.lean`
  let indexConfig := ctx.indexConfig
  let simpThms ← simps.filterMapM fun (stx, name) =>
    elabSimpTheoremFromTerm indexConfig (.stx name stx) stx (post := false) (inv := false)
  let mut thmsArray := ctx.simpTheorems
  let mut thms      := thmsArray[0]!
  for entries in simpThms do
    for entry in entries do
      thms := thms.addSimpEntry entry
  let ctx' := ctx.setSimpTheorems (thmsArray.set! 0 thms)
  return ctx'

/-- Perform simplification using `get_set_idempotent'`. This requires
some special handling since these `simp` theorems might only be given
in terms of `Expr`s. -/
private def simpGetSetForFieldRepTC (ctx : Meta.Simp.Context) : TermElabM Meta.Simp.Context := do
  let lctx ← getLCtx
  -- find the local `FieldRepresentation` hypothesis
  let some hyp := lctx.findDecl? (fun decl =>
    if decl.type.getForallBody.getAppFn.constName? == Option.some ``FieldRepresentation
    then .some decl else .none) | return ctx
  -- find the local `LawfulFieldRepresentation` hypothesis, record its name
  let some lawfulRep := lctx.findDecl? (fun decl =>
    if decl.type.getForallBody.getAppFn.constName? == Option.some ``LawfulFieldRepresentation
    then .some (mkIdent decl.userName) else .none) | return ctx
  -- get the state label type name
  let .forallE _ dom _ _ := hyp.type | return ctx
  let some labelTypeName := dom.constName? | return ctx
  -- get the state name from the hypothesis by taking the prefix of the state label type name
  let stateTypeName := labelTypeName.getPrefix
  let fields ← getFieldIdentsForStruct stateTypeName
  let simps ← fields.mapM fun f => do
    let stx ← `(($lawfulRep .$f).$(mkIdent `get_set_idempotent') (by infer_instance_for_iterated_prod))
    let name ← mkFreshUserName (f.getId ++ `get_set_idempotent')
    pure (stx, name)
  elabSimpArgForTerms ctx simps

-- NOTE: The uses of `open Classical` below is mainly for allowing
-- rewriting based simplification where the target term is depended by
-- instances like `Decidable`. For the whole term after rewriting to
-- typecheck, these instances need to be reconstructed, which might
-- fail due to unknown reasons. By opening `Classical`, we provide
-- default instances for `Decidable`, so the reconstruction will
-- always succeed. This is a bit of a hack, but it works for now.
private def evalOpenClassical (k : MetaM α) : MetaM α := do
  evalOpen (← `(Parser.Command.openDecl| $(mkIdent `Classical):ident)) k

private def simplifierGetSetForFieldRepTC : TermElabM Simplifier := do
  let ctx ← mkVeilSimpCtx #[]
  let ctx' ← simpGetSetForFieldRepTC ctx
  return (evalOpenClassical ∘ Simp.simpCore ctx')

/-- Define a theorem stating `∀ xs, lhs = rhs xs`, where `proof` is the proof
term for `lhs = rhs xs` (`xs` are free variables in the local context), and
`rhs` is a `Name` (i.e., a definition). `eqThmName` is the name of the theorem
to be defined. -/
private def proveEqABoutBody (lhs : Expr) (rhs : Name) (xs : Array Expr) (proof : Expr)
  (eqThmName : Name) (eqThmAttrs : Array Attribute) : TermElabM Unit := do
  let rhs ← Meta.mkAppOptM rhs $ xs.map Option.some
  let eqStatement ← Meta.mkEq lhs rhs
  let eqStatement ← instantiateMVars $ ← Meta.mkForallFVars xs eqStatement
  let eqProof ← instantiateMVars $ ← Meta.mkLambdaFVars xs proof
  let _ ← addVeilTheorem eqThmName eqStatement eqProof (attr := eqThmAttrs)

/-- **Pre-compute** the `wp` for the given action, store it in the `act.wp`
definition, and prove `act.wp_eq` which states that this definition is equal to
`wp act post`.

We can then rewrite/simp using `act.wp_eq` to not have to recompute the WP
for every VC. This is an optimisation — Veil would work without it, but it
would be significantly slower. -/
private def defineWp (mod : Module) (nm : Name) (mode : Mode) (dk : DeclarationKind) : TermElabM Unit := do
  let modeStr := match mode with | .internal => "internal" | .external => "external"
  -- Use dynamic trace class name so each WP computation appears separately in the profiler
  withTraceNode (`veil.perf.extract.defineWp ++ nm) (fun _ => return s!"defineWp {nm} ({modeStr})") do
    let fqn ← getFullyQualifiedName nm
    let (allBinders, allArgs) ← mod.declarationAllBindersArgs nm dk
    let wpDef ← wpTemplate fqn allArgs
    elabBinders allBinders $ fun vs => do -- `vs` are the fvars for the definition binders
    -- Warning to future maintainers: this code performs nitty-gritty simplification,
    -- and we've spent a long time on it. It appears that it's difficult to do this
    -- any other way. Trying to significantly rewrite this code is likely going to
    -- take more time than you'd like or expect.
    -- (1) Elaborate the template for the WP definition, parametrised by
    -- `handler` and `post`
    let e ← withTraceNode (`veil.perf.extract.elabTerm ++ nm) (fun _ => return s!"elabTerm wp {nm}") do
      withoutErrToSorry $ elabTermAndSynthesize wpDef none
    trace[veil.debug] "[{decl_name%}] e: {e}"
    -- (2) Simplify the _body_ of the WP definition and return the simplified
    -- body _and_ the simplified full expression (with lambdas). See note (*)
    -- for why we simplify the body rather than the full expression directly.
    Meta.lambdaTelescope e fun xs body => do -- `xs` are `handler` and `post`, respectively
      -- NOTE: `unfoldPartialApp` is required when some `foo.wp` is only partially
      -- applied (e.g., `(if ... then foo.wp else ...) th st`). In other words,
      -- if `foo.wp` becomes fully applied after simplification, `unfoldPartialApp` is not necessary.
      let mainSimp ← do
        let tmp : Simplifier := @id Simplifier (evalOpenClassical ∘ Simp.simp #[`wpSimp] { unfoldPartialApp := true : Meta.Simp.Config })
          |>.andThen (evalOpenClassical ∘ Simp.simp #[`forallQuantifierSimp])
          |>.andThen (evalOpenClassical ∘ Simp.simp #[`substateSimp])
        if mod._useFieldRepTC
        then
          let ss ← simplifierGetSetForFieldRepTC
          -- (1) do basic simplification using `LawfulFieldRepresentation`
          pure <| (tmp |>.andThen (Simp.simp #[`fieldRepresentationSetSimpPre])
            -- (2) simplify using `get_set_idempotent'`
            |>.andThen ss
            -- (3) simplify the resulting things
            |>.andThen (evalOpenClassical ∘ Simp.simp
              #[fieldLabelToDomainName stateName,
                fieldLabelToCodomainName stateName,
                `fieldRepresentationSetSimpPost]))
        else pure <| tmp
      let simp := (Simp.unfold #[fqn]) |>.andThen mainSimp
      let resBody ← withTraceNode (`veil.perf.extract.wpSimp ++ nm) (fun _ => return s!"wpSimp {nm}") do simp body
      -- (3) Construct the expression for `act.wp`
      -- The expression for `act.wp`; **TODO** register as a derived definition
      let wpExpr ← instantiateMVars $ ← Meta.mkLambdaFVars (vs ++ xs) resBody.expr
      let wpSimpAttrLow ← elabAttr $ ← `(Parser.Term.attrInstance| wpSimp ↓ low)
      let wpDef_fqn ← addVeilDefinition (toWpName nm) wpExpr (attr := #[{name := `reducible}, wpSimpAttrLow])
      -- We want to prove:
      -- `∀ ($handler) ($post), $(mkIdent ``wp) (@$(mkIdent sourceAction) $args*) $post = @$(mkIdent wpDefName) $args* $handler $post`
      -- But elaborating this here is cumbersome, since we would need a type
      -- annotation for the return type of the action, as well as typelcass
      -- instances. So instead of constructing this equality at the syntax level,
      -- we construct it directly as an `Expr`.
      -- (*) it's easier to construct the proof here with the body
      let #[_handler, post] := xs | throwError "defineWp: expected 2 arguments, got {xs.size}"
      let wpSimpAttrHigh ← elabAttr $ ← `(Parser.Term.attrInstance| wpSimp ↓ high)
      proveEqABoutBody body wpDef_fqn (vs ++ xs) (← resBody.getProof) (toWpEqName nm) #[wpSimpAttrHigh]

      if mod._useLocalRPropTC then
      if dk matches .derivedDefinition .actionLike _ then
      if mode matches .external then
        -- FIXME: this way of obtaining the arguments required by `LocalRPropTC` is hacky
        let vs' := vs.take mod.parameters.size
        let localRPropTCFqn ← resolveGlobalConstNoOverloadCore localRPropTCName
        let localRPropTCArg ← Meta.mkAppOptM localRPropTCFqn (vs'.map Option.some |>.push none |>.push post)
        Meta.withLocalDecl `localRPropTC BinderInfo.instImplicit localRPropTCArg fun inst => do
          -- add `LocalRProp` specific simplification
          let simp : Simplifier ← do
            let ctx ← mkVeilSimpCtx #[]
            let simpTerm ← `(term| $(mkIdent `LocalRProp.core_eq) ($(mkIdent `self) := by assumption))
            let arr := #[(simpTerm, (← mkFreshUserName `LocalRProp.core_eq))]
            let ctx' ← elabSimpArgForTerms ctx arr
            pure <| Simp.simpCore ctx'
          let simp := simp.andThen mainSimp
          let resBody' ← simp resBody.expr
          let fvars := (vs ++ xs).push inst
          let wpExpr' ← instantiateMVars $ ← Meta.mkLambdaFVars fvars resBody'.expr
          let wpDef_fqn' ← addVeilDefinition (toWpLOName nm) wpExpr' (attr := #[{name := `reducible}, wpSimpAttrLow])

          let resBody' ← resBody.mkEqTrans resBody'
          let wpSimpAttrHigher ← elabAttr $ ← `(Parser.Term.attrInstance| wpSimp ↓ (high + 100))
          -- NOTE: The proof term might be reduced by reusing the previous `wp_eq` theorem
          proveEqABoutBody body wpDef_fqn' fvars (← resBody'.getProof) (toWpLOEqName nm) #[wpSimpAttrHigher]

/-- Pre-compute the transition for the given action, store it in the `act.ext.tr`
definition, and prove `act.ext.tr_eq` which states that this definition is equal to
`VeilSpecM.toTransitionDerived (wp act.post)`. -/
private def defineTransition (mod : Module) (nm : Name) (dk : DeclarationKind) : TermElabM Unit := do
  -- Use dynamic trace class name so each transition computation appears separately in the profiler
  withTraceNode (`veil.perf.extract.defineTransition ++ nm) (fun _ => return s!"defineTransition {nm}") do
    let sourceWpFqn ← getFullyQualifiedName (toWpName nm)
    let (allBinders, allArgs) ← mod.declarationAllBindersArgs nm dk
    let trDef ← transitionTemplate sourceWpFqn allArgs
    elabBinders allBinders $ fun vs => do
      -- (1) Elaborate the template
      let e ← withTraceNode (`veil.perf.extract.elabTerm ++ nm) (fun _ => return s!"elabTerm transition {nm}") do
        withoutErrToSorry $ elabTermAndSynthesize trDef none
      trace[veil.debug] "[{decl_name%}] e: {e}"
      -- (2) Simplify
      Meta.lambdaTelescope e fun xs body => do
        let simp := Simp.dsimp #[``VeilSpecM.toTransitionDerived, ``Cont.inv, ``compl] { unfoldPartialApp := true : Meta.Simp.Config }
          |>.andThen (Simp.simp #[`wpSimp])   -- for rewriting with WP equality theorem
        let resBody ← withTraceNode (`veil.perf.extract.trSimp ++ nm) (fun _ => return s!"trSimp {nm}") do simp body
        -- (3) Construct the expression
        -- The expression for `act.ext.tr`; **TODO** register as a derived definition
        let trExpr ← instantiateMVars $ ← Meta.mkLambdaFVars (vs ++ xs) resBody.expr
        let attrs ← #[`actSimp, `nextSimp].mapM (fun attr => do elabAttr $ ← `(Parser.Term.attrInstance| $(Lean.mkIdent attr):ident))
        let trDef_fqn ← addVeilDefinition (toTransitionName nm) trExpr (attr := #[{name := `reducible}] ++ attrs)
        -- (4) Prove the equality theorem
        proveEqABoutBody body trDef_fqn (vs ++ xs) (← resBody.getProof) (toTransitionEqName nm) #[]
        -- (5) Prove the derived_eq theorem: VeilM.toTransitionDerived act.ext = act.ext.tr
        -- Use the action's fully qualified name (nm is already the external mode name)
        let actionFqn ← getFullyQualifiedName nm
        let derivedDef ← derivedTransitionTemplate actionFqn allArgs
        -- Elaborate within the same binder context (vs are already bound)
        let derivedExpr ← withoutErrToSorry $ elabTermAndSynthesize derivedDef none
        trace[veil.debug] "[{decl_name%}] derivedExpr for derived_eq: {derivedExpr}"
        -- The derivedExpr is `VeilM.toTransitionDerived (act.ext args*)` which has type `Transition ρ σ`
        -- We need to apply it to the transition variables (r₀ s₀ s₁) to get a Prop,
        -- but for equality of functions, we can work at the function level
        Meta.lambdaTelescope derivedExpr fun xs' derivedBody => do
          -- Simplify by unfolding VeilM.toTransitionDerived, then VeilSpecM.toTransitionDerived, Cont.inv, compl,
          -- and using wpSimp to rewrite wp to the precomputed wp definition
          let derivedSimp := Simp.dsimp #[``VeilM.toTransitionDerived] { unfoldPartialApp := true : Meta.Simp.Config }
            |>.andThen (Simp.dsimp #[``VeilSpecM.toTransitionDerived, ``Cont.inv, ``compl] { unfoldPartialApp := true : Meta.Simp.Config })
            |>.andThen (Simp.simp #[`wpSimp])
          let resBody' ← derivedSimp derivedBody
          -- Prove equality with act.ext.tr
          let attrs ← #[`actSimp, `nextSimp].mapM (fun attr => do elabAttr $ ← `(Parser.Term.attrInstance| $(Lean.mkIdent attr):ident))
          proveEqABoutBody derivedBody trDef_fqn (vs ++ xs') (← resBody'.getProof) (toDerivedEqName nm) attrs

end AuxiliaryDefinitions

/-! ## Procedure elaboration -/

private def withVeilModeVar (bi : BinderInfo) (k : Expr → TermElabM α) : TermElabM α :=
  Meta.withLocalDecl veilModeVar.getId bi (mkConst ``Mode) k

/-- Elaborate `body` under `br`, and obtain its extra parameters. -/
def elabProcedureCore (vs : Array Expr) (pi : ProcedureInfo) (br : Option (TSyntax ``Lean.explicitBinders)) (body : Term) (addModeArg : Bool := true) : TermElabM (Array Parameter × Expr) := do
  let brs ← Option.stxArrMapM br toFunBinderArray
  let stx ← mkFunSyntax brs body
  try
    withVeilModeVar BinderInfo.default fun mode => do
    /- We want to throw an error if anything fails or is missing during elaboration. -/
    withoutErrToSorry $ do
    let (mvars, e) ← elabTermDecidable stx
    let e ← Meta.mkLambdaFVarsImplicit ((if addModeArg then #[mode] else #[]) ++ vs ++ mvars) e (binderInfoForMVars := BinderInfo.instImplicit) >>= instantiateMVars
    -- `e` should not contain any metavariable; capture the error here
    if e.hasMVar then
      throwError "mvar(s) exist in the elaborated expression. Consider adding more type annotations."
    -- NOTE: Doing `dsimp` on `act.do`, `act` or `act.ext` will inline
    -- `let` bindings, which _might_ lead to performance issues
    return (← mvars.mapIdxM (fun i mvar => mvarToParam pi.name mvar i), e)
  catch ex =>
    throwError "Error in action {pi.name}: {← ex.toMessageData.toString}"
where
  mvarToParam (inAction : Name) (mvar : Expr) (i : Nat) : TermElabM Parameter := do
    let mvarTypeStx ← delabVeilExpr (← Meta.inferType mvar) true
    return { kind := .definitionParameter inAction .typeclass, name := Name.mkSimple s!"{inAction}_dec_{i}", «type» := mvarTypeStx, userSyntax := .missing }

def elabProcedureDoNotation (vs : Array Expr) (pi : ProcedureInfo) (br : Option (TSyntax ``Lean.explicitBinders)) (l : doSeq) : TermElabM (Array Parameter × Expr) := do
  let body ← `(veil_do $(mkIdent pi.name) in $environmentTheory, $environmentState in $l)
  elabProcedureCore vs pi br body

def elabTransitionTerm (vs : Array Expr) (pi : ProcedureInfo) (br : Option (TSyntax ``Lean.explicitBinders)) (t : Term) : TermElabM (Array Parameter × Expr) := do
  let body ← `(@$(mkIdent ``id) ($(mkIdent ``Transition) $environmentTheory $environmentState) ($t))
  elabProcedureCore vs pi br body (addModeArg := false)

def elabProcedureInMode (pi : ProcedureInfo) (mode : Mode) : TermElabM (Name × Expr) := do
  let doNm_fullyQualified ← getFullyQualifiedName $ (pi.nameInMode .none)
  let mut body := mkAppN (mkConst doNm_fullyQualified) #[mode.expr]
  /- The external mode of an action always returns `Unit`. -/
  if mode == Mode.external then
    body ← Meta.forallTelescope (← Meta.inferType body) fun ks _ => do
      Meta.mkLambdaFVars ks $ ← Meta.mkAppM' (mkConst ``VeilM.returnUnit) #[(mkAppN body ks)]
  let res ← (Simp.unfold #[doNm_fullyQualified]) body
  return (pi.nameInMode mode, res.expr)

def Module.registerProcedureSpecification [Monad m] [MonadError m] (mod : Module) (ps : ProcedureSpecification) : m Module := do
  mod.throwIfAlreadyDeclared ps.name
  return { mod with procedures := mod.procedures.push ps, _declarations := mod._declarations.insert ps.name (.procedure ps.info) }

private def Module.registerDerivedActionDefinition [Monad m] [MonadError m] [MonadQuotation m] (mod : Module) (base : ProcedureSpecification) (mode? : Option Mode) : m (Module × DeclarationKind) := do
  let derivedName := base.info.nameInMode mode?
  mod.throwIfAlreadyDeclared derivedName
  let derivedDefKind := match mode? with | .none => .actionDoLike | .some _ => .actionLike
  let declKind := .derivedDefinition derivedDefKind {base.name}
  let derivedDef : DerivedDefinition := { name := derivedName, kind := derivedDefKind, params := base.params, extraParams := base.extraParams, derivedFrom := {base.name}, stx := .none }
  let mod ← mod.registerDerivedDefinition derivedDef
  return (mod, declKind)

/- The implementation of this method _could_ be split into two distinct
parts (i.e. registering the action, then elaboration the definitions),
but that would eliminate opportunities for async elaboration. -/
def Module.defineProcedureCore (mod : Module) (pi : ProcedureInfo)
  (eDo : Expr) (ps : ProcedureSpecification) (deriveTransition? : Bool) : CommandElabM Module := do
  withTraceNode `veil.perf.extract (fun _ => return s!"defineProcedureCore {pi.name}") do
    -- We register the `internal` view of the action as the "real" one
    let mod ← mod.registerProcedureSpecification ps
    -- The `.do` and `.ext` views are marked as derived definitions
    let (mod, _doKind) ← mod.registerDerivedActionDefinition ps .none
    let intKind := ps.declarationKind
    let (mod, extKind) ← mod.registerDerivedActionDefinition ps Mode.external
    -- Elaborate the definitions in the Lean environment
    liftTermElabM $ do
      let nmDo := pi.nameInMode .none
      let _nmDo_fullyQualified ← addVeilDefinition nmDo eDo (attr := #[{name := `reducible}])
      let (nmInt, eInt) ← elabProcedureInMode pi Mode.internal
      let _nmInt_fullyQualified ← addVeilDefinition nmInt eInt (attr := #[{name := `actSimp}])
      AuxiliaryDefinitions.defineWp mod nmInt .internal intKind

      -- Procedures are never considered in their external view, so save some
      -- time by not elaborating those definitions.
      if pi matches .initializer | .action _ _ then do
        let (nmExt, eExt) ← elabProcedureInMode pi Mode.external
        let _nmExt_fullyQualified ← addVeilDefinition nmExt eExt (attr := #[{name := `actSimp}])
        AuxiliaryDefinitions.defineWp mod nmExt .external extKind
        if deriveTransition? then
          AuxiliaryDefinitions.defineTransition mod nmExt extKind
    return mod

def Module.defineProcedure (mod : Module) (pi : ProcedureInfo) (br : Option (TSyntax ``Lean.explicitBinders)) (spec : Option doSeq) (l : doSeq) (stx : Syntax) : CommandElabM Module := do
  -- Obtain `extraParams` so we can register the action
  let actionBinders ← (← mod.declarationBaseParams (.procedure pi)).mapM (·.binder)
  let (extraParams, eDo) ← liftTermElabMWithBinders actionBinders $ fun vs => elabProcedureDoNotation vs pi br l
  let ps := ProcedureSpecification.mk pi (← explicitBindersToParameters br pi.name) extraParams spec l stx
  mod.defineProcedureCore pi eDo ps true

/-- When `act` is given in the transition form, `act.ext.tr` will be defined
based on its syntax, and `act.do`, `act` and `act.ext` will be defined
using `Transition.toVeilM`. -/
def Module.defineTransition (mod : Module) (pi : ProcedureInfo) (br : Option (TSyntax `Lean.explicitBinders)) (t : Term) (stx : Syntax) : CommandElabM Module := do
  -- Obtain `extraParams` so we can register the action
  let actionBinders ← (← mod.declarationBaseParams (.procedure pi)).mapM (·.binder)
  let (extraParams, eTr) ← liftTermElabMWithBinders actionBinders $ fun vs => elabTransitionTerm vs pi br t
  let eDo ← liftTermElabM do
    let tmp ← withVeilModeVar BinderInfo.implicit fun mode => do
      Meta.lambdaTelescope eTr fun xs eTrBody => do
        -- get rid of the `id` wrapper; we can do this via `dsimp`-like
        -- things, but this is more direct
        let eTrBody := match_expr eTrBody with
          | id _ a => a
          | _ => eTrBody
        let body ← Meta.mkAppOptM ``Transition.toVeilM #[.some mode, .none, .none, .none, .none, .some eTrBody]
        let body ← (Simp.dsimp #[``Transition.toVeilM]) body
        Meta.mkLambdaFVars (#[mode] ++ xs) body.expr
    instantiateMVars tmp
  -- FIXME: How to define the `l` in `ps`? Might need to change the definition of `ProcedureSpecification`
  let ps := ProcedureSpecification.mk pi (← explicitBindersToParameters br pi.name) extraParams .none /- this is not correct -/ ⟨t.raw⟩ stx
  let _nmTr_fullyQualified ← liftTermElabM $ addVeilDefinition (toTransitionName <| toActName pi.name .external) eTr
  mod.defineProcedureCore pi eDo ps false

end Veil
