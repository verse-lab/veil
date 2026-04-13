import Lean
import Veil.Frontend.DSL.Action.Syntax
import Veil.Frontend.DSL.Action.DoNotation
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Util
import Veil.Util.Meta
import Mathlib.Tactic.Push
import Veil.Util.ReplacingInstances
import Veil.Frontend.DSL.Tactic

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

/-- `[unchanged_fields|s| id1 id2 ...]` does something similar to `unchanged`,
but it also casts the fields to their canonical types using `id`. This is
useful when synthesizing `DecidableEq` instances for fields. -/
elab_rules : term
  | `([unchanged_fields|$s:str| $ids:ident*]) => do
    let mod ← getCurrentModule
    let eqs ← do
      let sigs := mod.signature
      ids.filterMapM fun f => do
        let ty? ← (sigs.find? fun s => s.name == f.getId).mapM (·.typeStx)
        ty?.mapM fun ty => `((@$(mkIdent ``id) $ty $f:ident) = $(mkIdent <| f.getId.appendAfter s.getString))
    let eqConj ← repeatedAnd eqs
    elabTerm eqConj (mkSort .zero)

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

-- FIXME: Unfolding ghost relation as below is not very good. We might want
-- a new design of `LocalRProp` and have some meta theory over it to avoid
-- such unfolding.
open Meta in
/-- Generate a theorem `wp_local_eq` that rewrites the raw `wp` body to a
simplified form with `LocalRProp.core` in the postcondition and substate/field-
representation machinery largely eliminated.

General idea: consider `act.ext.wp`.
- Step 1: show that
  ```
  act.ext.wp (ρ := ρ) (σ := σ) post r s ↔
  act.ext.wp (ρ := Theory) (σ := State χ) (fun u _ st => post u r (setIn st s)) (readFrom r) (getFrom s)
  ```
  By unfolding and simplifying the *latter* and see if after simplification it `isDefEq`
  *(modulo decidable instances)* to the former. Note that the latter needs simplification
  because the `getFrom` and `setIn` might bring back some already simplified things
  in `act.ext.wp`. For example, consider `act.ext.wp post r s = post r s`. Then
  the latter reduces to `post r (setIn (getFrom s) s)`, which is not definitionally equal
  to the former, but after simplification it is.
- Step 2: changing the `(fun u _ st => post u r (setIn st s))` into
  ```
  fun u _ st => Theory.casesOn (readFrom r) <|
    State.casesOn (getFrom st) fun ... =>
    let ... := (χ_rep _).get ...
    LocalRProp.core u ... ...
  ```
  by using `LocalRProp.core_eq` and `substateSimp`. This step does not require unfolding
  `act.ext.wp`.
- Step 3: show that
  ```
  act.ext.wp (ρ := Theory) (σ := State χ) (fun u _ st => ... LocalRProp.core ...) (readFrom r) (getFrom s) ↔
  act.ext.wp (ρ := Theory) (σ := State FieldAbstractType)
    (fun u _ st => ... LocalRProp.core ...)   -- without (χ_rep _).get let-bindings
    (readFrom r)
    (State.casesOn (getFrom s) fun ... =>
      let ... := (χ_rep _).get ...
      (⟨...⟩ : State FieldAbstractType))
  ```
  by doing `dsimp -zeta [instIsSubStateOfRefl, ...]` + `simp [get_set_idempotent']`
  on the *former* expression. Currently it also unfolds ghost relations since the content
  of ghost relations also need simplification.

Special note: this simplification also incorporates a lightweight `Decidable` neutralization
step. It's required since the `Decidable` instance arguments will not have matching
types after specializing `ρ`/`σ` to other types. (E.g., a `Decidable` instance argument
for the original `wp` can have type `(s : σ) → ...`, but after specialization it cannot
be an argument of the new `wp`.) This issue might be resolved from a different angle by
doing certain generalization step when generating the `Decidable` instances, but that's
more complicated. Here we are only transforming a fully applied `wp` into a "downstream"
`Prop` for verification, so whether the `Decidable` instances are computational should
not matter much.

Special note: for transition-generated WPs, we skip Step 3 since they are typically in
the shape of `∀ (s : State χ), ...`, for which proving `↔` might be impossible.
-/
private def defineWpLocalEq (mod : Module) (nm : Name) (originalWpApp : Expr) (wpAppAfterSimp : Meta.Simp.Result)
    (vs : Array Expr) (handler post : Expr)
    (dk : DeclarationKind) (wpDef_fqn : Name) (notFromTransition? : Bool) : TermElabM Unit := do
  -- NOTE: Transition-generated WPs are typically in the shape of `∀ (s : State χ), ...`,
  -- for which proving `↔` in step 3 might be impossible, and consequently, the tactic workflow
  -- needs to be different based on whether step 3 is done. This makes things
  -- complicated, so we just skip the whole `wp_local_eq` generation for transition-generated WPs.
  unless notFromTransition? do
    return

  -- FIXME: this way of obtaining the arguments required by `LocalRPropTC` is hacky
  let vs' := vs.take mod.parameters.size
  let localRPropTCArgName := mkVeilImplementationDetailName `localRPropTC
  let localRPropTCArgIdent := mkIdent localRPropTCArgName
  let localRPropTCFqn ← resolveGlobalConstNoOverloadCore localRPropTCName
  -- `post : RProp Unit ρ σ`; apply to `()` to get `SProp ρ σ` for the new `LocalRProp` typeclass
  let localRPropTCArg ← mkAppOptM localRPropTCFqn (vs'.map Option.some |>.push (mkApp post (mkConst ``Unit.unit)))
  withLocalDecl localRPropTCArgName BinderInfo.instImplicit localRPropTCArg fun inst => do
    -- Further telescope into r : ρ and s : σ
    let originalWpApp ← etaExpand originalWpApp
    lambdaTelescope originalWpApp fun rs originalWpAppBody => do
      if rs.size != 2 then
        throwError "defineWpLocalEq: expected body to have exactly 2 lambda binders (r, s), got {rs.size}"
      let (r, s) := (rs[0]!, rs[1]!)

      -- Get params
      let (allModParams, actualParams) ← mod.declarationAllParams nm dk
      let allParams := allModParams ++ actualParams
      let readFromArg ← mkAppM ``readFrom #[r]
      let getFromArg ← mkAppM ``getFrom #[s]
      let theoryType ← (inferType readFromArg >>= instantiateMVars)
      let stateType ← (inferType getFromArg >>= instantiateMVars)

      let uName := mkVeilImplementationDetailName `u
      let thName := mkVeilImplementationDetailName `th
      let stName := mkVeilImplementationDetailName `st
      let uIdent := mkIdent uName
      let thIdent := mkIdent thName
      let stIdent := mkIdent stName

      -- ===== Step 1 (generalize state) =====
      let (curTarget, proof) ← generalizeState
        allParams readFromArg getFromArg theoryType stateType
        uName thName stName handler post r s wpDef_fqn wpAppAfterSimp vs

      -- ===== Step 2 (LocalRProp): apply core_eq + substateSimp =====
      let (curTarget, proof) ← applyLocalRProp curTarget proof nm

      -- ===== Step 3 (eliminate field rep) =====
      let (curTarget, proof) ←
        if mod._useFieldRepTC then
          eliminateFieldRep curTarget proof nm
            allParams theoryType stateType
            uIdent thIdent stIdent localRPropTCArgIdent
            readFromArg getFromArg handler wpDef_fqn vs
        else
          pure (curTarget, proof)

      -- Register theorem: ∀ (vs handler post inst r s), rawBody = curResult.expr
      let fvars := (vs ++ #[handler, post, inst, r, s])
      let eqStatement ← instantiateMVars $ ← mkForallFVars fvars (← mkEq originalWpAppBody curTarget)
      let eqProof ← do
        -- NOTE: `wpAppAfterSimp` DOES NOT have `r` and `s`, so need to do a congruence here
        let pf ← do
          let pfPre ← wpAppAfterSimp.getProof
          let pfPreCongr ← mkCongrFun pfPre r
          let pfPreCongr ← mkCongrFun pfPreCongr s
          mkEqTrans pfPreCongr proof
        instantiateMVars $ ← mkLambdaFVars fvars pf
      trace[veil.debug] "final eq statement: {eqStatement}"
      let _ ← do
        let attr ← elabAttr $ ← `(Parser.Term.attrInstance| wpLOSimp ↓ )
        addVeilTheorem (toWpLocalEqName nm) eqStatement eqProof (attr := #[attr])
where
  /-- Simplify using the locally assumed `LocalRProp` instance for `post` *only*. -/
  buildLocalRPropSimp : TermElabM Simplifier := do
    let ctx ← mkVeilSimpCtx #[]
    let simpTerm ← `(term| $(mkIdent `LocalRProp.core_eq) ($(mkIdent `self) := by assumption))
    let arr := #[(simpTerm, (← mkFreshUserName `LocalRProp.core_eq))]
    let ctx' ← elabSimpArgForTerms ctx arr
    pure <| Simp.simpCore ctx'
  toAbstractStateBodyStx (scrutinee abstractStateSortTerm : Term) : TermElabM Term := do
    mod.withTheoryAndStateTermTemplate
      [(.state .none "_conc", scrutinee, false)]
      (some (← `($stateIdent $abstractStateSortTerm)))
      (fun _ stateFields => `(⟨$[$stateFields],*⟩))
  /-- A meta-level construction for turning a `x : State χ` into `State FieldAbstractType`. -/
  toAbstractStateFun (abstractStateSortTerm : Term) (stateType abstractStateTypeExpr : Expr) : TermElabM Expr := do
    let stIdent := mkVeilImplementationDetailIdent `st    -- locally used here
    let body ← toAbstractStateBodyStx stIdent abstractStateSortTerm
    let argTy ← `($stateIdent $fieldConcreteType)
    let funTerm ← `(fun ($stIdent : $argTy) => $body)
    let funTypeExpr ← mkArrow stateType abstractStateTypeExpr
    let funExpr ← withoutErrToSorry $ elabTermAndSynthesize funTerm (some funTypeExpr)
    pure funExpr
  isDefEqModuloDecidableInstances (e1 e2 : Expr) : MetaM (Option <| Option Expr) := do
    if ← isDefEq e1 e2 then
      return some none
    let e1 ← whnf e1
    let e2 ← whnf e2
    let r1 ← (Simp.simp #[``Veil.Util.neutralizeDecidableInstGeneral]) e1
    let r2 ← (Simp.simp #[``Veil.Util.neutralizeDecidableInstGeneral]) e2
    if ← isDefEq r1.expr r2.expr then
      -- Return the proof that `e1` = `e2`
      -- `r1.proof : e1 = r1.expr, r2.proof : e2 = r2.expr`
      -- So `Eq.trans (r1.proof) (Eq.symm (r2.proof)) : e1 = e2`
      let pf1 ← r1.getProof
      let pf2 ← r2.getProof >>= mkEqSymm
      let pf ← mkEqTrans pf1 pf2
      return some (some pf)
    else
      return none
  specializeArgsForStateχ (allParams : Array Parameter) (vs : Array Expr) (theoryType stateType : Expr) : TermElabM (Array <| Option Expr) := do
    allParams.zipWithM (bs := vs) fun p v => do
      match p.kind with
      | .backgroundTheory => pure <| some theoryType        -- NOTE: Without this, there seems to be some unification issue
      | .environmentState => pure <| some stateType
      | .moduleTypeclass .backgroundTheory | .moduleTypeclass .environmentState => pure none
      | .definitionParameter _ .typeclass =>
        -- If `v` is a `Decidable`, then skip
        let ty ← inferType v
        if ty.getForallBody.getAppFn'.isConstOf ``Decidable then pure none else pure <| some v
      | _ => pure <| some v
  specializeArgsForStateAbstract (allParams : Array Parameter) (vs : Array Expr)
    (theoryType abstractStateTypeExpr abstractStateSortExpr : Expr) : TermElabM (Array <| Option Expr) := do
    allParams.zipWithM (bs := vs) fun p v => do
      match p.kind with
      | .backgroundTheory => pure <| some theoryType
      | .environmentState => pure <| some abstractStateTypeExpr
      | .fieldConcreteType => pure <| some abstractStateSortExpr
      | .moduleTypeclass .fieldRepresentation
      | .moduleTypeclass .lawfulFieldRepresentation
      | .moduleTypeclass .backgroundTheory | .moduleTypeclass .environmentState => pure none
      | .definitionParameter _ .typeclass =>
        -- If `v` is a `Decidable`, then skip
        let ty ← inferType v
        if ty.getForallBody.getAppFn'.isConstOf ``Decidable then pure none else pure <| some v
      | _ => pure <| some v
  /-- Step 1: Construct the wp specialized to `(Theory, State χ)` with reflexive
  substate instances, adjusted post (`fun u _ st => post u r (setIn st s)`),
  and `readFrom r`/`getFrom s`. -/
  generalizeState (allParams : Array Parameter)
      (readFromArg getFromArg theoryType stateType : Expr)
      (uName thName stName : Name)
      (handler post r s : Expr) (wpDef_fqn : Name)
      (wpAppAfterSimp : Meta.Simp.Result) (vs : Array Expr)
      : TermElabM (Expr × Expr) := do
    let step1AllArgs ← specializeArgsForStateχ allParams vs theoryType stateType
    let step1Post ← withLocalDeclsDND #[(uName, mkConst ``Unit), (thName, theoryType), (stName, stateType)] fun arr => do
      let setInSt ← mkAppM ``setIn #[arr[2]!, s]
      mkLambdaFVars arr (mkAppN post #[arr[0]!, r, setInSt])
    let step1Target ← Tactic.classical <|
      mkAppOptM wpDef_fqn <| step1AllArgs ++ #[some handler, some step1Post, some readFromArg, some getFromArg]
    trace[veil.debug] "step 1 target: {step1Target}"
    let step1Simp := (Simp.unfold #[wpDef_fqn] |>.andThen (evalOpenClassical ∘ Simp.simp #[`substateSimp]))
    let step1Result ← step1Simp step1Target
    let source := mkAppN wpAppAfterSimp.expr #[r, s]
    let some decidableNeutralizationPf ← isDefEqModuloDecidableInstances source step1Result.expr
      | throwError m!"wp_local_eq step 1 (generalize state) failed, not definitionally equal\n  source: {source}\n  step1Result: {step1Result.expr}"
    -- Goal: `source = step1Target`
    let proof ← do
      -- `pf1 : step1Target = step1Result.expr`
      let pf1 ← step1Result.getProof
      -- `pf1Symm : step1Result.expr = step1Target`
      let pf1Symm ← mkEqSymm pf1
      match decidableNeutralizationPf with
      | none => pure pf1Symm
      | some pf2 => do
        -- `pf2 : source = step1Result.expr`
        mkEqTrans pf2 pf1Symm
    return (step1Target, proof)
  /-- Step 2: Apply `LocalRProp.core_eq` + `substateSimp` to replace the
  postcondition with `inst.core`. -/
  applyLocalRProp (source proof : Expr) (nm : Name) : TermElabM (Expr × Expr) := do
    let step2Simp ← do
      let localRPropSimp ← buildLocalRPropSimp
      pure <| localRPropSimp |>.andThen (evalOpenClassical ∘ Simp.simp #[`substateSimp])
    let step2Result ← step2Simp source
    if step2Result.expr == source then
      throwError s!"wp_local_eq step 2 (LocalRProp) had no effect for {nm}"
    let proof ← mkEqTrans proof (← step2Result.getProof)
    return (step2Result.expr, proof)
  getAbstractStateRelated (stateType : Expr) : TermElabM (Term × Expr × Expr) := do
    let sortIdents ← mod.uninterpretedParamIdents
    -- NOTE: If possible, the following should be changed into `Expr`-level manipulation
    let abstractStateSortTerm ← `($fieldAbstractDispatcher $sortIdents*)
    let abstractStateSortExpr ← withoutErrToSorry $ elabTermAndSynthesize abstractStateSortTerm none
    -- kind of hacky here
    let abstractStateTypeExpr := mkApp stateType.getAppFn' abstractStateSortExpr
    pure (abstractStateSortTerm, abstractStateSortExpr, abstractStateTypeExpr)
  step3PostTerm (uIdent thIdent stIdent localRPropTCArgIdent : Ident) (abstractStateSortTerm : Term) : TermElabM Term := do
    let step3PostBody ← mod.withTheoryAndStateTermTemplate
      [(.theory, thIdent, false), (.state .none .none, stIdent, false)]
      (some (← `(Prop)))
      (fun theoryFields stateFields => do
        pure <| Syntax.mkApp (← `($localRPropTCArgIdent.$(mkIdent `core))) (theoryFields ++ stateFields))
      (stateSortTerm := some abstractStateSortTerm)
      (considerFieldRepTC := false)
    `(fun $uIdent $thIdent $stIdent => $step3PostBody)
  /-- Step 3: Construct the target at abstract field types using
  `withTheoryAndStateTermTemplate`, then prove equality by simplifying
  the Step 2 result with `dsimp -zeta` + `get_set_idempotent'`. -/
  eliminateFieldRep (source proof : Expr) (nm : Name)
      (allParams : Array Parameter)
      (theoryType stateType : Expr)
      (uIdent thIdent stIdent : Ident)
      (localRPropTCArgIdent : Ident)
      (readFromArg getFromArg : Expr)
      (handler : Expr) (wpDef_fqn : Name) (vs : Array Expr)
      : TermElabM (Expr × Expr) := do
    let (abstractStateSortTerm, abstractStateSortExpr, abstractStateTypeExpr) ← getAbstractStateRelated stateType
    -- (a) Abstract post: fun u th st => Theory.casesOn th ... => State.casesOn st ... => inst.core ...
    let step3Post ← do
      let step3PostTerm ← step3PostTerm uIdent thIdent stIdent localRPropTCArgIdent abstractStateSortTerm
      let step3PostTypeExpr ← mkArrowN #[mkConst ``Unit, theoryType, abstractStateTypeExpr] (Expr.sort 0)
      withoutErrToSorry $ elabTermAndSynthesize step3PostTerm (some step3PostTypeExpr)
    -- (b) Abstract pre-state: State.casesOn (getFrom s) fun f_conc... => let f := (χ_rep _).get f_conc; ...; ⟨f...⟩
    let step3PreState ← do
      let funExpr ← toAbstractStateFun abstractStateSortTerm stateType abstractStateTypeExpr
      Core.betaReduce <| mkApp funExpr getFromArg
    -- (c) Build wp application with abstract types
    let step3AllArgs ← specializeArgsForStateAbstract allParams vs theoryType abstractStateTypeExpr abstractStateSortExpr
    let step3Target ← Tactic.classical <|
      mkAppOptM wpDef_fqn <| step3AllArgs ++ #[some handler, some step3Post, some readFromArg, some step3PreState]
    trace[veil.debug] "step 3 target: {step3Target}"
    -- (d) Prove source = step3Target by simplifying source
    let step3Simp ← do
      let dsimpSubstate : Simplifier :=
        Simp.dsimp #[``instIsSubStateOfRefl, ``instIsSubReaderOfRefl, ``id, `ghostRelSimp] { zeta := false }    -- note the ``ghostRelSimp` here
      let getSetSimp ← simplifierGetSetForFieldRepTC
      -- let localRPropSimp : Simplifier := (evalOpenClassical ∘ (Simp.simp #[`LocalRProp.core_eq]))
      pure <| Simp.unfold #[wpDef_fqn] |>.andThen dsimpSubstate
        -- |>.andThen localRPropSimp
        |>.andThen (evalOpenClassical ∘ getSetSimp)
    let step3SimpResult ← step3Simp source
    -- unless ← isDefEq step3SimpResult.expr step3Target do
    let some decidableNeutralizationPf ← isDefEqModuloDecidableInstances step3SimpResult.expr step3Target
      | throwError m!"wp_local_eq step 3 (eliminate field rep) failed for {nm}\n  step3SimpResult: {step3SimpResult.expr}\n  step3Target: {step3Target}"
    let subproof ← do
      -- `pf1 : source = step3SimpResult.expr`
      let pf1 ← step3SimpResult.getProof
      match decidableNeutralizationPf with
      | none => pure pf1
      | some pf2 => do
        -- `pf2 : step3SimpResult.expr = step3Target`
        mkEqTrans pf1 pf2
    let proof ← mkEqTrans proof subproof
    return (step3Target, proof)

/-- **Pre-compute** the `wp` for the given action, store it in the `act.wp`
definition, and prove `act.wp_eq` which states that this definition is equal to
`wp act post`.

We can then rewrite/simp using `act.wp_eq` to not have to recompute the WP
for every VC. This is an optimisation — Veil would work without it, but it
would be significantly slower. -/
private def defineWp (mod : Module) (nm : Name) (mode : Mode) (dk : DeclarationKind) (notFromTransition? : Bool) : TermElabM Unit := do
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
      let #[handler, post] := xs | throwError "defineWp: expected 2 arguments, got {xs.size}"
      let wpSimpAttrHigh ← elabAttr $ ← `(Parser.Term.attrInstance| wpSimp ↓ high)
      proveEqABoutBody body wpDef_fqn (vs ++ xs) (← resBody.getProof) (toWpEqName nm) #[wpSimpAttrHigh]

      if mod._useLocalRPropTC then
      if dk matches .derivedDefinition .actionLike _ then
      if mode matches .external then
      if veil.experimental.generateWpLocalEq.get (← getOptions) then
        try
          defineWpLocalEq mod nm body resBody vs handler post dk wpDef_fqn notFromTransition?
        catch ex =>
          -- For non-transition wps, warn if any step fails (all 3 steps expected)
          logWarning m!"unable to generate wp_local_eq for {nm}: {ex.toMessageData}"

-- NOTE: This is for simplifying `.tr` form definitions
-- FIXME: This is probably not the best place to put this
attribute [push] apply_ite

/-- The template for proving `derive_eq` theorems for transitions. -/
private theorem derive_eq_template {act : VeilM m ρ σ α}
  {spec : (Int → Prop) → VeilSpecM ρ σ α}
  {tr : Transition ρ σ}
  (heq1 : ∀ (handler : Int → Prop) (post : RProp α ρ σ),
    [IgnoreEx handler| wp act post ] = spec handler post)
  (heq2 : VeilSpecM.toTransitionDerived (spec fun _ => True) = tr) :
  act.toTransitionDerived = tr :=
  Eq.trans (congrArg VeilSpecM.toTransitionDerived (heq1 (fun _ => True) |> funext)) heq2

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
          |>.andThen (Simp.simp #[`wpSimp, ``and_true, ``true_and])   -- for rewriting with WP equality theorem, and some minor things
          |>.andThen (Mathlib.Tactic.Push.pushCore (.const ``Not) {} none)    -- for pushing negations down to get more rewriting opportunities
        let resBody ← withTraceNode (`veil.perf.extract.trSimp ++ nm) (fun _ => return s!"trSimp {nm}") do simp body
        -- (3) Construct the expression
        -- The expression for `act.ext.tr`; **TODO** register as a derived definition
        let trExpr ← instantiateMVars $ ← Meta.mkLambdaFVars (vs ++ xs) resBody.expr
        let attrs ← #[`actSimp, `nextSimp].mapM (fun attr => do elabAttr $ ← `(Parser.Term.attrInstance| $(Lean.mkIdent attr):ident))
        let trDef_fqn ← addVeilDefinition (toTransitionName nm) trExpr (attr := #[{name := `reducible}] ++ attrs)
        -- (4) Prove the equality theorem
        proveEqABoutBody body trDef_fqn (vs ++ xs) (← resBody.getProof) (toTransitionEqName nm) #[]
        -- (5) Prove the derived_eq theorem: VeilM.toTransitionDerived act.ext = act.ext.tr
        -- by connecting `toWpEq` and `toTransitionEq` theorems
        -- Use the action's fully qualified name (nm is already the external mode name)
        let actionFqn ← getFullyQualifiedName nm
        let derivedDef ← derivedTransitionTemplate actionFqn allArgs
        -- Elaborate within the same binder context (vs are already bound)
        let derivedExpr ← withoutErrToSorry $ elabTermAndSynthesize derivedDef none
        trace[veil.debug] "[{decl_name%}] derivedExpr for derived_eq: {derivedExpr}"
        let proof ← do
          let wpEq_fqn ← resolveGlobalConstNoOverloadCore (toWpEqName nm)
          let heq1 ← Meta.mkAppOptM wpEq_fqn (vs.map some)
          let trEq_fqn ← resolveGlobalConstNoOverloadCore (toTransitionEqName nm)
          let heq2 ← Meta.mkAppOptM trEq_fqn (vs.map some)
          let res ← Meta.mkAppM ``derive_eq_template #[heq1, heq2]
          pure res
        let attrs ← #[`actSimp, `nextSimp].mapM (fun attr => do elabAttr $ ← `(Parser.Term.attrInstance| $(Lean.mkIdent attr):ident))
        proveEqABoutBody derivedExpr trDef_fqn vs proof (toDerivedEqName nm) attrs

end AuxiliaryDefinitions

/-! ## Transition Weakening Lemma -/

/-- Generate the transition weakening lemma for this module. Called after `#gen_state`. -/
def Module.declareTransitionWeakeningLemma (mod : Module) : TermElabM Command := do
  let params := mod.parameters
  let paramBinders ← params.mapM (·.binder)
  let paramArgs ← params.mapM (·.arg)
  let polyParams := params.filter isPolyParam
  let polyBinders ← polyParams.mapM (·.binder)
  let polyArgs ← polyParams.mapM (·.arg)

  -- Prepare
  let sortIdents ← mod.uninterpretedParamIdents
  let abstractStateSortTerm ← `($fieldAbstractDispatcher $sortIdents*)
  let abstractStateTypeTerm ← `($stateIdent $abstractStateSortTerm)
  let theoryTy ← `($theoryIdent $sortIdents*)
  let hole ← `(term| _ )
  let specializedPolyArgs := specializeArgsForStateAbstractStx polyParams polyArgs theoryTy abstractStateTypeTerm abstractStateSortTerm hole

  -- Main variables and additional idents for proof sub-terms
  let [tr, act, pred, trDerivedEq, wpLocalEq, wpEq, r₀, s₀, s₁,
    auxhandler, auxpost, auxlocalRPropInst, auxr, auxs, auxx, auxth, auxst] :=
    [`tr, `act, `pred, `tr_derived_eq, `wp_local_eq, `wp_eq, `r₀, `s₀, `s₁,
      `handler, `post, `localRPropTC, `r, `s, `x, `th, `st].map mkVeilImplementationDetailIdent
    | unreachable!

  let absst ← AuxiliaryDefinitions.defineWpLocalEq.toAbstractStateBodyStx mod (← `($(mkIdent ``getFrom) $auxs)) abstractStateSortTerm
  let absst₀ ← AuxiliaryDefinitions.defineWpLocalEq.toAbstractStateBodyStx mod (← `($(mkIdent ``getFrom) $s₀)) abstractStateSortTerm
  let absst₁ ← AuxiliaryDefinitions.defineWpLocalEq.toAbstractStateBodyStx mod (← `($(mkIdent ``getFrom) $s₁)) abstractStateSortTerm

  -- Arguments
  let transitionTy ← `(∀ $[$polyBinders]*, $(mkIdent ``Transition) $environmentTheory $environmentState)
  let veilMStx ← `($(mkIdent ``VeilM) $(mkIdent ``Mode.external) $environmentTheory $environmentState)
  let actTy ← do
    let a := Syntax.mkApp veilMStx #[(mkIdent ``Unit)]
    `(∀ $[$polyBinders]*, $a)
  let actFullyApplied ← `(@$act $polyArgs*)
  let predTy ← do
    let intToProp ← `($(mkIdent ``Int) → Prop)
    let veilSpecMUnit ← `($(mkIdent ``VeilSpecM) $theoryTy $abstractStateTypeTerm $(mkIdent ``Unit))
    `($intToProp → $veilSpecMUnit)
  let trDerivedEqTy ← do
    let mainTy ← `($(mkIdent ``VeilM.toTransitionDerived) $actFullyApplied = @$tr $polyArgs*)
    `(∀ $[$polyBinders]*, $mainTy)
  let wpLocalEqTy ← do
    let mainTy ← do
      let wpLocalEqLhs ← `([IgnoreEx $auxhandler| $(mkIdent ``wp) $actFullyApplied $auxpost $auxr $auxs])
      let wpLocalEqRhs ← do
        let post ← AuxiliaryDefinitions.defineWpLocalEq.step3PostTerm mod auxx auxth auxst auxlocalRPropInst abstractStateSortTerm
        `($pred $auxhandler $post ($(mkIdent ``readFrom) $auxr) $absst)
      `($wpLocalEqLhs = $wpLocalEqRhs)
    let localRPropInstTypeStx ← `(@$localRPropTC $paramArgs* ($auxpost $(mkIdent ``Unit.unit)))
    `(∀ $auxhandler:ident $auxpost:ident [$auxlocalRPropInst : $localRPropInstTypeStx]
        ($auxr : $environmentTheory) ($auxs : $environmentState), $mainTy)
  let wpEqTy ← do
    let mainTy ← `([IgnoreEx $auxhandler| $(mkIdent ``wp) (@$act $specializedPolyArgs*) $auxpost] = $pred $auxhandler $auxpost)
    `(∀ $auxhandler:ident $auxpost:ident, $mainTy)
  let allBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := paramBinders ++ [
    (← `(bracketedBinder| ($r₀ : $environmentTheory)) ),
    (← `(bracketedBinder| ($s₀ : $environmentState)) ),
    (← `(bracketedBinder| ($s₁ : $environmentState)) ),
    (← `(bracketedBinder| ($tr : $transitionTy)) ),
    (← `(bracketedBinder| ($act : $actTy)) ),
    (← `(bracketedBinder| ($pred : $predTy)) ),
    (← `(bracketedBinder| ($trDerivedEq : $trDerivedEqTy)) ),
    (← `(bracketedBinder| ($wpLocalEq : $wpLocalEqTy)) ),
    (← `(bracketedBinder| ($wpEq : $wpEqTy)) ),
  ]

  -- Conclusion terms
  let conclusion ← `(@$tr $polyArgs* $r₀ $s₀ $s₁ → @$tr $specializedPolyArgs* ($(mkIdent ``readFrom) $r₀) $absst₀ $absst₁)

  -- Proof sub-terms
  let transIntermediate ← `([IgnoreEx (fun _ => $(mkIdent ``True))|
      $(mkIdent ``wp) $actFullyApplied
        (fun $auxx $auxr $auxs =>
          ¬($(mkIdent ``readFrom) $auxr = $(mkIdent ``readFrom) $r₀ ∧ $absst = $absst₁))
        $r₀ $s₀])
  let declareLocalRPropInst ← do
    let auxrr := mkVeilImplementationDetailIdent `rr
    let auxss := mkVeilImplementationDetailIdent `ss
    let post ← do
      let absst ← AuxiliaryDefinitions.defineWpLocalEq.toAbstractStateBodyStx mod (← `($(mkIdent ``getFrom) $auxs)) abstractStateSortTerm
      `(fun $auxr $auxs => ¬ ($(mkIdent ``readFrom) $auxr = $auxrr ∧ $absst = $auxss))
    let ty ← `(@$localRPropTC $paramArgs* $post)
    let coreStx ← do
      let theoryFieldIdents : Array Ident := mod.immutableComponents.map fun sc => mkIdent sc.name
      let stateFieldIdents : Array Ident := mod.mutableComponents.map fun sc => mkIdent sc.name
      let fieldIdents : Array Ident := theoryFieldIdents ++ stateFieldIdents
      let fieldBinders : Array (TSyntax ``Lean.Parser.Term.funBinder) ← fieldIdents.mapM fun f =>
        `(Lean.Parser.Term.funBinder| $f)
      let body ← `(¬(⟨$[$theoryFieldIdents],*⟩ = $auxrr ∧ ⟨$[$stateFieldIdents],*⟩ = $auxss))
      mkFunSyntax fieldBinders body
    `(tactic| let _ ($auxrr : $theoryTy) ($auxss : $abstractStateTypeTerm) : $ty := {
      $(mkIdent `core):ident := $coreStx
      $(mkIdent `core_eq):ident := by intros ; dsimp
    })
  -- Build the command
  let cmd ← do
    let h := mkIdent `h
    `(command|theorem $transitionWeakeningLemma $[$allBinders]* : $conclusion := by
      $declareLocalRPropInst:tactic
      repeat rw [← $trDerivedEq:ident]
      unfold $(mkIdent ``VeilM.toTransitionDerived) $(mkIdent ``VeilSpecM.toTransitionDerived)
      simp only [$(mkIdent ``Cont.inv):ident, $(mkIdent ``Compl.compl):ident]
      contrapose
      trans $transIntermediate
      · dsimp
        conv => rhs; rw [$wpLocalEq:ident]; rw [← $wpEq:ident]; dsimp only [$(mkIdent <| localRPropTCName ++ `core):ident]
        intro $h:ident ; convert $h:ident
        try (simp ; (try rw [$(mkIdent $ stateName ++ `ext_iff):ident]) ; try simp)
      · dsimp only
        apply [IgnoreEx (fun _ => $(mkIdent ``True))| $(mkIdent ``wp_cons) ($(mkIdent `m) := $veilMStx)]
        simp only [$(mkIdent ``LE.le):ident]
        try grind
      )
  return cmd
where
  specializeArgsForStateAbstractStx (params : Array Parameter) (args : Array Term)
    (theoryStx stateStx fieldRepStx hole : Term) : Array Term :=
    params.zipWith (bs := args) fun p arg =>
      match p.kind with
      | .backgroundTheory => theoryStx
      | .environmentState => stateStx
      | .fieldConcreteType => fieldRepStx
      -- NOTE: The consideration here is that `definitionParameter` might
      -- not have correct type under different specialized types
      | .moduleTypeclass _ | .definitionParameter _ .typeclass => hole
      | _ => arg
  isPolyParam (p : Parameter) : Bool :=
    match p.kind with
    | .backgroundTheory | .environmentState | .fieldConcreteType => true
    | .moduleTypeclass .fieldRepresentation
    | .moduleTypeclass .lawfulFieldRepresentation
    | .moduleTypeclass .environmentState
    | .moduleTypeclass .backgroundTheory => true
    | _ => false

open Meta AuxiliaryDefinitions in
/-- For an action's `.ext.tr`, generate a theorem:
`act.ext.tr r s s' → act.ext.tr (readFrom r) (toAbstractState (getFrom s)) (toAbstractState (getFrom s'))`
where `toAbstractState` converts `State χ` to `State (FieldAbstractType ...)` by
applying `(χ_rep _).get` to each field. -/
private def defineTransitionAbstract (mod : Module) (nm : Name) (dk : DeclarationKind)
  (notFromTransition? : Bool) : TermElabM Unit := do
  -- The approach here is hybrid: the statement is constructed at the `Expr` level,
  -- but the proof is done by tactics.
  let trFqn ← getFullyQualifiedName (toTransitionName nm)
  let (allModParams, actualParams) ← mod.declarationAllParams nm dk
  let allParams := allModParams ++ actualParams
  let allArgs ← allParams.mapM (·.arg)
  let allBinders ← allParams.mapM (·.binder)
  elabBinders allBinders fun vs => do
    let trPartialApp ← mkAppOptM trFqn (vs.map some)
    let trPartialApp ← etaExpand trPartialApp
    lambdaTelescope trPartialApp fun rss trApp => do
      unless rss.size == 3 do
        throwError "defineTransitionAbstract: expected body to have exactly 3 lambda binders (r, s, s'), got {rss.size}"
      let (r, s, s') := (rss[0]!, rss[1]!, rss[2]!)

      let readFromArg ← mkAppM ``readFrom #[r]
      let getFromArg ← mkAppM ``getFrom #[s]
      let getFromArg' ← mkAppM ``getFrom #[s']
      let theoryType ← (inferType readFromArg >>= instantiateMVars)
      let stateType ← (inferType getFromArg >>= instantiateMVars)
      let (abstractStateSortTerm, abstractStateSortExpr, abstractStateTypeExpr) ← defineWpLocalEq.getAbstractStateRelated mod stateType

      let source := trApp
      let target ← do
        let funExpr ← defineWpLocalEq.toAbstractStateFun mod abstractStateSortTerm stateType abstractStateTypeExpr
        let preState ← Core.betaReduce <| mkApp funExpr getFromArg
        let postState ← Core.betaReduce <| mkApp funExpr getFromArg'
        let targetArgs ← defineWpLocalEq.specializeArgsForStateAbstract allParams vs theoryType abstractStateTypeExpr abstractStateSortExpr
        Tactic.classical <|
          mkAppOptM trFqn <| targetArgs ++ #[some readFromArg, some preState, some postState]
      let sourceImpTarget ← mkArrow source target

      let proof ←
        if notFromTransition? then
          proveViaTransitionWeakeningLemma sourceImpTarget nm allParams allArgs abstractStateSortTerm rss
        else
          -- For "native transitions", the proof is much easier
          proveSourceImpliesTargetForNativeTransition sourceImpTarget trFqn nm
      let allFVars := vs ++ rss
      let statement ← mkForallFVars allFVars sourceImpTarget >>= instantiateMVars
      let proof ← mkLambdaFVars allFVars proof >>= instantiateMVars
      let _ ← addVeilTheorem (toTransitionAbstractName nm) statement proof
where
  proveAndCheck (tac : Term) (ty : Expr) (nm : Name) (step : String) : TermElabM Expr := do
    try
      let pf ← withoutErrToSorry $ elabTermAndSynthesize tac ty
      check pf
      instantiateMVars pf
    catch ex =>
      throwError m!"Failed to prove {step} for {nm} in defineTransitionAbstract, goal: {ty}, proof script: {tac}, error: {ex.toMessageData}"
  -- FIXME: This piece of code is a mixture of syntax construction and `Expr` construction, kind of mess
  /-- Prove `source → target` by applying the module's `_transitionWeakeningLemma`
  with the action's `derived_eq`, `wp_local_eq`, and `wp_eq` theorems. -/
  proveViaTransitionWeakeningLemma (goal : Expr) (nm : Name) (allParams : Array Parameter)
    (allArgs : Array Term) (abstractStateSortTerm : Term) (rss : Array Expr) : TermElabM Expr := do
    let modParams := mod.parameters
    let modArgs ← modParams.mapM (·.arg)
    let polyParams := modParams.filter Module.declareTransitionWeakeningLemma.isPolyParam
    let polyArgs : Array Term := polyParams.map fun x => mkIdent <| x.name.appendAfter "_"
    let polyFunBinders ← polyParams.mapM fun x => `(Lean.Parser.Term.funBinder| $(mkIdent <| x.name.appendAfter "_"):ident)
    let hole ← `(term| _)
    let specializedArgsForTrAndAct := Module.declareTransitionWeakeningLemma.specializeArgsForStateAbstractStx allParams allArgs
      (polyParams.findIdx? (·.kind == .backgroundTheory) |>.map (polyArgs[·]!) |>.getD hole)
      (polyParams.findIdx? (·.kind == .environmentState) |>.map (polyArgs[·]!) |>.getD hole)
      (polyParams.findIdx? (·.kind == .fieldConcreteType) |>.map (polyArgs[·]!) |>.getD hole)
      hole
    let trStx ← do
      let body ← `(@$(mkIdent <| toTransitionName nm) $specializedArgsForTrAndAct*)
      mkFunSyntax polyFunBinders body
    let actStx ← do
      let body ← `(@$(mkIdent nm) $specializedArgsForTrAndAct*)
      mkFunSyntax polyFunBinders body
    let predStx ← do
      let sortIdents ← mod.uninterpretedParamIdents
      let theoryTy ← `($theoryIdent $sortIdents*)
      let abstractStateTypeTerm ← `($stateIdent $abstractStateSortTerm)
      let specializedArgsForPred := Module.declareTransitionWeakeningLemma.specializeArgsForStateAbstractStx allParams allArgs theoryTy abstractStateTypeTerm abstractStateSortTerm hole
      `(@$(mkIdent <| toWpName nm) $specializedArgsForPred*)
    let derivedEqThm := toDerivedEqName nm
    let wpLocalEqThm := toWpLocalEqName nm
    let wpEqThm := toWpEqName nm
    let [tr, act, pred, trDerivedEq, wpLocalEq, wpEq] :=
      [`tr, `act, `pred, `tr_derived_eq, `wp_local_eq, `wp_eq].map mkVeilImplementationDetailIdent
      | unreachable!
    let rssIdents ← rss.mapM fun x => do
      let userName ← x.fvarId!.getUserName
      pure <| mkIdent userName
    let h := mkIdent `h
    -- NOTE: Below, `h` is not `applied` because `__veil_neutralize_decidable_inst` might
    -- unexpectedly simplify away certain things. Also, using `__veil_neutralize_decidable_inst !`
    -- since the instances might not be fully applied
    let tac ← `(term| by
      classical
      have $h := @$transitionWeakeningLemma $modArgs* $rssIdents*
        ($tr := $trStx)
        ($act := $actStx)
        ($pred := $predStx)
        ($trDerivedEq := by intros; rw [$(mkIdent derivedEqThm):ident])
        ($wpLocalEq := by intros; rw [$(mkIdent wpLocalEqThm):ident])
        ($wpEq := by intros; rw [$(mkIdent wpEqThm):ident])
      __veil_neutralize_decidable_inst !
      exact $h
      )
    proveAndCheck tac goal nm "source → target (via transitionWeakeningLemma)"
  proveSourceImpliesTargetForNativeTransition (goal : Expr) (trFqn nm : Name) : TermElabM Expr := do
    let h := mkIdent `h
    -- Idea: the two sides should really equal modulo decidable instances
    let tac ← `(term| by
      intro $h:ident
      convert $h:ident
      dsimp only [$(mkIdent trFqn):ident]
      __veil_neutralize_decidable_inst
      rfl)
    proveAndCheck tac goal nm "source → target (native transition case)"

def Module.defineTransitionAbstractForNext (mod : Module) : TermElabM (Option Command) := do
  -- Completely syntax-based approach here
  if mod.actions.isEmpty then
    return none

  -- Prepare
  let [r₀, s₀, s₁, r₀', s₀', s₁', label] := [`r₀, `s₀, `s₁, `r₀', `s₀', `s₁', `label].map mkVeilImplementationDetailIdent | unreachable!
  let sortIdents ← mod.uninterpretedParamIdents
  let abstractStateSortTerm ← `($fieldAbstractDispatcher $sortIdents*)
  let abstractStateTypeTerm ← `($stateIdent $abstractStateSortTerm)
  let theoryTy ← `($theoryIdent $sortIdents*)
  let hole ← `(term| _ )

  let absr₀ ← `($(mkIdent ``readFrom) $r₀)
  let absst₀ ← AuxiliaryDefinitions.defineWpLocalEq.toAbstractStateBodyStx mod (← `($(mkIdent ``getFrom) $s₀)) abstractStateSortTerm
  let absst₁ ← AuxiliaryDefinitions.defineWpLocalEq.toAbstractStateBodyStx mod (← `($(mkIdent ``getFrom) $s₁)) abstractStateSortTerm

  let some dk := mod._declarations[assembledNextName]?
    | throwError "simplifyLocalRPropCore: {assembledNextName} not found in module declarations"
  let (params, _) ← mod.declarationAllParams assembledNextName dk
  let binders ← params.mapM (·.binder)
  let allBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := binders ++ [
    (← `(bracketedBinder| ($r₀ : $environmentTheory)) ),
    (← `(bracketedBinder| ($s₀ : $environmentState)) ),
    (← `(bracketedBinder| ($s₁ : $environmentState)) )]
  let actions := mod.actions
  -- Sanity check
  for act in actions do
    let _ ← resolveGlobalConstNoOverloadCore <| toTransitionAbstractName <| toExtName act.name

  let nextStx ← do
    let args ← params.mapM (·.arg)
    -- FIXME: Is this ordering of these 4 variables hardcoded?
    `(term| ∃ $label:ident, @$(mkIdent <| assembledNextName.appendAfter "'") $args* $r₀ $s₀ $label $s₁)
  let res ← actions.mapM fun s => do
    let tr := Lean.mkIdent <| toTransitionName <| toExtName s.name
    let (allModParams, actualParams) ← mod.declarationAllParams s.name s.declarationKind
    let allParams := allModParams ++ actualParams
    let allArgs ← allParams.mapM (·.arg)
    -- NOTE: This line comes from `assembleLabelCasesLemma`
    let actualArgs ← parametersToExplicitBinders actualParams
    let specializedArgs := Module.declareTransitionWeakeningLemma.specializeArgsForStateAbstractStx allParams allArgs theoryTy abstractStateTypeTerm abstractStateSortTerm hole
    let stx ← `(term| exists? $actualArgs, @$tr $specializedArgs* $r₀' $s₀' $s₁')
    pure (stx, (allArgs, actualParams))
  let (specializedActTrStxs, actArgsAndActualParams) := res.unzip
  let goalStx ← do
    let rhs ← repeatedOr specializedActTrStxs
    -- Use `letI` to avoid too many occurrences of the same huge expressions
    `(letI $r₀' := $absr₀
      letI $s₀' := $absst₀
      letI $s₁' := $absst₁
      $nextStx → $rhs)

  let tac ← do
    let simps :=
      -- let derivedEqs := actions.map fun s => toDerivedEqName <| toExtName s.name
      -- derivedEqs.map Lean.mkIdent ++ #[labelCases, assembledNext, assembledNextAct]
      #[labelCases, mkIdent <| assembledNextName.appendAfter "'"]
    let h := mkVeilImplementationDetailIdent `h
    let splitOrPat ← do
      let tmp := Array.replicate actions.size h
      `(Lean.Parser.Tactic.rcasesPatMed| $tmp:rcasesPat|*)
    let leafTacs ← do
      let rightTac ← `(tactic| right )
      let leftTac ← `(tactic| left )
      let res ← actions.zip actArgsAndActualParams |>.mapIdxM fun i (s, allArgs, actualParams) => do
        let pathFindingTac ← do
          let seq := Array.replicate i rightTac
          let seq := if i == actions.size - 1 then seq else seq.push leftTac
          if seq.isEmpty then `(tactic| skip) else `(tactic| ($seq*) )
        let existsTac ← if actualParams.isEmpty then
          `(tactic| skip )
        else
          let args := actualParams.map fun p => mkIdent p.name
          let casesPat ← do
            let tmp := args.push h
            `(Lean.Parser.Tactic.rcasesPatMed| ⟨$tmp,*⟩)
          `(tactic| (rcases $h:ident with $casesPat ; exists $args,*) )
        let revertAndApplyTac ← do
          -- NOTE: As somewhere mentioned, directly `apply` can sometimes fail due to
          -- failing to synthesize instance of instance does not match, so need to
          -- be very careful here
          let thm ← `(@$(mkIdent <| toTransitionAbstractName <| toExtName s.name) $allArgs* $r₀ $s₀ $s₁)
          let tmp := mkIdent `tmp   -- using `mkVeilImplementationDetailIdent` here causes some problem
          `(tactic| (revert $h:ident ; have $tmp := $thm ; __veil_neutralize_decidable_inst ! ; exact $tmp) )
        pure #[pathFindingTac, existsTac, revertAndApplyTac]
      pure res.flatten
    `(term| by
      intro $h:ident
      simp only [$[$simps:ident],*] at $h:ident
      rcases $h:ident with $splitOrPat
      $leafTacs*
    )
  `(open $(mkIdent `Classical):ident in theorem $(mkIdent <| toTransitionAbstractName assembledNextName) $allBinders* : $goalStx := $tac)

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
    let (decInstsMvars, e) ← elabTermDecidable pi.name stx (dsimpSubReaderSubStateRefl >=> foldFieldRepresentationGet)
    let (decInsts, mvars) := decInstsMvars.unzip
    let e ← Meta.mkLambdaFVarsImplicit ((if addModeArg then #[mode] else #[]) ++ vs ++ mvars) e (binderInfoForMVars := BinderInfo.instImplicit) >>= instantiateMVars
    -- `e` should not contain any metavariable; capture the error here
    if e.hasMVar then
      throwError "mvar(s) exist in the elaborated expression. Consider adding more type annotations."
    -- NOTE: Doing `dsimp` on `act.do`, `act` or `act.ext` will inline
    -- `let` bindings, which _might_ lead to performance issues
    return (← decInsts.mapIdxM (fun i p => mvarToParam pi.name i p), e)
  catch ex =>
    throwError "Error in action {pi.name}: {← ex.toMessageData.toString}"
where
  mvarToParam (inAction : Name) (i : Nat) (typeSyntax : Term) : TermElabM Parameter := do
    return { kind := .definitionParameter inAction .typeclass, name := Name.mkSimple s!"{inAction}_dec_{i}", «type» := typeSyntax, userSyntax := .missing }

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
      let _nmDo_fullyQualified ← addVeilDefinition nmDo eDo (attr := #[{name := `reducible}]) (compile := !(← isModelCheckCompileMode))
      let (nmInt, eInt) ← elabProcedureInMode pi Mode.internal
      let _nmInt_fullyQualified ← addVeilDefinition nmInt eInt (attr := #[{name := `actSimp}]) (compile := !(← isModelCheckCompileMode))
      AuxiliaryDefinitions.defineWp mod nmInt .internal intKind deriveTransition?

      -- Procedures are never considered in their external view, so save some
      -- time by not elaborating those definitions.
      if pi matches .initializer | .action _ _ then do
        let (nmExt, eExt) ← elabProcedureInMode pi Mode.external
        let _nmExt_fullyQualified ← addVeilDefinition nmExt eExt (attr := #[{name := `actSimp}]) (compile := !(← isModelCheckCompileMode))
        unless (← isModelCheckCompileMode) do
          AuxiliaryDefinitions.defineWp mod nmExt .external extKind deriveTransition?
          if deriveTransition? then
            AuxiliaryDefinitions.defineTransition mod nmExt extKind
          if mod._useFieldRepTC then
            try
              defineTransitionAbstract mod nmExt extKind deriveTransition?
            catch ex =>
              logWarning m!"unable to generate transition weakening theorem for {nmExt}: {ex.toMessageData}"
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
  let _nmTr_fullyQualified ← liftTermElabM $ addVeilDefinition (toTransitionName <| toActName pi.name .external) eTr (compile := !(← isModelCheckCompileMode))
  mod.defineProcedureCore pi eDo ps false

end Veil
