import Veil.Frontend.DSL.Module.Util.LocalTheoryProp

open Lean Parser Elab Command Term Meta Tactic

namespace Veil

/-! ## LocalRProp Typeclass Declaration -/

-- NOTE: `LocalRPropTC` actually does not have to be about `Prop`s, but currently
-- we only use it for `Prop`s, so it is dealt with as such.

-- NOTE: Previously, `LocalRPropTC` had an extra `{α : Type}` parameter and
-- took `post : RProp α ρ σ` instead of `post : SProp ρ σ`. In practice, `α`
-- was always instantiated to `Unit`, so it has been removed to simplify the
-- code. This file is planned for a rewrite; see also `Action/Elaborators.lean`
-- which still carries `Unit`-typed `u` variables related to the old design.

/-- Declare the `LocalRProp` typeclass for the module.
Its general form is:
```lean
class LocalRPropTC /- module parameters -/ (post : SProp ρ σ)
where
  core :
    /- types of fields of `Theory`, connected with `→` -/ →
    /- types of _canonical_ fields of `State`, connected with `→` -/ → Prop
  core_eq : ∀ (th : ρ) (st : σ),
    post th st = core /- fields of `Theory` -/ /- _canonical_ fields of `State` -/
```
-/
def Module.declareLocalRPropTC (mod : Module) : MetaM (List Command) := do
  -- this can be given fewer parameters, but for simplicity we give it all of them
  let params := mod.parameters
  let paramBinders ← params.mapM (·.binder)
  -- build binders
  let post ← Lean.mkIdent <$> mkFreshUserName `post
  let core := mkIdent `core ; let core_eq := mkIdent `core_eq
  -- build the type of `core`
  let coreType ← do
    let theoryFields ← mod.immutableComponents.mapM (·.getSimpleBinder >>= getSimpleBinderType)
    let stateFields ← mod.mutableComponents.mapM (·.getSimpleBinder >>= getSimpleBinderType)
    mkArrowStx ((theoryFields ++ stateFields).toList) (← `(term| Prop ))
  -- build the type of `core_eq`
  let th ← Lean.mkIdent <$> mkFreshUserName `th
  let st ← Lean.mkIdent <$> mkFreshUserName `st
  let coreEqType ← do
    let body ← mod.withTheoryAndStateTermTemplate [(.theory, th, true), (.state .none "_conc", st, true)] (some $ ← `(term| Prop)) fun theoryFieldNames stateFieldNames =>
      pure <| Syntax.mkApp core (theoryFieldNames ++ stateFieldNames)
    `(term| ∀ ($th : $environmentTheory) ($st : $environmentState),
    $post $th $st = $body)
  let cmd1 ← do
    let binders := paramBinders.push (← `(bracketedBinder| ($post : $(mkIdent ``SProp) $environmentTheory $environmentState) ))
    `(command| class $localRPropTC $[$binders]* where
      $core:ident : $coreType
      $core_eq:ident : $coreEqType)
  let cmd2 ← `(command| attribute [$(mkIdent `wpSimp):ident] $(mkIdent <| localRPropTCName ++ `core):ident)
  -- Instance for composing `LocalRProp` over `∧`:
  -- Given `[LocalRProp p]` and `[LocalRProp q]`, derive `LocalRProp (fun th st => p th st ∧ q th st)`.
  -- This allows `Invariants` (a conjunction) to automatically get a `LocalRProp` instance.
  let cmd3 ← do
    let implBinders ← paramBinders.mapM mkImplicitBinder
    let p ← Lean.mkIdent <$> mkFreshUserName `p ; let q ← Lean.mkIdent <$> mkFreshUserName `q
    let inst1 ← Lean.mkIdent <$> mkFreshUserName `inst1 ; let inst2 ← Lean.mkIdent <$> mkFreshUserName `inst2
    let args ← params.mapM (·.arg)
    let fieldNames : Array Ident := (mod.immutableComponents ++ mod.mutableComponents).map fun sc => mkIdent sc.name
    let fieldBinders : Array (TSyntax ``Lean.Parser.Term.funBinder) ← fieldNames.mapM fun f => `(Lean.Parser.Term.funBinder| $f)
    let fieldArgs : Array Term ← fieldNames.mapM fun f => `(term| $f)
    let coreFn ← mkFunSyntax fieldBinders (← `(term| $inst1.$(mkIdent `core) $fieldArgs* ∧ $inst2.$(mkIdent `core) $fieldArgs*))
    `(command| scoped instance $[$implBinders]* ($p $q : $(mkIdent ``SProp) $environmentTheory $environmentState)
        [$inst1 : @$localRPropTC $args* $p] [$inst2 : @$localRPropTC $args* $q] :
        @$localRPropTC $args* (fun $th $st => $p $th $st ∧ $q $th $st) where
      $core:ident := $coreFn
      $core_eq:ident := fun $th $st => $(mkIdent ``congrArg₂) $(mkIdent ``And) ($inst1.$(mkIdent `core_eq) $th $st) ($inst2.$(mkIdent `core_eq) $th $st))
  return [cmd1, cmd2, cmd3]

/-! ## Simplification Infrastructure -/

private structure StatePredicateLayout where
  params : Array Parameter
  thPos : Nat
  stPos : Nat

private def Module.localDeclarationName? (mod : Module) (fullName : Name) : Option Name :=
  if mod._declarations.contains fullName then
    some fullName
  else
    -- `_declarations` stores the names as module-local DSL names, while the
    -- simplifier sees the fully qualified Lean constants added under the
    -- current namespace. Keep only the declaration suffix before consulting
    -- the metadata table.
    let localName := fullName.updatePrefix Name.anonymous
    if mod._declarations.contains localName then some localName else none

private def Module.statePredicateExprParams [Monad m] [MonadQuotation m] [MonadError m]
    (mod : Module) (nm : Name) (dk : DeclarationKind) : m (Array Parameter) := do
  -- TODO Replace this reconstruction with a systematic Parameter-layout API.
  -- Locality needs the exact binder order of generated Lean declarations, but
  -- assertion, ghost, and assembled-definition metadata currently split user
  -- params, extracted Decidable params, and generated theory/state binders
  -- differently.
  let (baseParams, extraParams, actualParams) ← mod.declarationSplitParams nm dk
  -- TODO State assertions and assembled invariant-like definitions do have
  -- theory/state binders in their generated Lean declarations. Assertions get
  -- defaults from `withTheoryAndState` (`:= by veil_exact_theory/state`), while
  -- `Invariants`/`Safeties` get explicit `rd`/`st` binders from assembly.
  -- Their metadata does not record those binders as `Parameter`s, unlike ghost
  -- definitions where `defineGhostDefinition` tags `thstBinders` as
  -- `.theoryArg`/`.stateArg`. The synthetic params below paper over that gap.
  let thParam := { kind := .theoryArg, name := `th, «type» := ← `(term| $environmentTheory), userSyntax := .missing }
  let stParam := { kind := .stateArg, name := `st, «type» := ← `(term| $environmentState), userSyntax := .missing }
  match dk with
  | .stateAssertion k =>
    unless isStateAssertionWithState k do
      throwError "{nm} is not a state assertion with a state argument"
    pure <| baseParams ++ extraParams ++ #[thParam, stParam]
  | .derivedDefinition (.ghost true) _ =>
    -- FIXME: Relax this to support general ghost definitions
    let (userParams, thstParams) := actualParams.partition fun p => p.kind != .theoryArg && p.kind != .stateArg
    unless (thstParams.any (·.kind == .theoryArg) && thstParams.any (·.kind == .stateArg)) do
      throwError "state ghost relation {nm} does not carry theory/state argument metadata"
    -- `mkVeilTerm` elaborates ghost definitions as
    --   module params, user params, extracted Decidable params, th, st.
    -- `declarationSplitParams` intentionally separates extra params from
    -- actual params, so reassemble the order used by the Lean declaration.
    pure <| baseParams ++ userParams ++ extraParams ++ thstParams
  | .derivedDefinition .invariantLike _ =>
    pure <| baseParams ++ extraParams ++ #[thParam, stParam]
  | _ =>
    throwError "{nm} is not a recognized LocalRProp state predicate"
where
  isStateAssertionWithState : StateAssertionKind → Bool
  | .assumption => false
  | .invariant | .safety | .trustedInvariant | .termination | .stateConstraint => true

private def Module.statePredicateLayout [Monad m] [MonadQuotation m] [MonadError m]
    (mod : Module) (nm : Name) : m StatePredicateLayout := do
  let some dk := mod._declarations[nm]?
    | throwError "statePredicateLayout: {nm} not found in module declarations"
  let params ← mod.statePredicateExprParams nm dk
  let some thPos := params.findIdx? (·.kind == .theoryArg)
    | throwError "statePredicateLayout: missing theory argument for {nm}"
  let some stPos := params.findIdx? (·.kind == .stateArg)
    | throwError "statePredicateLayout: missing state argument for {nm}"
  pure { params, thPos, stPos }

private def Module.statePredicateLayout? [Monad m] [MonadQuotation m] [MonadError m]
    (mod : Module) (nm : Name) : m (Option StatePredicateLayout) := do
  try
    pure (some (← mod.statePredicateLayout nm))
  catch _ =>
    pure none

private def mkStatePredicateSelf (f : Sum Name Expr) (args : Array Expr) (layout : StatePredicateLayout) : MetaM Expr := do
  let th := args[layout.thPos]!
  let st := args[layout.stPos]!
  let thName ← mkFreshUserName `th
  let stName ← mkFreshUserName `st
  -- Well, is there any better way to write this?
  withLocalDeclsDND #[(thName, (← inferType th).consumeMData), (stName, (← inferType st).consumeMData)] fun ldecls => do
    let argsAbstracted := args.set! layout.thPos ldecls[0]! |>.set! layout.stPos ldecls[1]!
    let t ← match f with
      | Sum.inl fName => mkAppOptM fName <| argsAbstracted.map some
      | Sum.inr fExpr => pure <| mkAppN fExpr argsAbstracted
    mkLambdaFVarsWithAppSuffixEta ldecls t

private def getLocalRPropInst (f : Expr) (args : Array Expr) : SimpM (Option (Expr × Expr × Expr)) := do
  let some fName := f.constName? | return none
  let mod ← getCurrentModule
  let some nm := mod.localDeclarationName? fName | return none
  let some layout ← mod.statePredicateLayout? nm | return none
  unless args.size == layout.params.size do return none
  unless mod.parameters.size ≤ layout.params.size do return none
  let self ← mkStatePredicateSelf (.inr f) args layout
  let targetInstName ← resolveGlobalConstNoOverloadCore localRPropTCName
  -- TODO: this relies on the invariant that generated state-predicate
  -- declarations take `mod.parameters` as their exact binder prefix, and that
  -- `LocalRProp` is parameterized by precisely those module parameters. This
  -- should eventually come from a systematic Parameter-layout API instead of
  -- slicing raw application arguments by prefix length.
  let localRPropArgs := args.take mod.parameters.size
  let targetInstType ← mkAppOptM targetInstName ((localRPropArgs.push self).map Option.some)
  let e ← synthInstance targetInstType
  pure <| some (e, args[layout.thPos]!, args[layout.stPos]!)

private def mkLocalRPropCoreAppOnLCtxFields (mod : Module) (inst : Expr) : SimpM Expr := do
  let coreFn ← Meta.mkProjection inst `core
  -- relying on `mod` to find the field variables by their
  -- "canonical names" in the local context
  let lctx ← getLCtx
  let fieldVars ← (mod.immutableComponents ++ mod.mutableComponents).mapM fun sc => do
    let nm := sc.name
    let some ldecl := lctx.findFromUserName? nm
      | throwError "unable to find local field {nm}"
    pure ldecl.toExpr
  pure <| mkAppN coreFn fieldVars

-- This `Expr → SimpM Expr` is bespoke!
private def replaceLocalRPropCore (e : Expr) (rhs? : Option (Expr → SimpM Expr)) : SimpM Simp.Step := do
  let f := e.getAppFn'
  let args := e.getAppArgs'
  unless f.isConst && args.size ≥ 4 do return .continue
  try
    let some (inst, th, st) ← getLocalRPropInst f args | return .continue
    let coreEqApp ← do
      let coreEq ← Meta.mkProjection inst `core_eq
      pure <| mkAppN coreEq #[th, st]
    let rhs ← match rhs? with
      | some rhs => rhs inst
      | none =>
        let ty ← inferType coreEqApp
        let ty ← instantiateMVars ty
        let some ⟨_, _, rhs⟩ := ty.eq? | return .continue
        pure rhs
    return .done { expr := rhs, proof? := coreEqApp }
  catch _ =>
    return .continue

/-- Replace a state predicate by its `LocalRProp.core` when the surrounding
context has already exposed the current theory/state fields.

The old version of this was a `dsimproc` and pretended the proof was `rfl`.
The replacement has the same rewrite behavior, but carries the predicate's
`core_eq` proof explicitly. -/
simproc_decl replaceLocalRPropWithCoreAppOnLCtxFields (_) := fun e => do
  replaceLocalRPropCore e <| some fun inst => do
    let mod ← getCurrentModule
    mkLocalRPropCoreAppOnLCtxFields mod inst

simproc_decl replaceLocalRPropGeneralCase (_) := fun e => do
  replaceLocalRPropCore e none

/-! ## Locality Proof Generation -/

/-- Construct a `LocalRProp` term for the given state predicate `nm`,
including assertions and ghost relations. This is done at the level of
`Expr` to avoid uncertainty introduced by, for example, the use of
`veil_exact_state` tactics. Also, this should provide more useful
error message.

This function returns the instance. Its error message shall be handled
by the caller. -/
private def Module.proveLocalityForStatePredicateCore (mod : Module) (nm : Name) (expr? : Option Expr := none) : TermElabM Expr := do
  let nmFull ← resolveGlobalConstNoOverloadCore nm
  let expr ← match expr? with
    | some expr => pure expr
    | none => pure (← getConstInfoDefn nmFull).value
  let layout ← mod.statePredicateLayout nm
  -- NOTE: This proof generator peels apart the expression shape produced by
  -- `mkVeilTerm`/assembly. The hidden invariants are:
  -- * the outer lambdas are exactly the predicate binders described by
  --   `layout.params`;
  -- * after those binders, the body is an application `(fun th st => ...) th st`
  --   (or the assembled analogue) with exactly the theory/state value args;
  -- * instantiating that function with `th` and `st` exposes a
  --   `Theory.casesOn` application whose last argument is the theory-field
  --   body;
  -- * that body exposes a `State.casesOn` application whose last argument is
  --   the state-field body;
  -- * when field representation typeclasses are enabled, that state-field body
  --   begins with let-bound canonical fields obtained from concrete fields.
  -- These assumptions should eventually be replaced by a systematic
  -- Parameter/layout API, or by recording a more explicit elaboration artifact.
  let inst ← lambdaTelescope expr fun xs body => do
    unless xs.size == layout.params.size do
      throwError "unexpected binder arity for state predicate {nm}, got {xs.size}, expected {layout.params.size}"
    let f := body.getAppFn'
    let [th, st] := body.getAppArgs'.toList
      | throwError "unexpected shape of state predicate {nm}: unable to extract theory and state arguments"
    let f := f.instantiateLambdasOrApps #[th, st]
    -- `f` should be like `Theory.casesOn ...`
    let .app ff theoryCasesOnBody := f
      | throwError "unexpected shape of state predicate {f}: expected an application with Theory.casesOn as the function"
    lambdaTelescope theoryCasesOnBody fun theoryFields theoryBody => do
      -- `body` should be like `State.casesOn ...`
      let stateCasesApp := theoryBody
      let .app ff2 stateCasesOnBody := stateCasesApp
        | throwError "unexpected shape of state predicate {stateCasesApp}: expected an application with State.casesOn as the function"
      lambdaTelescope stateCasesOnBody fun stateFieldsConc body => do
        -- now, `body` should be the actual body of the predicate
        letBoundedTelescope body (.some <| if mod._useFieldRepTC then stateFieldsConc.size else 0) fun stateFields body => do
          let simplifyBody : Simp.Simplifier :=
            Simp.simp #[``Veil.Util.neutralizeDecidableInstGeneralWithExpectedType]
              |>.andThen (Simp.simp #[``replaceLocalTheoryPropWithCoreAppOnLCtxFields,
                ``replaceLocalRPropWithCoreAppOnLCtxFields])
          let bodyResult ← simplifyBody body
          -- Construct `core` independently from the simplified leaf body. In
          -- field-representation mode, the canonical state fields are let-bound
          -- in the peeled expression, so re-declare them as ordinary locals
          -- before abstracting the `core`.
          let core ← if mod._useFieldRepTC then
              let stateFieldDecls ← stateFields.mapM fun f => do
                let decl ← f.fvarId!.getDecl
                pure (decl.userName, decl.type)
              withLocalDeclsDND stateFieldDecls fun stateFieldsPlain => do
                mkLambdaFVars (theoryFields ++ stateFieldsPlain)
                  (bodyResult.expr.replaceFVars stateFields stateFieldsPlain)
            else
              mkLambdaFVars (theoryFields ++ stateFieldsConc) bodyResult.expr
          trace[veil.debug] "core for LocalRProp instance of {nm}: {core}"
          let targetInstName ← resolveGlobalConstNoOverloadCore localRPropTCName
          let some ctor := getStructureLikeCtor? (← getEnv) targetInstName
            | throwError "unexpected error: unable to find constructor for {localRPropTCName}"
          let ctorArgs ← do
            -- This mirrors `getLocalRPropInst`: `LocalRProp` is parameterized
            -- by the module-parameter prefix, followed by the state predicate
            -- with its theory/state arguments abstracted away.
            unless mod.parameters.size ≤ xs.size do
              throwError "unexpected module-parameter prefix while building LocalRProp instance for {nm}"
            let localRPropArgs := xs.take mod.parameters.size
            let self ← mkStatePredicateSelf (.inl nmFull) xs layout
            pure (localRPropArgs.push self)
          -- Construct the `core_eq` proof by "rolling back" what has been peeled off and simplified
          let coreEq ← do
            let stateLetExpr ← if mod._useFieldRepTC
              then mkLetFVars stateFields bodyResult.expr (usedLetOnly := false) (generalizeNondepLet := false)
              else pure bodyResult.expr
            let stateLetProof ← if mod._useFieldRepTC
              then mkLetFVars stateFields (← bodyResult.getProof) (usedLetOnly := false) (generalizeNondepLet := false)
              else bodyResult.getProof
            -- CHECK `Result.addLambdas` uses the default `mkLambdaFVars` settings,
            -- which generalize these nondependent lets and no longer matches
            -- the `core_eq` RHS generated by `declareLocalRPropTC`.
            let stateAltExpr ← mkLambdaFVars stateFieldsConc stateLetExpr (generalizeNondepLet := false)
            let stateAltProof ← stateFieldsConc.foldrM (init := stateLetProof) fun x h => do
              mkFunExt (← mkLambdaFVars #[x] h (generalizeNondepLet := false))
            let stateAppNew := mkApp ff2 stateAltExpr
            let stateAppProof ← mkCongrArg ff2 stateAltProof
            let stateAppResult : Meta.Simp.Result := { expr := stateAppNew, proof? := some stateAppProof }
            let theoryAltResult ← stateAppResult.addLambdas theoryFields
            let fullProof ← mkCongrArg ff (← theoryAltResult.getProof)
            -- NOTE: Here, implicitly requiring `th` and `st` to be fvars;
            -- which should be the case in general
            mkLambdaFVars #[th, st] fullProof
          let inst ← Meta.mkAppOptM ctor.name (ctorArgs |>.push core |>.push coreEq |>.map Option.some)
          mkLambdaFVars xs inst (usedOnly := true)
  check inst
  let inst ← instantiateMVars inst
  trace[veil.debug] "LocalRProp instance for {nm}: {inst}"
  return inst

private def Module.defineLocalAbstractEqForStatePredicate (mod : Module) (nm : Name) : TermElabM Unit := do
  let nmFull ← resolveGlobalConstNoOverloadCore nm
  let layout ← mod.statePredicateLayout nm
  let info ← getConstInfoDefn nmFull
  -- Build, for a state predicate `p`, the theorem
  --
  --   p ... th st = p ... (readFrom th) (toAbstractState (getFrom st)).
  --
  -- The proof does not unfold `p` directly. Instead, it uses the already
  -- generated `LocalRProp.core_eq` on the generic side and on the
  -- abstract-state side, then checks that the two `core` applications match.
  lambdaTelescope info.value fun xs _ => do
    unless xs.size == layout.params.size do
      throwError "defineLocalAbstractEqForStatePredicate: unexpected binder arity for {nm}, got {xs.size}, expected {layout.params.size}"
    unless mod.parameters.size ≤ layout.params.size do
      throwError "defineLocalAbstractEqForStatePredicate: malformed layout for {nm}"
    let th := xs[layout.thPos]!
    let st := xs[layout.stPos]!
    -- The left-hand side is evaluated in the original reader/state.  The
    -- right-hand side lives in the concrete module theory/state obtained from
    -- `readFrom`/`getFrom`; if field representations are enabled, the concrete
    -- state is immediately re-packed as the abstract `State FieldAbstractType`.
    let readFromArg ← mkAppM ``readFrom #[th]
    let getFromArg ← mkAppM ``getFrom #[st]
    let theoryType ← inferType readFromArg >>= instantiateMVars
    let stateType ← inferType getFromArg >>= instantiateMVars
    let (stateTypeTarget, stateSortTarget?, targetState) ←
      if mod._useFieldRepTC then
        let (abstractStateSortTerm, abstractStateSortExpr, abstractStateTypeExpr) ← mod.getAbstractStateRelated stateType
        let funExpr ← mod.toAbstractStateFun abstractStateSortTerm stateType abstractStateTypeExpr
        let targetState ← Core.betaReduce <| mkApp funExpr getFromArg
        pure (abstractStateTypeExpr, some abstractStateSortExpr, targetState)
      else
        pure (stateType, none, getFromArg)
    -- Translate arguments from the generic declaration into the target
    -- abstract-state declaration.  Explicit theory/state binders are replaced
    -- by the supplied `thArg`/`stArg`; module typeclass arguments and
    -- `Decidable` parameters may be omitted so elaboration can synthesize the
    -- right instances under `classical`.
    let specializeArg (thArg stArg : Expr) (p : Parameter) (v : Expr) : TermElabM (Option Expr) := do
      match p.kind with
      | .theoryArg => pure (some thArg)
      | .stateArg => pure (some stArg)
      | _ =>
        match stateSortTarget? with
        | some stateSort => specializeArgForStateAbstract p v theoryType stateTypeTarget stateSort
        | none => specializeArgForStateχ p v theoryType stateTypeTarget
    let specializeArgs (params : Array Parameter) (args : Array Expr) (thArg stArg : Expr)
        : TermElabM (Array (Option Expr)) := do
      unless params.size == args.size do
        throwError "defineLocalAbstractEqForStatePredicate: parameter/argument length mismatch for {nm}"
      params.zipWithM (bs := args) fun p v =>
        specializeArg thArg stArg p v
    -- Construct the theorem statement directly from full applications of the
    -- predicate.  Separately construct the `SProp` arguments needed to
    -- synthesize the generic and abstract-state `LocalRProp` instances.
    let lhs ← mkAppOptM nmFull (xs.map some)
    let targetFullArgs ← specializeArgs layout.params xs readFromArg targetState
    let rhs ← Tactic.classical <| mkAppOptM nmFull targetFullArgs
    let postGeneric ← mkStatePredicateSelf (.inl nmFull) xs layout
    let postTarget ← do
      let thName ← mkFreshUserName `th
      let stName ← mkFreshUserName `st
      -- Rebuild the target predicate under fresh target-world theory/state
      -- variables so the result has type `SProp targetTheory targetState`.
      withLocalDeclsDND #[(thName, theoryType.consumeMData), (stName, stateTypeTarget.consumeMData)] fun ldecls => do
        let targetSelfArgs ← specializeArgs layout.params xs ldecls[0]! ldecls[1]!
        let targetSelfApp ← Tactic.classical <| mkAppOptM nmFull targetSelfArgs
        mkLambdaFVarsWithAppSuffixEta ldecls targetSelfApp
    -- Synthesize the two locality instances:
    --   genericInst : LocalRProp postGeneric
    --   targetInst  : LocalRProp postTarget
    --
    -- `LocalRProp` itself is parameterized only by the module-parameter
    -- prefix, so this mirrors the prefix invariant used by `getLocalRPropInst`.
    let localRPropName ← resolveGlobalConstNoOverloadCore localRPropTCName
    let localRPropArgs := xs.take mod.parameters.size
    let genericInstType ← mkAppOptM localRPropName ((localRPropArgs.push postGeneric).map some)
    let genericInst ← synthInstance genericInstType
    let targetLocalRPropArgs ← specializeArgs mod.parameters localRPropArgs readFromArg targetState
    let targetInstType ← Tactic.classical <| mkAppOptM localRPropName (targetLocalRPropArgs.push (some postTarget))
    let targetInst ← Tactic.classical <| synthInstance targetInstType
    -- The two `core_eq` fields give:
    --
    --   lhs = genericCore
    --   rhs = targetCore
    --
    -- If the predicate is truly local, the cores are definitionally equal
    -- after neutralizing `Decidable` instances.  Transitivity then yields the
    -- requested `lhs = rhs`.
    let genericCoreEq ← Meta.mkProjection genericInst `core_eq
    let targetCoreEq ← Meta.mkProjection targetInst `core_eq
    let genericProof := mkAppN genericCoreEq #[th, st]
    let targetProof := mkAppN targetCoreEq #[readFromArg, targetState]
    let genericProofType ← inferType genericProof >>= instantiateMVars
    let some (_, _, genericCore) := genericProofType.eq?
      | throwError "defineLocalAbstractEqForStatePredicate: expected equality proof for generic core, got{indentExpr genericProofType}"
    let targetProofType ← inferType targetProof >>= instantiateMVars
    let some (_, _, targetCore) := targetProofType.eq?
      | throwError "defineLocalAbstractEqForStatePredicate: expected equality proof for target core, got{indentExpr targetProofType}"
    let coreProof ←
      match ← isDefEqModuloDecidableInstances genericCore targetCore with
      | some none => mkEqRefl genericCore
      | some (some proof) => pure proof
      | none =>
        throwError m!"defineLocalAbstractEqForStatePredicate: core mismatch for {nm}\n  generic: {genericCore}\n  target: {targetCore}"
    let proof ← mkEqTrans genericProof coreProof
    let proof ← mkEqTrans proof (← mkEqSymm targetProof)
    let eqStatement ← mkEq lhs rhs
    let eqStatement ← instantiateMVars $ ← mkForallFVars xs eqStatement
    let proof ← instantiateMVars $ ← mkLambdaFVars xs proof
    let _ ← addVeilTheorem (toLocalAbstractEqName nm) eqStatement proof

def Module.tryDefineLocalAbstractEqForStatePredicate (mod : Module) (nm : Name) (stx : Syntax) : TermElabM Unit := do
  try
    mod.defineLocalAbstractEqForStatePredicate nm
  catch ex =>
    logWarningAt stx m!"unable to generate local abstract equality for state predicate {nm}: {ex.toMessageData}"

/-! ## Instance Registration -/

/-- Prove locality for the state predicate `nm`, and register
the corresponding `LocalRProp` instance in the module. Any error
will be caught and logged as a warning. -/
def Module.proveLocalityForStatePredicate (mod : Module) (nm : Name) (stx : Syntax) (expr? : Option Expr := none) : TermElabM Unit := do
  try
    let inst ← mod.proveLocalityForStatePredicateCore nm expr?
    let attrs ← do
      let tmp ← `(Parser.Term.attrInstance| scoped instance)
      elabAttrs (#[tmp])
    let _ ← addVeilDefinition (generateLocalRPropInstName nm) inst (attr := attrs)
  catch ex =>
    logWarningAt stx m!"unable to prove locality for state predicate {nm}: {ex.toMessageData}"
where
  generateLocalRPropInstName (nm : Name) : Name :=
    Name.mkSimple <| "instLocalRProp" ++ nm.capitalize.toString

/-! ## Simplified LocalRProp for Assembled Definitions -/

-- NOTE: There are two ways to use this pre-simplification.
-- One is to store the simplified result as an instance and rely on the
-- instance resolution to use it, the other is to directly save the simplified
-- result as a theorem and use it in the proof. Here, we use the latter.

/-- Simplify the `LocalRProp.core` for a definition. -/
def Module.simplifyLocalRPropCore (mod : Module) (nm : Name) : TermElabM Unit := do
  if !mod._useLocalRPropTC || (← isModelCheckCompileMode) then return
  let some dk := mod._declarations[nm]?
    | throwError "simplifyLocalRPropCore: {nm} not found in module declarations"
  let (nmParams, _) ← mod.declarationAllParams nm dk
  -- `nm` may take more parameters than `LocalRProp` (e.g. `Invariants`
  -- takes extra params beyond the module parameters)
  let nmBinders ← nmParams.mapM (·.binder)
  elabBinders nmBinders fun vs => do
    let localRPropArgs ← mod.parameters.mapM (·.arg)
    -- Step 1: construct and synthesize the LocalRProp instance
    let nmApp ← do
      let nmFull ← resolveGlobalConstNoOverloadCore nm
      mkAppOptM nmFull (vs.map some)
    let instType ← do
      -- NOTE: Ideally, we could also construct it only at the `Expr` level,
      -- but that requires filtering out the parameters that are not needed,
      -- which is a bit tricky.
      let tm ← `(@$localRPropTC $localRPropArgs*)
      let tc ← withoutErrToSorry <| elabTermAndSynthesize tm none
      pure <| mkApp tc nmApp
    let inst ← synthInstance instType
    let core ← mkProjection inst `core
    -- Step 2: simplify the `core` field
    -- NOTE: can do more `simp` here, can do less `dsimp` here
    let core' ← (Simp.dsimp #[`LocalRProp.core, `nextSimp]) core
    let core' ← do
      let unfoldghostRel? := veil.unfoldGhostRel.get (← getOptions)
      let simps := #[`invSimp, `smtSimp]
      let simps := if unfoldghostRel? then simps.push `ghostRelSimp else simps
      (Simp.simp simps) core'.expr
    -- Step 3: save simplified core as a definition
    let coreSimplifiedFqn ← do
      let e ← instantiateMVars $ ← mkLambdaFVars vs core'.expr
      -- let attr ← do
      --   let tmp ← `(Parser.Term.attrInstance| $(mkIdent `derivedInvSimp):ident)
      --   elabAttrs (#[tmp])
      addVeilDefinition (toCoreSimplifiedName nm) e --(attr := attr)
    -- Step 4: save the equality as a theorem
    -- NOTE: The RHS should not directly contain `core'.expr`, since
    -- after beta reduction, all its arguments will be substituted into
    -- the body, and this makes generalization difficult. That's why
    -- we save the simplified `core` as a definition and use it in the RHS.
    let coreEq ← mkProjection inst `core_eq
    let ty ← (inferType coreEq >>= instantiateMVars)
    -- Here, the inferred type might have `nm` unfolded, so explicitly
    -- construct this equality
    forallTelescope ty fun xs eq => do
      let some (_, _, rhs) := eq.eq? | throwError "unexpected shape of core_eq type for {nm}"
      let lhs := mkAppN nmApp xs
      let (rhs', eqProof) ← do
        let core'' ← mkAppOptM coreSimplifiedFqn (vs.map some)
        -- The following works in a similar way as `rewrite` does
        let rhsAbs ← Meta.kabstract rhs core
        let rhsFun := Expr.lam `_a (← inferType core) rhsAbs BinderInfo.default
        let rhs' := Expr.instantiate1 rhsAbs core''
        let congrProof ← mkCongrArg rhsFun (← core'.getProof)
        let eqProof ← mkEqTrans (mkAppN coreEq xs) congrProof
        pure (rhs', eqProof)
      -- Only do `iota` like simp in this step
      let rhs' ← (Simp.dsimp #[]) rhs'
      let fvars := vs ++ xs
      withImplicitBinderInfos vs do
        let eqStatement ← do
          let eq' ← mkEq lhs rhs'.expr
          instantiateMVars $ ← mkForallFVars fvars eq'
        let eqProof ← instantiateMVars $ ← mkLambdaFVars fvars eqProof
        let _ ← addVeilTheorem (toCoreSimplifiedEqName nm) eqStatement eqProof

/-! ## Assembled Definition Simplification -/

/-- Simplify an assembled definition (e.g. `Invariants`) by applying
`replaceLocalRPropGeneralCase` to rewrite each sub-predicate into its
`LocalRProp.core` form, then register the result as a `core_eq` theorem. -/
def Module.simplifyAssembledWithLocalRProp (mod : Module) (nm : Name) : TermElabM Unit := do
  if !mod._useLocalRPropTC || (← isModelCheckCompileMode) then return
  try
    let nmFull ← resolveGlobalConstNoOverloadCore nm
    let info ← getConstInfoDefn nmFull
    lambdaTelescope info.value fun xs body => do
      let simp : Simp.Simplifier := Simp.unfold #[nmFull]
        |>.andThen (Simp.simp #[``replaceLocalRPropGeneralCase])
      let simpResult ← simp body
      let lhs ← mkAppOptM nmFull (xs.map Option.some)
      let eqStatement ← mkEq lhs simpResult.expr
      let eqStatement ← instantiateMVars $ ← mkForallFVars xs eqStatement
      let eqProof ← instantiateMVars $ ← mkLambdaFVars xs (← simpResult.getProof)
      let _ ← addVeilTheorem (nm ++ `core_eq) eqStatement eqProof
  catch ex =>
    logWarning m!"unable to simplify {nm} with LocalRProp: {ex.toMessageData}"

end Veil
