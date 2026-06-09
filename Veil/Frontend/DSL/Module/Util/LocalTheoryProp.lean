import Veil.Frontend.DSL.Module.Util.LocalRProp

open Lean Parser Elab Command Term Meta Tactic

namespace Veil

/-! ## LocalTheoryProp Typeclass Declaration -/

/-- The module parameters relevant to predicates over the background theory.
This mirrors the `theoryParameters` helper used by `declarationBaseParams` for
assumptions and theory-only derived definitions. -/
private def Module.localTheoryPropParams (mod : Module) : Array Parameter :=
  mod.parameters.filterMap fun p => match p.kind with
  | .environmentState | .fieldConcreteType => none
  | .moduleTypeclass kd =>
    match kd with
    | .environmentState | .fieldRepresentation | .lawfulFieldRepresentation => none
    | _ => some p
  | _ => some p

/-- Declare the `LocalTheoryProp` typeclass for the module.
Its general form is:
```lean
class LocalTheoryProp /- theory parameters -/ (post : ρ → Prop)
where
  core :
    /- types of fields of `Theory`, connected with `→` -/ → Prop
  core_eq : ∀ (th : ρ),
    post th = core /- fields of `Theory` -/
```
-/
def Module.declareLocalTheoryPropTC (mod : Module) : MetaM (List Command) := do
  let params := mod.localTheoryPropParams
  let paramBinders ← params.mapM (·.binder)
  let post ← Lean.mkIdent <$> mkFreshUserName `post
  let core := mkIdent `core
  let core_eq := mkIdent `core_eq
  let coreType ← do
    let theoryFields ← mod.immutableComponents.mapM (·.getSimpleBinder >>= getSimpleBinderType)
    mkArrowStx theoryFields.toList (← `(term| Prop))
  let th ← Lean.mkIdent <$> mkFreshUserName `th
  let coreEqType ← do
    let body ← mod.withTheoryAndStateTermTemplate [(.theory, th, true)] (some $ ← `(term| Prop)) fun theoryFieldNames _ =>
      pure <| Syntax.mkApp core theoryFieldNames
    `(term| ∀ ($th : $environmentTheory), $post $th = $body)
  let cmd1 ← do
    let binders := paramBinders.push (← `(bracketedBinder| ($post : $environmentTheory → Prop)))
    `(command| class $localTheoryPropTC $[$binders]* where
      $core:ident : $coreType
      $core_eq:ident : $coreEqType)
  let cmd2 ← `(command| attribute [$(mkIdent `wpSimp):ident] $(mkIdent <| localTheoryPropTCName ++ `core):ident)
  let cmd3 ← do
    let implBinders ← paramBinders.mapM mkImplicitBinder
    let p ← Lean.mkIdent <$> mkFreshUserName `p
    let q ← Lean.mkIdent <$> mkFreshUserName `q
    let inst1 ← Lean.mkIdent <$> mkFreshUserName `inst1
    let inst2 ← Lean.mkIdent <$> mkFreshUserName `inst2
    let args ← params.mapM (·.arg)
    let fieldNames : Array Ident := mod.immutableComponents.map fun sc => mkIdent sc.name
    let fieldBinders : Array (TSyntax ``Lean.Parser.Term.funBinder) ← fieldNames.mapM fun f =>
      `(Lean.Parser.Term.funBinder| $f)
    let fieldArgs : Array Term ← fieldNames.mapM fun f => `(term| $f)
    let coreFn ← mkFunSyntax fieldBinders (← `(term| $inst1.$(mkIdent `core) $fieldArgs* ∧ $inst2.$(mkIdent `core) $fieldArgs*))
    `(command| scoped instance $[$implBinders]* ($p $q : $environmentTheory → Prop)
        [$inst1 : @$localTheoryPropTC $args* $p] [$inst2 : @$localTheoryPropTC $args* $q] :
        @$localTheoryPropTC $args* (fun $th => $p $th ∧ $q $th) where
      $core:ident := $coreFn
      $core_eq:ident := fun $th => $(mkIdent ``congrArg₂) $(mkIdent ``And) ($inst1.$(mkIdent `core_eq) $th) ($inst2.$(mkIdent `core_eq) $th))
  pure [cmd1, cmd2, cmd3]

/-! ## Simplification Infrastructure -/

private structure TheoryPredicateLayout where
  params : Array Parameter
  thPos : Nat

private def Module.localDeclarationName? (mod : Module) (fullName : Name) : Option Name :=
  if mod._declarations.contains fullName then
    some fullName
  else
    let localName := fullName.updatePrefix Name.anonymous
    if mod._declarations.contains localName then some localName else none

private def Module.theoryPredicateExprParams [Monad m] [MonadQuotation m] [MonadError m]
    (mod : Module) (nm : Name) (dk : DeclarationKind) : m (Array Parameter) := do
  -- TODO Replace this reconstruction with a systematic Parameter-layout API.
  -- As with `LocalRProp`, locality needs the exact binder order of generated
  -- Lean declarations, but the metadata for assertions, ghost definitions, and
  -- assembled definitions does not currently store that order uniformly.
  let (baseParams, extraParams, actualParams) ← mod.declarationSplitParams nm dk
  let thParam := { kind := .theoryArg, name := `th, «type» := ← `(term| $environmentTheory), userSyntax := .missing }
  match dk with
  | .stateAssertion .assumption =>
    pure <| baseParams ++ extraParams ++ #[thParam]
  | .derivedDefinition (.theoryGhost true) _ =>
    let (userParams, thParams) := actualParams.partition fun p => p.kind != .theoryArg
    unless thParams.any (·.kind == .theoryArg) do
      throwError "theory ghost relation {nm} does not carry theory argument metadata"
    -- `mkVeilTerm` elaborates theory ghost definitions as
    --   theory params, user params, extracted Decidable params, th.
    -- Reassemble that order explicitly because `declarationSplitParams`
    -- separates extracted instances from user-written parameters.
    pure <| baseParams ++ userParams ++ extraParams ++ thParams
  | .derivedDefinition .assumptionLike _ =>
    pure <| baseParams ++ extraParams ++ #[thParam]
  | _ =>
    throwError "{nm} is not a recognized LocalTheoryProp predicate"

private def Module.theoryPredicateLayout [Monad m] [MonadQuotation m] [MonadError m]
    (mod : Module) (nm : Name) : m TheoryPredicateLayout := do
  let some dk := mod._declarations[nm]?
    | throwError "theoryPredicateLayout: {nm} not found in module declarations"
  let params ← mod.theoryPredicateExprParams nm dk
  let some thPos := params.findIdx? (·.kind == .theoryArg)
    | throwError "theoryPredicateLayout: missing theory argument for {nm}"
  pure { params, thPos }

private def Module.theoryPredicateLayout? [Monad m] [MonadQuotation m] [MonadError m]
    (mod : Module) (nm : Name) : m (Option TheoryPredicateLayout) := do
  try
    pure (some (← mod.theoryPredicateLayout nm))
  catch _ =>
    pure none

private def mkTheoryPredicateSelf (f : Sum Name Expr) (args : Array Expr)
    (layout : TheoryPredicateLayout) : MetaM Expr := do
  let th := args[layout.thPos]!
  let thName ← mkFreshUserName `th
  withLocalDeclsDND #[(thName, (← inferType th).consumeMData)] fun ldecls => do
    let argsAbstracted := args.set! layout.thPos ldecls[0]!
    let t ← match f with
      | Sum.inl fName => mkAppOptM fName <| argsAbstracted.map some
      | Sum.inr fExpr => pure <| mkAppN fExpr argsAbstracted
    mkLambdaFVarsWithAppSuffixEta ldecls t

private def getLocalTheoryPropInst (f : Expr) (args : Array Expr) : SimpM (Option (Expr × Expr)) := do
  let some fName := f.constName? | return none
  let mod ← getCurrentModule
  let some nm := mod.localDeclarationName? fName | return none
  let some layout ← mod.theoryPredicateLayout? nm | return none
  unless args.size == layout.params.size do return none
  let classParams := mod.localTheoryPropParams
  unless classParams.size ≤ layout.params.size do return none
  let self ← mkTheoryPredicateSelf (.inr f) args layout
  let targetInstName ← resolveGlobalConstNoOverloadCore localTheoryPropTCName
  -- TODO: Like `getLocalRPropInst`, this relies on the generated predicate
  -- declaration taking the theory-local module parameters as its exact binder
  -- prefix. This should eventually come from a systematic Parameter-layout API.
  let targetInstType ← mkAppOptM targetInstName (((args.take classParams.size).push self).map some)
  let e ← synthInstance targetInstType
  pure <| some (e, args[layout.thPos]!)

private def mkLocalTheoryPropCoreAppOnLCtxFields (mod : Module) (inst : Expr) : SimpM Expr := do
  let coreFn ← Meta.mkProjection inst `core
  let lctx ← getLCtx
  let fieldVars ← mod.immutableComponents.mapM fun sc => do
    let some ldecl := lctx.findFromUserName? sc.name
      | throwError "unable to find local theory field {sc.name}"
    pure ldecl.toExpr
  pure <| mkAppN coreFn fieldVars

private def replaceLocalTheoryPropCore (e : Expr) (rhs? : Option (Expr → SimpM Expr)) :
    SimpM Simp.Step := do
  let f := e.getAppFn'
  let args := e.getAppArgs'
  unless f.isConst && args.size ≥ 1 do return .continue
  try
    let some (inst, th) ← getLocalTheoryPropInst f args | return .continue
    let coreEqApp ← do
      let coreEq ← Meta.mkProjection inst `core_eq
      pure <| mkApp coreEq th
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

/-- Replace a theory predicate by its `LocalTheoryProp.core` when the current
theory fields have already been exposed in the local context. -/
simproc_decl replaceLocalTheoryPropWithCoreAppOnLCtxFields (_) := fun e => do
  replaceLocalTheoryPropCore e <| some fun inst => do
    let mod ← getCurrentModule
    mkLocalTheoryPropCoreAppOnLCtxFields mod inst

simproc_decl replaceLocalTheoryPropGeneralCase (_) := fun e => do
  replaceLocalTheoryPropCore e none

/-! ## Locality Proof Generation -/

private def Module.proveLocalityForTheoryPredicateCore (mod : Module) (nm : Name)
    (expr? : Option Expr := none) : TermElabM Expr := do
  let nmFull ← resolveGlobalConstNoOverloadCore nm
  let expr ← match expr? with
    | some expr => pure expr
    | none => pure (← getConstInfoDefn nmFull).value
  let layout ← mod.theoryPredicateLayout nm
  -- This is the theory-only analogue of `proveLocalityForStatePredicateCore`.
  -- The expected shape comes from `withTheory`: after the declaration binders,
  -- the body is `(fun th => Theory.casesOn ... body) th`. We peel that one
  -- layer, simplify nested theory-local predicates at the leaf, then roll the
  -- proof back through the `Theory.casesOn` application.
  let inst ← lambdaTelescope expr fun xs body => do
    unless xs.size == layout.params.size do
      throwError "unexpected binder arity for theory predicate {nm}, got {xs.size}, expected {layout.params.size}"
    let f := body.getAppFn'
    let [th] := body.getAppArgs'.toList
      | throwError "unexpected shape of theory predicate {nm}: unable to extract theory argument"
    let f := f.instantiateLambdasOrApps #[th]
    let .app ff theoryCasesOnBody := f
      | throwError "unexpected shape of theory predicate {f}: expected an application with Theory.casesOn as the function"
    lambdaTelescope theoryCasesOnBody fun theoryFields body => do
      let simplifyBody : Simp.Simplifier :=
        Simp.simp #[``replaceLocalTheoryPropWithCoreAppOnLCtxFields]
          |>.andThen (Simp.simp #[``Veil.Util.neutralizeDecidableInstGeneralWithExpectedType])
      let bodyResult ← simplifyBody body
      let core ← mkLambdaFVars theoryFields bodyResult.expr
      trace[veil.debug] "core for LocalTheoryProp instance of {nm}: {core}"
      let targetInstName ← resolveGlobalConstNoOverloadCore localTheoryPropTCName
      let some ctor := getStructureLikeCtor? (← getEnv) targetInstName
        | throwError "unexpected error: unable to find constructor for {localTheoryPropTCName}"
      let ctorArgs ← do
        let classParams := mod.localTheoryPropParams
        unless classParams.size ≤ xs.size do
          throwError "unexpected theory-parameter prefix while building LocalTheoryProp instance for {nm}"
        let self ← mkTheoryPredicateSelf (.inl nmFull) xs layout
        pure ((xs.take classParams.size).push self)
      let coreEq ← do
        let theoryAltResult ← bodyResult.addLambdas theoryFields
        let fullProof ← mkCongrArg ff (← theoryAltResult.getProof)
        mkLambdaFVars #[th] fullProof
      let inst ← Meta.mkAppOptM ctor.name (ctorArgs |>.push core |>.push coreEq |>.map some)
      mkLambdaFVars xs inst (usedOnly := true)
  check inst
  let inst ← instantiateMVars inst
  trace[veil.debug] "LocalTheoryProp instance for {nm}: {inst}"
  pure inst

private def specializeTheoryArg (p : Parameter) (v theoryType : Expr) : TermElabM (Option Expr) := do
  match p.kind with
  | .backgroundTheory => pure (some theoryType)
  | .moduleTypeclass .backgroundTheory => pure none
  | .theoryArg => pure (some v)
  | .definitionParameter _ .typeclass =>
    let ty ← inferType v
    if ty.getForallBody.getAppFn'.isConstOf ``Decidable then pure none else pure (some v)
  | _ => pure (some v)

private def specializeTheoryArgs (params : Array Parameter) (args : Array Expr)
    (theoryType : Expr) : TermElabM (Array (Option Expr)) := do
  unless params.size == args.size do
    throwError "specializeTheoryArgs: parameter/argument length mismatch"
  params.zipWithM (bs := args) fun p v =>
    specializeTheoryArg p v theoryType

private def Module.defineLocalAbstractEqForTheoryPredicate (mod : Module) (nm : Name) :
    TermElabM Unit := do
  let nmFull ← resolveGlobalConstNoOverloadCore nm
  let layout ← mod.theoryPredicateLayout nm
  let info ← getConstInfoDefn nmFull
  -- Build, for a theory predicate `p`, the theorem
  --
  --   p ... th = p ... (readFrom th).
  --
  -- The proof follows the same pattern as the state-predicate version: use
  -- `LocalTheoryProp.core_eq` on both sides, then compare the two cores.
  lambdaTelescope info.value fun xs _ => do
    unless xs.size == layout.params.size do
      throwError "defineLocalAbstractEqForTheoryPredicate: unexpected binder arity for {nm}, got {xs.size}, expected {layout.params.size}"
    let th := xs[layout.thPos]!
    let readFromArg ← mkAppM ``readFrom #[th]
    let theoryType ← inferType readFromArg >>= instantiateMVars
    let lhs ← mkAppOptM nmFull (xs.map some)
    let targetFullArgs ← specializeTheoryArgs layout.params (xs.set! layout.thPos readFromArg) theoryType
    let rhs ← Tactic.classical <| mkAppOptM nmFull targetFullArgs
    let postGeneric ← mkTheoryPredicateSelf (.inl nmFull) xs layout
    let postTarget ← do
      let thName ← mkFreshUserName `th
      withLocalDeclsDND #[(thName, theoryType.consumeMData)] fun ldecls => do
        let targetSelfArgs ← specializeTheoryArgs layout.params (xs.set! layout.thPos ldecls[0]!) theoryType
        let targetSelfApp ← Tactic.classical <| mkAppOptM nmFull targetSelfArgs
        mkLambdaFVarsWithAppSuffixEta ldecls targetSelfApp
    let localTheoryPropName ← resolveGlobalConstNoOverloadCore localTheoryPropTCName
    let classParams := mod.localTheoryPropParams
    let localTheoryPropArgs := xs.take classParams.size
    let genericInstType ← mkAppOptM localTheoryPropName ((localTheoryPropArgs.push postGeneric).map some)
    let genericInst ← synthInstance genericInstType
    let targetLocalTheoryPropArgs ← specializeTheoryArgs classParams localTheoryPropArgs theoryType
    let targetInstType ← Tactic.classical <| mkAppOptM localTheoryPropName (targetLocalTheoryPropArgs.push (some postTarget))
    let targetInst ← Tactic.classical <| synthInstance targetInstType
    let genericCoreEq ← Meta.mkProjection genericInst `core_eq
    let targetCoreEq ← Meta.mkProjection targetInst `core_eq
    let genericProof := mkApp genericCoreEq th
    let targetProof := mkApp targetCoreEq readFromArg
    let genericProofType ← inferType genericProof >>= instantiateMVars
    let some (_, _, genericCore) := genericProofType.eq?
      | throwError "defineLocalAbstractEqForTheoryPredicate: expected equality proof for generic core, got{indentExpr genericProofType}"
    let targetProofType ← inferType targetProof >>= instantiateMVars
    let some (_, _, targetCore) := targetProofType.eq?
      | throwError "defineLocalAbstractEqForTheoryPredicate: expected equality proof for target core, got{indentExpr targetProofType}"
    let coreProof ←
      match ← isDefEqModuloDecidableInstances genericCore targetCore with
      | some none => mkEqRefl genericCore
      | some (some proof) => pure proof
      | none =>
        throwError m!"defineLocalAbstractEqForTheoryPredicate: core mismatch for {nm}\n  generic: {genericCore}\n  target: {targetCore}"
    let proof ← mkEqTrans genericProof coreProof
    let proof ← mkEqTrans proof (← mkEqSymm targetProof)
    let eqStatement ← mkEq lhs rhs
    let eqStatement ← instantiateMVars $ ← mkForallFVars xs eqStatement
    let proof ← instantiateMVars $ ← mkLambdaFVars xs proof
    let _ ← addVeilTheorem (toLocalAbstractEqName nm) eqStatement proof

def Module.tryDefineLocalAbstractEqForTheoryPredicate (mod : Module) (nm : Name) (stx : Syntax) :
    TermElabM Unit := do
  try
    mod.defineLocalAbstractEqForTheoryPredicate nm
  catch ex =>
    logWarningAt stx m!"unable to generate local abstract equality for theory predicate {nm}: {ex.toMessageData}"

def Module.proveLocalityForTheoryPredicate (mod : Module) (nm : Name) (stx : Syntax)
    (expr? : Option Expr := none) : TermElabM Unit := do
  try
    let inst ← mod.proveLocalityForTheoryPredicateCore nm expr?
    let attrs ← do
      let tmp ← `(Parser.Term.attrInstance| scoped instance)
      elabAttrs (#[tmp])
    let _ ← addVeilDefinition (generateLocalTheoryPropInstName nm) inst (attr := attrs)
  catch ex =>
    logWarningAt stx m!"unable to prove theory locality for predicate {nm}: {ex.toMessageData}"
where
  generateLocalTheoryPropInstName (nm : Name) : Name :=
    Name.mkSimple <| "instLocalTheoryProp" ++ nm.capitalize.toString

/-! ## Assembled Definition Simplification -/

def Module.simplifyAssembledWithLocalTheoryProp (mod : Module) (nm : Name) : TermElabM Unit := do
  if !mod._useLocalRPropTC || (← isModelCheckCompileMode) then return
  try
    let nmFull ← resolveGlobalConstNoOverloadCore nm
    let info ← getConstInfoDefn nmFull
    lambdaTelescope info.value fun xs body => do
      let simp : Simp.Simplifier := Simp.unfold #[nmFull]
        |>.andThen (Simp.simp #[``replaceLocalTheoryPropGeneralCase])
      let simpResult ← simp body
      let lhs ← mkAppOptM nmFull (xs.map some)
      let eqStatement ← mkEq lhs simpResult.expr
      let eqStatement ← instantiateMVars $ ← mkForallFVars xs eqStatement
      let eqProof ← instantiateMVars $ ← mkLambdaFVars xs (← simpResult.getProof)
      let _ ← addVeilTheorem (nm ++ `core_eq) eqStatement eqProof
  catch ex =>
    logWarning m!"unable to simplify {nm} with LocalTheoryProp: {ex.toMessageData}"

end Veil
