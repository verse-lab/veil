import Veil.Frontend.DSL.Module.Util.Assertions

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
  -- NOTE: This part is not useful since this instance contains too many arguments
  -- that cannot be filled automatically, which prevents it from being used
  /-
  -- Trivial instance for `⊤` (needed for `doesNotThrow` VCs which use `⊤` as postcondition)
  let cmd3 ← do
    let args ← params.mapM (·.arg)
    let args := args.push <| ← `(fun _ _ => $(mkIdent ``True)) -- ← `(⊤)
    let binders ← paramBinders.mapM mkImplicitBinder
    let wildcards : Array (TSyntax ``Lean.Parser.Term.funBinder) ← do
      let wc ← `(Lean.Parser.Term.funBinder| _ )
      pure <| Array.replicate (mod.immutableComponents.size + mod.mutableComponents.size) wc
    let coreStx ← mkFunSyntax wildcards (← `(term| $(mkIdent ``True)))
    `(command| scoped instance $localRPropTCInstForTop:ident $[$binders]* : @$localRPropTC $args* where
      core := $coreStx
      core_eq := fun _ _ => rfl)
  -/
  return [cmd1, cmd2]

/-! ## Simplification Infrastructure -/

private def getLocalRPropInst (f : Expr) (args : Array Expr) : SimpM (Option (Expr × Expr × Expr)) := do
  let (targetInstType, th, st) ← do
    let targetInstName ← resolveGlobalConstNoOverloadCore localRPropTCName
    let targetInstInfo ← getConstInfo targetInstName
    let mut argsMore := args.take (targetInstInfo.type.getForallArity - 1)    -- the 1 accounts for the `post` parameter
    let (self, th, st) ← do
      let ρ := args[0]! ; let σ := args[1]!
      -- remove the arguments representing theory and state from `args`,
      -- by a heuristic
      let args' := args.reverse
      let some thPos ← args'.findIdxM? fun a => do isDefEq (← inferType a) ρ
        | return none
      let thPos := args.size - 1 - thPos
      let some stPos ← args'.findIdxM? fun a => do isDefEq (← inferType a) σ
        | return none
      let stPos := args.size - 1 - stPos
      -- a special check: see the comment below
      let self ← if thPos == args.size - 2 && stPos == args.size - 1 then
          pure <| mkAppN f (args.pop.pop)
        else
          let thName ← mkFreshUserName `th ; let stName ← mkFreshUserName `st
          withLocalDeclsDND #[(thName, ρ.consumeMData), (stName, σ.consumeMData)] fun ldecls => do
            let argsAbstracted := args.set! thPos ldecls[0]! |>.set! stPos ldecls[1]!
            mkLambdaFVars ldecls <| mkAppN f argsAbstracted
      pure (self, args[thPos]!, args[stPos]!)
    argsMore := argsMore.push self
    let targetInstType ← mkAppOptM targetInstName (argsMore.map Option.some)
    pure (targetInstType, th, st)
  let e ← synthInstance targetInstType
  pure <| some (e, th, st)

/-- This `dsimproc` attempts to replace assertions that have associated
`LocalRProp` instances with their `core` definitions. -/
dsimproc_decl replaceLocalRPropReflCase (_) := fun e => do
  let f := e.getAppFn'
  let args := e.getAppArgs'
  unless f.isConst && args.size ≥ 4 do return .continue
  -- search for the `LocalRProp` instance of `nm`
  -- NOTE: The following code relies on some hacks
  try
    let some (inst, _, _) ← getLocalRPropInst f args | return .continue
    let coreFn ← Meta.mkProjection inst `core
    let coreApp ← do
      -- relying on `mod` to find the field variables by their
      -- "canonical names" in the local context
      let lctx ← getLCtx
      let mod ← getCurrentModule
      let scs := mod.immutableComponents ++ mod.mutableComponents
      let fieldVars ← scs.mapM fun sc => do
        let nm := sc.name
        let some ldecl := lctx.findFromUserName? nm
          | throwError "unable to find theory field {nm} in the local context"
        pure ldecl.toExpr
      pure <| mkAppN coreFn fieldVars
    return .done coreApp
  catch _ =>
    return .continue

simproc_decl replaceLocalRPropGeneralCase (_) := fun e => do
  let f := e.getAppFn'
  let args := e.getAppArgs'
  unless f.isConst && args.size ≥ 4 do return .continue
  try
    let some (inst, th, st) ← getLocalRPropInst f args | return .continue
    let coreEq ← Meta.mkProjection inst `core_eq
    let coreEqApp := mkAppN coreEq #[th, st]
    let ty ← inferType coreEqApp
    let ty ← instantiateMVars ty
    let some ⟨_, _, rhs⟩ := ty.eq? | return .continue
    return .done { expr := rhs, proof? := coreEqApp }
  catch _ =>
    return .continue

/-! ## Locality Proof Generation -/

/-- Construct a `LocalRProp` term for the given state predicate `nm`,
including assertions and ghost relations. This is done at the level of
`Expr` to avoid uncertainty introduced by, for example, the use of
`veil_exact_state` tactics. Also, this should provide more useful
error message.

This function returns the instance. Its error message shall be handled
by the caller. -/
private def Module.proveLocalityForStatePredicateCore (mod : Module) (nm : Name) : MetaM Expr := do
  let nmFull ← resolveGlobalConstNoOverloadCore nm
  let info ← getConstInfoDefn nmFull
  -- exploit the shape of `info.value`
  let inst ← lambdaTelescope info.value fun xs body => do
    let f := body.getAppFn'
    let [th, st] := body.getAppArgs'.toList
      | throwError "unexpected shape of state predicate {nm}: unable to extract theory and state arguments"
    let ρ ← inferType th
    let σ ← inferType st
    let f := f.instantiateLambdasOrApps #[th, st]
    -- `f` should be like `Theory.casesOn ...`
    let theoryCasesOnBody := f.getAppArgs'.back!
    lambdaTelescope theoryCasesOnBody fun theoryFields body => do
      -- `body` should be like `State.casesOn ...`
      let stateCasesOnBody := body.getAppArgs'.back!
      lambdaTelescope stateCasesOnBody fun stateFieldsConc body => do
        -- now, `body` should be the actual body of the predicate
        letBoundedTelescope body (.some <| if mod._useFieldRepTC then stateFieldsConc.size else 0) fun stateFields body => do
          let stateFieldsInUse := if mod._useFieldRepTC then stateFields else stateFieldsConc
          -- construct and simplify the `core`
          let core ← do
            let tmp ← (Simp.dsimp #[``replaceLocalRPropReflCase]) body
            mkLambdaFVars (theoryFields ++ stateFieldsInUse) tmp.expr
          trace[veil.debug] "core for LocalRProp instance of {nm}: {core}"
          -- the `core_eq` should have `proof` inside
          let coreEq ← do
            let thName ← mkFreshUserName `th ; let stName ← mkFreshUserName `st
            withLocalDeclsDND #[(thName, ρ.consumeMData), (stName, σ.consumeMData)] fun ldecls => do
              let xs' := xs.replace th ldecls[0]! |>.replace st ldecls[1]!
              let self ← mkAppOptM nmFull (xs'.map Option.some)
              let eqrefl ← mkEqRefl self
              mkLambdaFVars ldecls eqrefl
          -- now, build the instance
          let targetInstName ← resolveGlobalConstNoOverloadCore localRPropTCName
          let some ctor := getStructureLikeCtor? (← getEnv) targetInstName
            | throwError "unexpected error: unable to find constructor for {localRPropTCName}"
          let ctorArgs ← do
            let targetInstInfo ← getConstInfo targetInstName
            let mut argsMore := xs.take (targetInstInfo.type.getForallArity - 1)    -- the 1 accounts for the `post` parameter
            -- `self` is the definition `nmFull` applied to all arguments except `th` and `st`,
            -- so do a special check: if `th` and `st` are at the tail position, then just pop them;
            -- otherwise use `mkLambdaFVars` to build it
            let self ← do
              let thPos := xs.idxOf th
              let stPos := xs.idxOf st
              if thPos == xs.size - 2 && stPos == xs.size - 1 then
                mkAppOptM nmFull (xs.pop.pop |>.map Option.some)
              else
                let tmp ← mkAppOptM nmFull (xs.map Option.some)
                mkLambdaFVars #[th, st] tmp
            argsMore := argsMore.push self
            pure argsMore
          let inst ← Meta.mkAppOptM ctor.name (ctorArgs |>.push core |>.push coreEq |>.map Option.some)
          mkLambdaFVars xs inst (usedOnly := true)
  check inst
  let inst ← instantiateMVars inst
  trace[veil.debug] "LocalRProp instance for {nm}: {inst}"
  return inst

/-! ## Instance Registration -/

/-- Prove locality for the state predicate `nm`, and register
the corresponding `LocalRProp` instance in the module. Any error
will be caught and logged as a warning. -/
def Module.proveLocalityForStatePredicate (mod : Module) (nm : Name) (stx : Syntax) : TermElabM Unit := do
  try
    let inst ← mod.proveLocalityForStatePredicateCore nm
    let attrs ← do
      let tmp ← `(Parser.Term.attrInstance| scoped instance)
      elabAttrs (#[tmp])
    let _ ← addVeilDefinition (generateLocalRPropInstName nm) inst (attr := attrs)
  catch ex =>
    logWarningAt stx s!"unable to prove locality for state predicate {nm}: {← ex.toMessageData.toString}"
where
  generateLocalRPropInstName (nm : Name) : Name :=
    Name.mkSimple <| "instLocalRProp" ++ nm.capitalize.toString

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
