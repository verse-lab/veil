import Veil.Frontend.DSL.Module.Util.Assertions

open Lean Parser Elab Command Term Meta Tactic

namespace Veil

/-! ## LocalRProp Typeclass Declaration -/

/-- Declare the `LocalRProp` typeclass for the module.
Its general form is:
```lean
class LocalRPropTC /- module parameters -/ {α : Type} (post : RProp α ρ σ)
where
  core : α →
    /- types of fields of `Theory`, connected with `→` -/ →
    /- types of _canonical_ fields of `State`, connected with `→` -/ → Prop
  core_eq : ∀ (a : α) (th : ρ) (st : σ),
    post a th st = core a /- fields of `Theory` -/ /- _canonical_ fields of `State` -/
```
-/
def Module.declareLocalRPropTC (mod : Module) : MetaM (Command × Command) := do
  -- this can be given fewer parameters, but for simplicity we give it all of them
  let params := mod.parameters
  let mut binders ← params.mapM (·.binder)
  -- build binders
  let α ← Lean.mkIdent <$> mkFreshUserName `α
  let post ← Lean.mkIdent <$> mkFreshUserName `post
  let core := mkIdent `core ; let core_eq := mkIdent `core_eq
  binders := binders.push (← `(bracketedBinder| {$α : Type} ))
  binders := binders.push (← `(bracketedBinder| ($post : $(mkIdent ``RProp) $α $environmentTheory $environmentState) ))
  -- build the type of `core`
  let coreType ← do
    let theoryFields ← mod.immutableComponents.mapM (·.getSimpleBinder >>= getSimpleBinderType)
    let stateFields ← mod.mutableComponents.mapM (·.getSimpleBinder >>= getSimpleBinderType)
    mkArrowStx (α :: (theoryFields ++ stateFields).toList) (← `(term| Prop ))
  -- build the type of `core_eq`
  let a ← Lean.mkIdent <$> mkFreshUserName `a
  let th ← Lean.mkIdent <$> mkFreshUserName `th
  let st ← Lean.mkIdent <$> mkFreshUserName `st
  let coreEqType ← do
    let body ← mod.withTheoryAndStateTermTemplate [(.theory, th), (.state .none "_conc", st)] fun theoryFieldNames stateFieldNames =>
      pure <| Syntax.mkApp core (#[a] ++ theoryFieldNames ++ stateFieldNames)
    `(term| ∀ ($a : $α) ($th : $environmentTheory) ($st : $environmentState),
    $post $a $th $st = $body)
  let cmd1 ← `(command| class $localRPropTC $[$binders]* where
      $core:ident : $coreType
      $core_eq:ident : $coreEqType)
  let cmd2 ← `(command| attribute [$(mkIdent `wpSimp):ident] $(mkIdent <| localRPropTCName ++ `core):ident)
  return (cmd1, cmd2)

/-! ## Simplification Infrastructure -/

/-- This `dsimproc` attempts to replace assertions that have associated
`LocalRProp` instances with their `core` definitions. -/
dsimproc_decl replaceLocalRProp (_) := fun e => do
  let f := e.getAppFn'
  let args := e.getAppArgs'
  unless f.isConst && args.size ≥ 4 do return .continue
  -- search for the `LocalRProp` instance of `nm`
  -- NOTE: The following code relies on some hacks
  try
    let targetInstType ← do
      let targetInstName ← resolveGlobalConstNoOverloadCore localRPropTCName
      let targetInstInfo ← getConstInfo targetInstName
      let mut argsMore := args.take (targetInstInfo.type.getForallArity - 2)    -- the 2 is also a magic number here
      argsMore := argsMore.push (mkConst ``Unit)
      let self ← do
        let ρ := args[0]! ; let σ := args[1]!
        -- remove the arguments representing theory and state from `args`,
        -- by a heuristic
        let args' := args.reverse
        let some thPos ← args'.findIdxM? fun a => do isDefEq (← inferType a) ρ
          | return .continue
        let thPos := args.size - 1 - thPos
        let some stPos ← args'.findIdxM? fun a => do isDefEq (← inferType a) σ
          | return .continue
        let stPos := args.size - 1 - stPos
        -- a special check: see the comment below
        if thPos == args.size - 2 && stPos == args.size - 1 then
          pure <| mkAppN f (args.pop.pop)
        else
          let thName ← mkFreshUserName `th ; let stName ← mkFreshUserName `st
          withLocalDeclsDND #[(thName, ρ.consumeMData), (stName, σ.consumeMData)] fun ldecls => do
            let argsAbstracted := args.set! thPos ldecls[0]! |>.set! stPos ldecls[1]!
            mkLambdaFVars ldecls <| mkAppN f argsAbstracted
      argsMore := argsMore.push (← mkFunUnit self)
      mkAppOptM targetInstName (argsMore.map Option.some)
    let e ← synthInstance targetInstType
    let coreFn ← Meta.mkProjection e `core
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
      pure <| mkAppN coreFn (#[Lean.mkConst (``Unit.unit)] ++ fieldVars)
    return .done coreApp
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
def Module.proveLocalityForStatePredicateCore (mod : Module) (nm : Name) : MetaM Expr := do
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
            /-
            let tmp ← mkLambdaFVars (theoryFields ++ stateFieldsInUse) body >>= mkFunUnit
            (Simp.dsimp #[``replaceLocalRProp]) tmp
            -/
            let tmp ← (Simp.dsimp #[``replaceLocalRProp]) body
            let res ← mkLambdaFVars (theoryFields ++ stateFieldsInUse) tmp.expr
            -- pure (← mkFunUnit res, ← tmp.getProof)
            mkFunUnit res
          trace[veil.debug] "core for LocalRProp instance of {nm}: {core}"
          -- the `core_eq` should have `proof` inside
          let coreEq ← do
            let a ← mkFreshUserName `a ; let thName ← mkFreshUserName `th ; let stName ← mkFreshUserName `st
            withLocalDeclsDND #[(a, (mkConst ``Unit)), (thName, ρ.consumeMData), (stName, σ.consumeMData)] fun ldecls => do
              let xs' := xs.replace th ldecls[1]! |>.replace st ldecls[2]!
              let self ← mkAppOptM nmFull (xs'.map Option.some)
              let eqrefl ← mkEqRefl self
              mkLambdaFVars ldecls eqrefl
          -- now, build the instance
          let targetInstName ← resolveGlobalConstNoOverloadCore localRPropTCName
          let some ctor := getStructureLikeCtor? (← getEnv) targetInstName
            | throwError "unexpected error: unable to find constructor for {localRPropTCName}"
          let ctorArgs ← do
            let targetInstInfo ← getConstInfo targetInstName
            let mut argsMore := xs.take (targetInstInfo.type.getForallArity - 2)    -- the 2 is also a magic number here
            argsMore := argsMore.push (mkConst ``Unit)
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
            argsMore := argsMore.push (← Meta.mkFunUnit self)
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
      let tmp ← `(Parser.Term.attrInstance| instance)
      elabAttrs (#[tmp])
    let _ ← addVeilDefinition (generateLocalRPropInstName nm) inst (attr := attrs)
  catch ex =>
    logWarningAt stx s!"unable to prove locality for state predicate {nm}: {← ex.toMessageData.toString}"
where
  generateLocalRPropInstName (nm : Name) : Name :=
    Name.mkSimple <| "instLocalRProp" ++ nm.capitalize.toString

end Veil
