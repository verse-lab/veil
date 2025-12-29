import Lean
import Smt
import ProofWidgets.Compat
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Names
import Veil.Frontend.DSL.Module.Util.Basic
import Veil.Frontend.DSL.Module.Util.StateTheory
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Core.UI.Verifier.Model
import Veil.Backend.SMT.Model

/-!
# Induction Counterexample

This module provides structured representation of SMT counterexamples for induction
(invariant preservation) verification conditions.

An induction counterexample consists of:
- A pre-state (`st`)
- A post-state (`st'`)
- A transition label (action with parameters)
- Background theory values
- Sort instantiations
-/

namespace Veil

open Lean Elab Meta Smt

/-- Evaluate an expression to JSON by dynamically synthesizing the `ToJson`
instance. This function works without knowing the type at compile time. -/
private unsafe def evalExprToJson (typeExpr : Expr) (valueExpr : Expr) : MetaM Json := do
  let toJsonType ← Meta.mkAppM ``ToJson #[typeExpr]
  let toJsonInst ← Meta.synthInstance toJsonType
  let jsonExpr ← Meta.mkAppOptM ``toJson #[some typeExpr, some toJsonInst, some valueExpr]
  Meta.evalExpr Json (mkConst ``Json) jsonExpr

/-- Convert a `VeilModel` to a JSON object containing the structured counterexample.

  This function works dynamically without requiring explicit type parameters.
  It synthesizes `ToJson` instances at runtime using the type expressions
  stored in the `VeilModel`. -/

unsafe def VeilModel.toJson (vm : VeilModel) : MetaM Json := do
  -- Build instantiation JSON from sortInstInfo (since Type fields are erased at runtime)
  let instJson := Json.mkObj <| vm.sortInstInfo.toList.map fun (name, typeStr) =>
    (name.toString, Json.str typeStr)
  let theoryJson ← evalExprToJson vm.theoryType vm.theoryExpr
  let preStateJson ← evalExprToJson vm.stateType vm.preStateExpr
  let postStateJson ← match vm.postStateExpr with
    | some e => evalExprToJson vm.stateType e
    | none => pure Json.null
  let labelJson ← match vm.labelExpr, vm.labelType with
    | some labelExpr, some labelType => evalExprToJson labelType labelExpr
    | _, _ => pure (Json.str "initializer")

  -- Build extraSorts JSON: map from sort name to cardinality type (similar to instJson)
  let extraSortsJson := Json.mkObj <| ← vm.extraSorts.toList.mapM fun (sortExpr, cardExpr) => do
    let ectx := vm.ctx.toExprWithCtx sortExpr
    ectx.runMetaM fun sortExpr => do
      let nameStr := (← Meta.ppExpr sortExpr).pretty
      let typeStr := (← Meta.ppExpr cardExpr).pretty
      return (nameStr, Json.str typeStr)

  -- Build extraVals JSON: substitute abstract sorts with concrete types and Prop with Bool
  let sortFVars := vm.sortSubst.map (·.1)
  let sortTypes := vm.sortSubst.map (·.2)
  let extraValsJson := Json.mkObj <| ← vm.extraVals.toList.mapM fun (nameExpr, valueExpr) => do
    (vm.ctx.toExprWithCtx nameExpr).runMetaM fun nameExpr => do
      let nameStr := (← Meta.ppExpr nameExpr).pretty
      let concreteType := ((← Meta.inferType nameExpr).replaceFVars sortFVars sortTypes).replace
        fun e => if e.isProp then some (mkConst ``Bool) else none
      let adapted ← adaptSmtExprType valueExpr concreteType
      return (nameStr, ← evalExprToJson (← Meta.inferType adapted) adapted)

  return Json.mkObj [
    ("instantiation", instJson),
    ("theory", theoryJson),
    ("preState", preStateJson),
    ("label", labelJson),
    ("postState", postStateJson),
    ("extraSorts", extraSortsJson),
    ("extraVals", extraValsJson),
  ]

/-! ## Helper Functions -/

/-- Extract the user name from an fvar expression using the model context. -/
def getExprName (ctx : ModelContext) (e : Expr) : IO (Option Name) := do
  let ectx := ctx.toExprWithCtx e
  ectx.runMetaM fun e =>
    if e.isFVar then
      return some (← e.fvarId!.getUserName)
    else
      return none

/-- Check if a name matches the pattern "st.fieldName" and return fieldName. -/
def isPreStateField (n : Name) : Option Name :=
  match n with
  | .str (.str .anonymous "st") fieldName => some (.mkSimple fieldName)
  | _ => none

/-- Check if a name matches the pattern "st'.fieldName" and return fieldName. -/
def isPostStateField (n : Name) : Option Name :=
  match n with
  | .str (.str .anonymous "st'") fieldName => some (.mkSimple fieldName)
  | _ => none

/-- Check if a name matches the pattern "th.fieldName" and return fieldName. -/
def isTheoryField (n : Name) : Option Name :=
  match n with
  | .str (.str .anonymous "th") fieldName => some (.mkSimple fieldName)
  | _ => none

/-- Parse model sorts into a map from sort name to cardinality type (Fin n). -/
def parseSortsFromModel (model : Model) : IO (Std.HashMap Name Expr) := do
  let mut sortMap : Std.HashMap Name Expr := {}
  for (sortExpr, cardExpr) in model.sorts do
    let name? ← getExprName model.ctx sortExpr
    if let some name := name? then
      sortMap := sortMap.insert name cardExpr
  return sortMap

/-- Classify model values into state fields, theory fields, action params, and extras. -/
def classifyModelValues (model : Model) (mod : Module) (actionName : Name)
    : IO (Std.HashMap Name Expr × Std.HashMap Name Expr ×
          Std.HashMap Name Expr × Std.HashMap Name Expr ×
          Array (Expr × Expr)) := do
  let stateFieldNames := mod.mutableComponents.map (·.name) |>.toList
  let theoryFieldNames := mod.immutableComponents.map (·.name) |>.toList
  let actionParamNames := match mod.procedures.find? (fun (p : ProcedureSpecification) => p.name == actionName) with
    | some proc => proc.params.map (fun (p : Parameter) => p.name) |>.toList
    | none => []

  let mut preStateFields : Std.HashMap Name Expr := {}
  let mut postStateFields : Std.HashMap Name Expr := {}
  let mut theoryFields : Std.HashMap Name Expr := {}
  let mut actionParams : Std.HashMap Name Expr := {}
  let mut extraVals : Array (Expr × Expr) := #[]

  for (nameExpr, valueExpr) in model.values do
    let name? ← getExprName model.ctx nameExpr
    match name? with
    | some name =>
      -- Check if it's a pre-state field (st.fieldName)
      if let some fieldName := isPreStateField name then
        if stateFieldNames.contains fieldName then
          preStateFields := preStateFields.insert fieldName valueExpr
        else
          extraVals := extraVals.push (nameExpr, valueExpr)
      -- Check if it's a post-state field (st'.fieldName)
      else if let some fieldName := isPostStateField name then
        if stateFieldNames.contains fieldName then
          postStateFields := postStateFields.insert fieldName valueExpr
        else
          extraVals := extraVals.push (nameExpr, valueExpr)
      -- Check if it's a theory field (th.fieldName)
      else if let some fieldName := isTheoryField name then
        if theoryFieldNames.contains fieldName then
          theoryFields := theoryFields.insert fieldName valueExpr
        else
          extraVals := extraVals.push (nameExpr, valueExpr)
      -- Check if it's an action parameter
      else if actionParamNames.contains name then
        actionParams := actionParams.insert name valueExpr
      else
        extraVals := extraVals.push (nameExpr, valueExpr)
    | none =>
      extraVals := extraVals.push (nameExpr, valueExpr)

  return (preStateFields, postStateFields, theoryFields, actionParams, extraVals)

/-! ## Expression Building Functions -/

/-- Build an Instantiation struct literal expression from model sorts. -/
def buildInstantiationExpr (mod : Module) (sortMap : Std.HashMap Name Expr) : MetaM Expr := do
  let instName := mod.name ++ `Instantiation
  let sortArgs ← mod.sortParams.mapM fun (param, _) =>
    match sortMap[param.name]? with
    | some e => pure e
    | none =>
      -- dbg_trace "Sort {param.name} not found in model, using Fin 1 as default"
      pure (mkApp (mkConst ``Fin) (mkNatLit 1))
  mkAppM (instName ++ `mk) sortArgs

/-- Build a State struct literal expression from field values.
    Handles Prop<->Bool conversion for SMT model values.
    Uses `default` for fields not present in the model. -/
def buildStateExpr (mod : Module) (sortArgs : Array Expr)
    (fieldMap : Std.HashMap Name Expr) : MetaM Expr := do
  let stateName := mod.name ++ `State
  let fieldAbstractTypeName := mod.name ++ fieldAbstractDispatcherName
  let dispatcher ← mkAppM fieldAbstractTypeName sortArgs
  let fieldValues ← mod.mutableComponents.mapM fun sc => do
    -- Get expected type via FieldAbstractType sortArgs* fieldLabel
    let fieldLabelName := mod.name ++ `State ++ `Label ++ sc.name
    let fieldLabel := mkConst fieldLabelName
    let expectedType ← Meta.reduceAll (← mkAppM fieldAbstractTypeName (sortArgs.push fieldLabel))
    match fieldMap[sc.name]? with
    | some e => adaptSmtExprType e expectedType
    | none =>
      -- dbg_trace "State field {sc.name} not found in model, using default"
      mkAppOptM ``default #[some expectedType, none]
  mkAppOptM (stateName ++ `mk) <| (#[dispatcher] ++ fieldValues).map (Option.some ·)

/-- Build a Theory struct literal expression from field values.
    Handles Prop<->Bool conversion for SMT model values.
    Uses `default` for fields not present in the model. -/
def buildTheoryExpr (mod : Module) (sortArgs : Array Expr)
    (fieldMap : Std.HashMap Name Expr) : MetaM Expr := do
  let theoryName := mod.name ++ `Theory
  let fieldValues ← mod.immutableComponents.mapM fun sc => do
    -- Get expected type from the field projector: Theory.fieldName : ∀ sorts..., Theory sorts... → FieldType
    let projName := theoryName ++ sc.name
    let projType ← Meta.inferType (mkConst projName)
    -- Apply sort args to get: Theory sorts... → FieldType
    let projTypeInstantiated ← Meta.instantiateForall projType sortArgs
    -- Extract the return type (FieldType) by skipping only the first forall (the Theory argument)
    let expectedType ← Meta.reduceAll (← Meta.forallBoundedTelescope projTypeInstantiated (some 1) fun _ retTy => pure retTy)
    match fieldMap[sc.name]? with
    | some e => adaptSmtExprType e expectedType
    | none =>
      -- dbg_trace "Theory field {sc.name} not found in model, using default"
      mkAppOptM ``default #[some expectedType, none]
  mkAppOptM (theoryName ++ `mk) <| (sortArgs ++ fieldValues).map (Option.some ·)

/-- Build a Label constructor expression from action name and params.
    Uses `default` for parameters not present in the model.
    Returns `none` if the action is an initializer (which has no Label constructor). -/
def buildLabelExpr (mod : Module) (sortArgs : Array Expr)
    (actionName : Name) (paramMap : Std.HashMap Name Expr) : MetaM (Option Expr) := do
  let proc := mod.procedures.find? (·.name == actionName)
  match proc with
  | some p =>
    -- Check if this is an initializer (which doesn't have a Label constructor)
    match p.info with
    | .initializer => return none
    | _ =>
      let labelName := mod.name ++ `Label ++ actionName
      -- Get the constructor type to extract parameter types
      let ctorType ← Meta.inferType (mkConst labelName)
      -- Apply sort args to get the instantiated constructor type
      let ctorTypeInst ← Meta.instantiateForall ctorType sortArgs
      -- Extract the parameter types from the constructor signature
      let paramValues ← Meta.forallTelescope ctorTypeInst fun args _ => do
        p.params.mapIdxM fun idx param => do
          match paramMap[param.name]? with
          | some e => pure e
          | none =>
            let expectedType ← Meta.reduceAll (← Meta.inferType args[idx]!)
            -- dbg_trace "Action parameter {param.name} not found in model, using default"
            mkAppOptM ``default #[some expectedType, none]
      some <$> mkAppOptM labelName ((sortArgs ++ paramValues).map (Option.some ·))
  | none => return none

/-! ## Main Construction -/

/-- Get the sort arguments (cardinality types) from the model in the order expected by the module. -/
def getSortArgs (mod : Module) (sortMap : Std.HashMap Name Expr) : MetaM (Array Expr) := do
  mod.sortParams.mapM fun (param, _) =>
    match sortMap[param.name]? with
    | some e => pure e
    | none =>
      -- dbg_trace "Sort {param.name} not found in model, using Fin 1 as default"
      pure (mkApp (mkConst ``Fin) (mkNatLit 1))

/-- Build all counterexample expressions from a Model.
    Returns expressions that can be converted to runtime values via evalExpr.

    The caller should use `evalExpr` with the module-specific types to convert
    the expressions to runtime values:
    ```
    let inst ← unsafe Meta.evalExpr Mod.Instantiation instType instExpr
    let theory ← unsafe Meta.evalExpr (Mod.Theory ...) theoryType theoryExpr
    -- etc.
    ```
-/
def buildCounterexampleExprs (model : Model) (mod : Module) (actionName : Name) : MetaM VeilModel := do
  -- Parse sorts from model
  let sortMap ← parseSortsFromModel model

  -- Build sort substitution map: module sort fvars -> concrete types
  let moduleSortNames := mod.sortParams.map (·.1.name) |>.toList
  let sortSubst ← model.sorts.filterM fun (sortExpr, _) => do
    return (← getExprName model.ctx sortExpr).any moduleSortNames.contains

  -- Separate extra sorts (those not part of module's Instantiation)
  let extraSorts ← model.sorts.filterM fun (sortExpr, _) => do
    return !(← getExprName model.ctx sortExpr).any moduleSortNames.contains

  -- Get sort arguments in module order
  let sortArgs ← getSortArgs mod sortMap

  -- Classify model values
  let (preStateFields, postStateFields, theoryFields, actionParams, extraVals) ←
    classifyModelValues model mod actionName

  -- Build Instantiation expression and type
  let instExpr ← buildInstantiationExpr mod sortMap
  let instType := mkConst (mod.name ++ `Instantiation)
  -- Build sort instantiation info (for JSON serialization, since Type is erased at runtime)
  let sortInstInfo ← (mod.sortParams.zip sortArgs).mapM fun ((param, _), cardExpr) => do
    let typeStr ← Meta.ppExpr cardExpr
    pure (param.name, typeStr.pretty)
  -- dbg_trace "instExpr: {← ppExpr instExpr} | instType: {← ppExpr instType}"

  -- Build Theory expression and type
  let theoryExpr ← buildTheoryExpr mod sortArgs theoryFields
  let theoryType ← mkAppOptM (mod.name ++ `Theory) <| sortArgs.map (Option.some ·)
  -- dbg_trace "theoryExpr: {← ppExpr theoryExpr} | theoryType: {← ppExpr theoryType}"

  -- Build State expressions and type
  let preStateExpr ← buildStateExpr mod sortArgs preStateFields
  let fieldAbstractTypeName := mod.name ++ fieldAbstractDispatcherName
  let dispatcher ← mkAppM fieldAbstractTypeName sortArgs
  let stateType ← mkAppM (mod.name ++ `State) #[dispatcher]
  -- dbg_trace "preStateExpr: {← ppExpr preStateExpr} | stateType: {← ppExpr stateType}"

  let postStateExpr ← if postStateFields.isEmpty then
    pure none
  else
    some <$> buildStateExpr mod sortArgs postStateFields
  -- dbg_trace "postStateExpr: {← if postStateExpr.isSome then do ppExpr postStateExpr.get! else pure "none"} | postStateType: { ← ppExpr stateType}"

  -- Build Label expression and type (none for initializers)
  let labelExpr ← buildLabelExpr mod sortArgs actionName actionParams
  let labelType ← match labelExpr with
    | some _ => some <$> mkAppM (mod.name ++ `Label) sortArgs
    | none => pure none
  -- dbg_trace "labelExpr: {← match labelExpr with | some e => ppExpr e | none => pure "none"} | labelType: {← match labelType with | some t => ppExpr t | none => pure "none"}"

  return {
    instExpr, instType, sortInstInfo, sortSubst
    theoryExpr, theoryType
    preStateExpr, stateType
    postStateExpr
    labelExpr, labelType
    extraVals, extraSorts
    ctx := model.ctx
  }

end Veil
