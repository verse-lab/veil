import Lean
import Smt
import ProofWidgets.Compat
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Names
import Veil.Frontend.DSL.Module.Util.Basic
import Veil.Frontend.DSL.Module.Util.StateTheory
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Core.UI.Verifier.Model

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

/-! ## Data Structure -/

/-- A structured counterexample for induction VCs.
    Parametric over module-specific types to enable ToJson serialization. -/
structure InductionCounterexample (Inst ρ σ l : Type)
    [ToJson Inst] [ToJson ρ] [ToJson σ] [ToJson l] where
  /-- The Instantiation value (e.g., { node := Fin 2 }). -/
  inst : Inst
  /-- Background theory value of type `Theory sorts*`. -/
  backgroundTheory : ρ
  /-- Pre-state value of type `State (FieldAbstractType sorts*)`. -/
  preState : σ
  /-- Post-state value (optional). May be none for init VCs. -/
  postState : Option σ
  /-- Action label of type `Label sorts*`. -/
  label : l
  /-- Any remaining values that don't fit above categories (as Expr pairs). -/
  extraVals : Array (Expr × Expr)
  /-- Sorts not part of module's Instantiation. -/
  extraSorts : Array (Expr × Expr)
  /-- Context for interpreting extraVals/extraSorts expressions. -/
  ctx : ModelContext

instance [ToJson Inst] [ToJson ρ] [ToJson σ] [ToJson l] :
    ToJson (InductionCounterexample Inst ρ σ l) where
  toJson ce := Json.mkObj [
    ("instantiation", toJson ce.inst),
    ("backgroundTheory", toJson ce.backgroundTheory),
    ("preState", toJson ce.preState),
    ("postState", toJson ce.postState),
    ("label", toJson ce.label)
    -- Note: extraVals/extraSorts would need special handling via pretty-printing
  ]

/-! ## Helper Functions -/

/-- Convert an SMT model function that uses Prop to one that uses Bool.

    SMT models may convert `Bool` types to `Prop` in both arguments and return types.
    For example, a relation `r : node -> Bool -> Bool` might be returned as
    `r_smt : node -> Prop -> Prop`.

    This function creates a wrapper that:
    - For arguments where expected is Bool but SMT expects Prop: converts via `(· = true)`
    - For return where expected is Bool but SMT returns Prop: converts via `decide`

    Parameters:
    - `smtExpr`: The expression from the SMT model (with Prop types)
    - `expectedType`: The expected type (with Bool types)

    Throws an error if no Decidable instance can be synthesized for the return type. -/
def adaptSmtExprType (smtExpr : Expr) (expectedType : Expr) : MetaM Expr := do
  -- VERY IMPOTANT that we reduce the types
  let expectedType ← Meta.reduceAll expectedType
  let smtType ← Meta.reduceAll (← Meta.inferType smtExpr)
  -- dbg_trace "expectedType: {expectedType}"
  -- dbg_trace "smtType: {smtType}"
  -- If types already match, no conversion needed
  if ← Meta.isDefEq smtType expectedType then
    return smtExpr

  -- Decompose both types to compare argument-by-argument
  Meta.forallTelescope expectedType fun expectedArgs expectedRetTy => do
    Meta.forallTelescope smtType fun smtArgs smtRetTy => do
      -- Get the argument types from both
      let expectedArgTypes ← expectedArgs.mapM Meta.inferType
      let smtArgTypes ← smtArgs.mapM Meta.inferType

      -- Create new bound variables with the expected types
      Meta.withLocalDeclsD (expectedArgTypes.mapIdx fun i ty =>
        (Name.mkSimple s!"arg{i}", fun _ => pure ty)) fun newArgs => do

        -- Build application: smtExpr applied to converted arguments
        let mut app := smtExpr
        for i in [:newArgs.size] do
          let newArg := newArgs[i]!
          let expectedArgTy := expectedArgTypes[i]!
          let smtArgTy := smtArgTypes[i]!

          -- dbg_trace "arg{i}: {expectedArgTy} -> {smtArgTy}"

          -- Check if we need to convert Bool -> Prop for this argument
          -- (expected is Bool, but SMT expects Prop)
          if expectedArgTy.isBool && smtArgTy.isProp then
            -- Convert Bool arg to Prop via `arg = true`
            let propArg ← Meta.mkAppM ``Eq #[newArg, mkConst ``Bool.true]
            app := mkApp app propArg
          else
            app := mkApp app newArg

        -- Check if we need to convert return from Prop -> Bool
        let result ← if expectedRetTy.isBool && smtRetTy.isProp then
          -- dbg_trace "Wrapping with decide: {expectedRetTy} ≠ {smtRetTy}"
          -- Wrap with decide
          Meta.mkAppOptM ``decide #[some app, none]
        else
          -- dbg_trace "No need to wrap with decide: {expectedRetTy} = {smtRetTy}"
          pure app

        -- Build the lambda with expected argument types
        let res ← Meta.mkLambdaFVars newArgs result
        -- dbg_trace "{← ppExpr smtExpr}\n->\n{← ppExpr res}\n\n"
        return res

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
      -- Check if it's an action parameter
      else if actionParamNames.contains name then
        actionParams := actionParams.insert name valueExpr
      -- Check if it's a theory field
      else if theoryFieldNames.contains name then
        theoryFields := theoryFields.insert name valueExpr
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
    | none => throwError "Sort {param.name} not found in model"
  mkAppM (instName ++ `mk) sortArgs

/-- Build a State struct literal expression from field values.
    Handles Prop<->Bool conversion for SMT model values. -/
def buildStateExpr (mod : Module) (sortArgs : Array Expr)
    (fieldMap : Std.HashMap Name Expr) : MetaM Expr := do
  let stateName := mod.name ++ `State
  let fieldAbstractTypeName := mod.name ++ fieldAbstractDispatcherName
  let dispatcher ← mkAppM fieldAbstractTypeName sortArgs
  let fieldValues ← mod.mutableComponents.mapM fun sc => do
    match fieldMap[sc.name]? with
    | some e =>
      -- Get expected type via FieldAbstractType sortArgs* fieldLabel
      let fieldLabelName := mod.name ++ `State ++ `Label ++ sc.name
      let fieldLabel := mkConst fieldLabelName
      let expectedType ← mkAppM fieldAbstractTypeName (sortArgs.push fieldLabel)
      adaptSmtExprType e expectedType
    | none => throwError "State field {sc.name} not found in model"
  mkAppOptM (stateName ++ `mk) <| (#[dispatcher] ++ fieldValues).map (Option.some ·)

/-- Build a Theory struct literal expression from field values.
    Handles Prop<->Bool conversion for SMT model values. -/
def buildTheoryExpr (mod : Module) (sortArgs : Array Expr)
    (fieldMap : Std.HashMap Name Expr) : MetaM Expr := do
  let theoryName := mod.name ++ `Theory
  let fieldValues ← mod.immutableComponents.mapM fun sc => do
    match fieldMap[sc.name]? with
    | some e =>
      -- Get expected type from the field projector: Theory.fieldName : ∀ sorts..., Theory sorts... → FieldType
      let projName := theoryName ++ sc.name
      let projType ← Meta.inferType (mkConst projName)
      -- Apply sort args to get: Theory sorts... → FieldType
      let projTypeInstantiated ← Meta.instantiateForall projType sortArgs
      -- Extract the return type (FieldType)
      let expectedType ← Meta.forallTelescope projTypeInstantiated fun _ retTy => pure retTy
      adaptSmtExprType e expectedType
    | none => throwError "Theory field {sc.name} not found in model"
  mkAppOptM (theoryName ++ `mk) <| (sortArgs ++ fieldValues).map (Option.some ·)

/-- Build a Label constructor expression from action name and params. -/
def buildLabelExpr (mod : Module) (sortArgs : Array Expr)
    (actionName : Name) (paramMap : Std.HashMap Name Expr) : MetaM Expr := do
  let labelName := mod.name ++ `Label ++ actionName
  let proc := mod.procedures.find? (·.name == actionName)
  let paramValues ← match proc with
    | some p => p.params.mapM fun param =>
        match paramMap[param.name]? with
        | some e => pure e
        | none => throwError "Action parameter {param.name} not found in model"
    | none => pure #[]
  mkAppOptM labelName <| (sortArgs ++ paramValues).map (Option.some ·)

/-! ## Main Construction -/

/-- Get the sort arguments (cardinality types) from the model in the order expected by the module. -/
def getSortArgs (mod : Module) (sortMap : Std.HashMap Name Expr) : MetaM (Array Expr) := do
  mod.sortParams.mapM fun (param, _) =>
    match sortMap[param.name]? with
    | some e => pure e
    | none => throwError "Sort {param.name} not found in model"

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

  -- Separate module sorts from extra sorts
  let moduleSortNames := mod.sortParams.map (·.1.name) |>.toList
  let mut extraSorts : Array (Expr × Expr) := #[]
  for (sortExpr, cardExpr) in model.sorts do
    let name? ← getExprName model.ctx sortExpr
    match name? with
    | some name =>
      if !moduleSortNames.contains name then
        extraSorts := extraSorts.push (sortExpr, cardExpr)
    | none =>
      extraSorts := extraSorts.push (sortExpr, cardExpr)

  -- Get sort arguments in module order
  let sortArgs ← getSortArgs mod sortMap

  -- Classify model values
  let (preStateFields, postStateFields, theoryFields, actionParams, extraVals) ←
    classifyModelValues model mod actionName

  -- Build Instantiation expression and type
  let instExpr ← buildInstantiationExpr mod sortMap
  let instType := mkConst (mod.name ++ `Instantiation)
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

  -- Build Label expression and type
  let labelExpr ← buildLabelExpr mod sortArgs actionName actionParams
  let labelType ← mkAppM (mod.name ++ `Label) sortArgs
  -- dbg_trace "labelExpr: {← ppExpr labelExpr} | labelType: {← ppExpr labelType}"

  return {
    instExpr, instType
    theoryExpr, theoryType
    preStateExpr, stateType
    postStateExpr
    labelExpr, labelType
    extraVals, extraSorts
    ctx := model.ctx
  }

end Veil
