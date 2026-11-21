module

public meta import Lean
public meta import Smt
public meta import ProofWidgets.Compat
public meta import Veil.Frontend.DSL.Module.Representation
public meta import Veil.Frontend.DSL.Module.Names
public meta import Veil.Frontend.DSL.Module.Util.Basic
public meta import Veil.Frontend.DSL.Module.Util.StateTheory
public meta import Veil.Frontend.DSL.Infra.EnvExtensions
public meta import Veil.Core.UI.Verifier.Model
public meta import Veil.Core.UI.Verifier.InductionCounterexample
public meta import Veil.Backend.SMT.Model

public meta section

/-!
# Trace Counterexample

This module provides structured representation of SMT counterexamples for symbolic
trace queries (`sat trace` / `unsat trace`).

A trace counterexample consists of:
- A sequence of states (`st0`, `st1`, ..., `stn`)
- Transition labels between consecutive states
- Background theory values
- Sort instantiations

The naming conventions from TraceLang.lean are:
- States: `st0`, `st1`, `st2`, ..., `stn`
- Tags: `_tr1_tag`, `_tr2_tag`, etc.
- Params (specific action): `_tr{trIdx}_arg{argIdx}_{paramName}`
- Params (any action): `_tr{trIdx}_act_{actionName}_arg{argIdx}_{paramName}`
-/

namespace Veil

open Lean Elab Meta Smt

/-! ## VeilTrace Structure -/

/-- A structured representation of a trace counterexample from an SMT model.
    This parallels `VeilModel` but for multi-step traces. -/
structure VeilTrace where
  /-- Context for interpreting expressions -/
  ctx : Smt.ModelContext

  /-- Sort instantiation info: maps sort name to pretty-printed type name. -/
  sortInstInfo : Array (Name × String) := #[]
  /-- Substitution of original sort and value parameters by their concrete model arguments. -/
  sortSubst : Array (Expr × Expr) := #[]
  /-- Enum sort adaptations used for converting SMT `Fin` values to enum constructors. -/
  enumAdapts : Array EnumSortAdaptation := #[]

  /-- Sorts not part of module's Instantiation -/
  extraSorts : Array (Expr × Expr)

  /-- Expression for `Theory.mk sortArgs* fieldValues*` -/
  theoryExpr : Expr
  /-- Type expression for `Theory sortArgs*` -/
  theoryType : Expr

  /-- Type expression for `State (FieldAbstractType sortArgs*)` -/
  stateType : Expr
  /-- Array of state expressions, indexed 0..n (st0, st1, ..., stn) -/
  stateExprs : Array Expr

  /-- Type expression for `Label sortArgs*` -/
  labelType : Expr
  /-- Array of label expressions for transitions (one fewer than states) -/
  labelExprs : Array Expr

  /-- Values that couldn't be classified -/
  extraVals : Array (Expr × Expr)

/-! ## Main Construction -/

/-- Build a VeilTrace from an SMT Model.
    `numTransitions` is the number of transitions in the trace (states = numTransitions + 1). -/
def buildTraceFromModel (model : Model) (mod : Module) (numTransitions : Nat)
    : MetaM VeilTrace := do
  let numStates := numTransitions + 1

  -- Parse sorts from model
  let sortMap ← parseSortsFromModel model

  -- Resolve sort arguments (including enum concretization when mappings are complete)
  let (sortArgs, enumAdapts) ← resolveSortArgsAndEnumAdapts model mod sortMap

  -- Resolve the complete structural parameter list and its dependent substitution.
  let (moduleArgs, sortSubst) ← resolveModuleArgs model mod sortArgs enumAdapts

  -- Separate extra sorts
  let moduleSortNames := mod.sortParams.map (·.1.name) |>.toList
  let extraSorts ← model.sorts.filterM fun (sortExpr, _) => do
    return !(← getExprName model.ctx sortExpr).any moduleSortNames.contains

  -- Only Veil's marked binders participate in reconstruction. Keep the full
  -- projection path when a tactic has split a structure before calling SMT.
  let mut values : Std.HashMap Name Expr := {}
  let mut extraVals := #[]
  for (e, value) in model.values do
    if let some key := (← getExprName model.ctx e).bind modelBinderKey? then
      values := values.insert key value
    else
      extraVals := extraVals.push (e, value)

  -- Build sort instantiation info
  let sortInstInfo ← (mod.sortParams.zip sortArgs).mapM fun ((sp, _), cardExpr) => do
    let typeStr ← Meta.ppExpr cardExpr
    pure (sp.name, typeStr.pretty)

  -- Build Theory expression and type
  let theoryExpr ← buildTheoryExpr mod moduleArgs values enumAdapts `th
  let theoryType ← mkAppOptM (mod.name ++ `Theory) <| moduleArgs.map (Option.some ·)

  -- Build State type
  let fieldAbstractTypeName := mod.name ++ fieldAbstractDispatcherName
  let dispatcher ← mkAppM fieldAbstractTypeName moduleArgs
  let stateType ← mkAppM (mod.name ++ `State) #[dispatcher]

  -- Build State expressions for each state
  let stateExprs ← (Array.range numStates).mapM fun i =>
    buildStateExpr mod moduleArgs values enumAdapts (traceStateName i)

  -- Build Label type
  let labelType ← mkAppM (mod.name ++ `Label) moduleArgs

  -- Build Label expressions for each transition
  let defaultLabel := mkAppOptM ``default #[some labelType, none]
  let mut actionsByTag : Std.HashMap Nat (Nat × Name) := {}
  for (act, idx) in mod.actions.zipIdx do
    let some value := values[actionTagEnumInstName ++ act.name]? | continue
    let some tag ← extractFinValue model.ctx value | continue
    actionsByTag := actionsByTag.insert tag (idx, act.name)
  let labelExprs ← (Array.range numTransitions).mapM fun i => do
    let step := i + 1
    let some tagExpr := values[traceTagName step]? | defaultLabel
    let some tag ← extractFinValue model.ctx tagExpr | defaultLabel
    let some (idx, actionName) := actionsByTag[tag]? | defaultLabel
    let some label ← buildLabelExpr mod moduleArgs actionName values enumAdapts
        (traceArgumentName step idx) | defaultLabel
    return label

  return {
    ctx := model.ctx
    sortInstInfo, sortSubst, enumAdapts
    extraSorts
    theoryExpr, theoryType
    stateType, stateExprs
    labelType, labelExprs
    extraVals
  }

/-! ## JSON Serialization -/

/-- Convert a VeilTrace to JSON matching the `Trace.toJsonWithPicks` format:
    ```json
    {
      "theory": {...},
      "states": [
        {"index": 0, "fields": {...}, "transition": "after_init"},
        {"index": 1, "fields": {...}, "transition": <label>},
        ...
      ]
    }
    ```
    `encode` gives the JSON of each value: `evalExprToDisplay` (the default) shows it to people,
    `evalExprToJson` serializes it for programs that read it back.
-/
unsafe def VeilTrace.toJson (vt : VeilTrace)
    (encode : Expr → Expr → MetaM Json := evalExprToDisplay) : MetaM Json := do
  -- Build theory JSON
  let theoryJson ← encode vt.theoryType vt.theoryExpr

  -- Build states array
  let mut statesArr : Array Json := #[]

  -- First state (initial, after_init)
  if h : 0 < vt.stateExprs.size then
    let stateJson ← encode vt.stateType vt.stateExprs[0]
    statesArr := statesArr.push <| Json.mkObj [
      ("index", Json.num 0),
      ("fields", stateJson),
      ("transition", Json.str "after_init")
    ]

  -- Subsequent states with their transition labels
  for i in [1:vt.stateExprs.size] do
    if hi : i < vt.stateExprs.size then
      let stateJson ← encode vt.stateType vt.stateExprs[i]
      let labelIdx := i - 1
      let labelJson ← if hl : labelIdx < vt.labelExprs.size then
        encode vt.labelType vt.labelExprs[labelIdx]
      else
        pure (Json.str "unknown")
      statesArr := statesArr.push <| Json.mkObj [
        ("index", Json.num i),
        ("fields", stateJson),
        ("transition", labelJson)
      ]

  -- Build instantiation JSON
  let instJson := Json.mkObj <| vt.sortInstInfo.toList.map fun (name, typeStr) =>
    (name.toString, Json.str typeStr)

  -- Build extra sorts JSON
  let extraSortsJson := Json.mkObj <| ← vt.extraSorts.toList.mapM fun (sortExpr, cardExpr) => do
    let ectx := vt.ctx.toExprWithCtx sortExpr
    ectx.runMetaM fun sortExpr => do
      let nameStr := (← Meta.ppExpr sortExpr).pretty
      let typeStr := (← Meta.ppExpr cardExpr).pretty
      return (nameStr, Json.str typeStr)

  -- Build extraVals JSON: substitute abstract sorts with concrete types and Prop with Bool
  let sortFVars := vt.sortSubst.map (·.1)
  let sortTypes := vt.sortSubst.map (·.2)
  let extraValsJson := Json.mkObj <| ← vt.extraVals.toList.mapM fun (nameExpr, valueExpr) => do
    (vt.ctx.toExprWithCtx nameExpr).runMetaM fun nameExpr => do
      let nameStr ← modelValueDisplayName nameExpr
      let concreteType := ((← Meta.inferType nameExpr).replaceFVars sortFVars sortTypes).replace
        fun e => if e.isProp then some (mkConst ``Bool) else none
      let adapted ← adaptSmtExprType valueExpr concreteType vt.enumAdapts
      return (nameStr, ← encode (← Meta.inferType adapted) adapted)

  return Json.mkObj [
    ("instantiation", instJson),
    ("theory", theoryJson),
    ("states", Json.arr statesArr),
    ("extraSorts", extraSortsJson),
    ("extraVals", extraValsJson)
  ]

/-- Convert VeilTrace to a ModelCheckingResult-like JSON format for TraceDisplayViewer.
    - For `sat trace` (isExpectedSat = true): returns `result: "no_violation_found"` with the trace
    - For `unsat trace` (isExpectedSat = false): returns `result: "found_violation"` with safety_failure -/
unsafe def VeilTrace.toModelCheckingResultJson (vt : VeilTrace) (isExpectedSat : Bool) : MetaM Json := do
  let traceJson ← vt.toJson

  -- Extract the trace portion
  let traceOnly := Json.mkObj [
    ("instantiation", traceJson.getObjValD "instantiation"),
    ("theory", traceJson.getObjValD "theory"),
    ("states", traceJson.getObjValD "states"),
    ("extraVals", traceJson.getObjValD "extraVals")
  ]

  -- Different JSON structure for sat trace vs unsat trace counterexample
  if isExpectedSat then
    -- sat trace: found a satisfying trace (success case)
    return Json.mkObj [
      ("result", Json.str "no_violation_found"),
      ("trace", traceOnly)
    ]
  else
    -- unsat trace: found a counterexample (violation)
    return Json.mkObj [
      ("result", Json.str "found_violation"),
      ("violation", Json.mkObj [
        ("kind", Json.str "safety_failure"),
        ("violates", Json.arr #[])
      ]),
      ("trace", traceOnly)
    ]

end Veil
