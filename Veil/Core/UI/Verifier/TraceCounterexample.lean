import Lean
import Smt
import ProofWidgets.Compat
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Names
import Veil.Frontend.DSL.Module.Util.Basic
import Veil.Frontend.DSL.Module.Util.StateTheory
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Core.UI.Verifier.Model
import Veil.Core.UI.Verifier.InductionCounterexample
import Veil.Backend.SMT.Model

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
- Params (any action): `_tr{trIdx}_act{actIdx}_arg{argIdx}_{paramName}`
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
  /-- Sort substitution: maps sort parameter fvars to their concrete types. -/
  sortSubst : Array (Expr × Expr) := #[]

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

/-! ## Name Pattern Matchers -/

/-- Parse a natural number from a string, returning none if it's not a valid number. -/
private def parseNat? (s : String) : Option Nat :=
  s.toNat?

/-- Check if a name matches the pattern "st{n}.fieldName" and return (n, fieldName).
    For example: `st0.leader` → `some (0, leader)`, `st3.msgs` → `some (3, msgs)` -/
def isIndexedStateField (name : Name) : Option (Nat × Name) :=
  match name with
  | .str (.str .anonymous stN) fieldName =>
    if stN.startsWith "st" then
      match parseNat? (stN.drop 2) with
      | some n => some (n, .mkSimple fieldName)
      | none => none
    else none
  | _ => none

/-- Check if a name matches the pattern "_tr{n}_tag" and return n.
    For example: `_tr1_tag` → `some 1`, `_tr3_tag` → `some 3` -/
def isTransitionTag (name : Name) : Option Nat :=
  match name with
  | .str .anonymous s =>
    if s.startsWith "_tr" && s.endsWith "_tag" then
      let middle := (s.drop 3).dropRight 4  -- Remove "_tr" prefix and "_tag" suffix
      parseNat? middle
    else none
  | _ => none

/-- Parse "{m}_{param}" into (argIdx, paramName). -/
private def parseArgParam (s : String) : Option (Nat × Name) := do
  let parts := s.splitOn "_"
  guard (parts.length ≥ 2)
  let argIdx ← parseNat? parts.head!
  let paramName := "_".intercalate parts.tail!
  return (argIdx, .mkSimple paramName)

/-- Check if a name matches the pattern "_tr{n}_arg{m}_{param}" and return (trIdx, argIdx, paramName).
    For example: `_tr1_arg0_sender` → `some (1, 0, sender)` -/
def isSpecificActionParam (name : Name) : Option (Nat × Nat × Name) := do
  let .str .anonymous s := name | none
  let afterTr ← (s.dropPrefix? "_tr").map (·.toString)
  let [trIdxStr, rest] := afterTr.splitOn "_arg" | none
  let trIdx ← parseNat? trIdxStr
  let (argIdx, paramName) ← parseArgParam rest
  return (trIdx, argIdx, paramName)

/-- Check if a name matches the pattern "_tr{n}_act{a}_arg{m}_{param}" and return (trIdx, actIdx, argIdx, paramName).
    For example: `_tr1_act0_arg0_sender` → `some (1, 0, 0, sender)` -/
def isAnyActionParam (name : Name) : Option (Nat × Nat × Nat × Name) := do
  let .str .anonymous s := name | none
  let afterTr ← (s.dropPrefix? "_tr").map (·.toString)
  let [trIdxStr, rest] := afterTr.splitOn "_act" | none
  let trIdx ← parseNat? trIdxStr
  let [actIdxStr, argRest] := rest.splitOn "_arg" | none
  let actIdx ← parseNat? actIdxStr
  let (argIdx, paramName) ← parseArgParam argRest
  return (trIdx, actIdx, argIdx, paramName)

/-- Check if a name matches the pattern `actionTagEnumInstName.actionName` and return actionName.
    For example: `__veil_tag.send` → `some send` -/
def isVeilTagEntry (name : Name) : Option Name :=
  match name with
  | .str parent actionName =>
    if parent == Veil.actionTagEnumInstName then some (.mkSimple actionName) else none
  | _ => none

/-- Extract a Nat value from a Fin expression.
    Handles `OfNat.ofNat α n inst` and `Fin.mk bound val proof` forms. -/
def extractFinValue (ctx : ModelContext) (e : Expr) : IO (Option Nat) :=
  ctx.toExprWithCtx e |>.runMetaM fun e => do
    let e ← Meta.whnf e
    -- Check if it's a Nat literal directly
    if let .lit (.natVal n) := e then
      return some n
    let args := e.getAppArgs
    -- Check if it's OfNat.ofNat α n inst - value is at index 1
    if e.isAppOf ``OfNat.ofNat && args.size >= 2 then
      let valArg ← Meta.whnf args[1]!
      if let .lit (.natVal n) := valArg then
        return some n
    -- Check if it's Fin.mk bound val proof - value is at index 1
    if e.isAppOf ``Fin.mk && args.size >= 2 then
      let valArg ← Meta.whnf args[1]!
      if let .lit (.natVal n) := valArg then
        return some n
    return none

/-! ## Model Classification -/

/-- Classify model values into indexed state fields, theory fields, transition tags,
    action parameters, and extras.

    Returns:
    - `stateFields`: Array of hashmaps, one per state index, mapping field names to values
    - `theoryFields`: HashMap of theory field names to values
    - `transitionTags`: HashMap of transition index to tag value expression
    - `specificActionParams`: HashMap of (trIdx, argIdx) to parameter value expression
    - `anyActionParams`: HashMap of (trIdx, actIdx, argIdx) to parameter value expression
    - `tagToAction`: HashMap of tag value (Nat) to action name
    - `extraVals`: Array of unclassified (name, value) pairs
-/
def classifyTraceModelValues (model : Model) (mod : Module) (numStates : Nat)
    : IO (Array (Std.HashMap Name Expr)
        × Std.HashMap Name Expr
        × Std.HashMap Nat Expr
        × Std.HashMap (Nat × Nat) Expr
        × Std.HashMap (Nat × Nat × Nat) Expr
        × Std.HashMap Nat Name
        × Array (Expr × Expr)) := do
  let stateFieldNames := mod.mutableComponents.map (·.name) |>.toList
  let theoryFieldNames := mod.immutableComponents.map (·.name) |>.toList

  -- Initialize state field maps (one per state)
  let mut stateFields : Array (Std.HashMap Name Expr) := Array.replicate numStates {}
  let mut theoryFields : Std.HashMap Name Expr := {}
  let mut transitionTags : Std.HashMap Nat Expr := {}
  let mut specificActionParams : Std.HashMap (Nat × Nat) Expr := {}
  let mut anyActionParams : Std.HashMap (Nat × Nat × Nat) Expr := {}
  let mut tagToAction : Std.HashMap Nat Name := {}
  let mut extraVals : Array (Expr × Expr) := #[]

  for (nameExpr, valueExpr) in model.values do
    let name? ← getExprName model.ctx nameExpr
    match name? with
    | some name =>
      -- Check if it's a veil tag entry (__veil_tag.actionName = tagValue)
      if let some actionName := isVeilTagEntry name then
        if let some tagValue ← extractFinValue model.ctx valueExpr then
          tagToAction := tagToAction.insert tagValue actionName
      -- Check if it's an indexed state field (st{n}.fieldName)
      else if let some (stateIdx, fieldName) := isIndexedStateField name then
        if stateIdx < numStates && stateFieldNames.contains fieldName then
          stateFields := stateFields.modify stateIdx (·.insert fieldName valueExpr)
        else
          extraVals := extraVals.push (nameExpr, valueExpr)
      -- Check if it's a theory field (th.fieldName)
      else if let some fieldName := isTheoryField name then
        if theoryFieldNames.contains fieldName then
          theoryFields := theoryFields.insert fieldName valueExpr
        else
          extraVals := extraVals.push (nameExpr, valueExpr)
      -- Check if it's a transition tag (_tr{n}_tag)
      else if let some trIdx := isTransitionTag name then
        transitionTags := transitionTags.insert trIdx valueExpr
      -- Check if it's a specific action parameter (_tr{n}_arg{m}_{param})
      else if let some (trIdx, argIdx, _paramName) := isSpecificActionParam name then
        specificActionParams := specificActionParams.insert (trIdx, argIdx) valueExpr
      -- Check if it's an any-action parameter (_tr{n}_act{a}_arg{m}_{param})
      else if let some (trIdx, actIdx, argIdx, _paramName) := isAnyActionParam name then
        anyActionParams := anyActionParams.insert (trIdx, actIdx, argIdx) valueExpr
      else
        extraVals := extraVals.push (nameExpr, valueExpr)
    | none =>
      extraVals := extraVals.push (nameExpr, valueExpr)

  return (stateFields, theoryFields, transitionTags, specificActionParams, anyActionParams, tagToAction, extraVals)

/-! ## Label Construction -/

/-- Resolve the action name from a tag expression using the tag-to-action mapping.
    The tag is a Fin value, and we use the mapping built from `__veil_tag.*` entries.
    Returns (actionName, tagValue) if resolved, or none otherwise. -/
def resolveActionFromTag (ctx : ModelContext) (tagExpr : Expr)
    (tagToAction : Std.HashMap Nat Name) : IO (Option (Name × Nat)) := do
  let some tagValue ← extractFinValue ctx tagExpr | return none
  let some actionName := tagToAction[tagValue]? | return none
  return some (actionName, tagValue)

/-- Build a Label constructor expression from action name and parameter values.
    Uses the transition index and tag value to look up parameters.
    First tries specific params (trIdx, argIdx), then any-action params (trIdx, tagValue, argIdx). -/
def buildLabelFromAction (mod : Module) (sortArgs : Array Expr)
    (actionName : Name) (trIdx : Nat) (tagValue : Nat)
    (specificParams : Std.HashMap (Nat × Nat) Expr)
    (anyActionParams : Std.HashMap (Nat × Nat × Nat) Expr)
    : MetaM (Option Expr) :=
  buildLabelExprCore mod sortArgs actionName fun idx =>
    -- First try specific params, then fall back to any-action params
    specificParams[(trIdx, idx)]? <|> anyActionParams[(trIdx, tagValue, idx)]?

/-! ## Main Construction -/

/-- Build a VeilTrace from an SMT Model.
    `numTransitions` is the number of transitions in the trace (states = numTransitions + 1). -/
def buildTraceFromModel (model : Model) (mod : Module) (numTransitions : Nat)
    : MetaM VeilTrace := do
  let numStates := numTransitions + 1

  -- Parse sorts from model
  let sortMap ← parseSortsFromModel model

  -- Build sort substitution map
  let moduleSortNames := mod.sortParams.map (·.1.name) |>.toList
  let sortSubst ← model.sorts.filterM fun (sortExpr, _) => do
    return (← getExprName model.ctx sortExpr).any moduleSortNames.contains

  -- Separate extra sorts
  let extraSorts ← model.sorts.filterM fun (sortExpr, _) => do
    return !(← getExprName model.ctx sortExpr).any moduleSortNames.contains

  -- Get sort arguments in module order
  let sortArgs ← getSortArgs mod sortMap

  -- Classify model values
  let (stateFieldMaps, theoryFields, transitionTags, specificParams, anyActionParams, tagToAction, extraVals) ←
    classifyTraceModelValues model mod numStates

  -- Build sort instantiation info
  let sortInstInfo ← (mod.sortParams.zip sortArgs).mapM fun ((param, _), cardExpr) => do
    let typeStr ← Meta.ppExpr cardExpr
    pure (param.name, typeStr.pretty)

  -- Build Theory expression and type
  let theoryExpr ← buildTheoryExpr mod sortArgs theoryFields
  let theoryType ← mkAppOptM (mod.name ++ `Theory) <| sortArgs.map (Option.some ·)

  -- Build State type
  let fieldAbstractTypeName := mod.name ++ fieldAbstractDispatcherName
  let dispatcher ← mkAppM fieldAbstractTypeName sortArgs
  let stateType ← mkAppM (mod.name ++ `State) #[dispatcher]

  -- Build State expressions for each state
  let stateExprs ← stateFieldMaps.mapM fun fieldMap => do
    buildStateExpr mod sortArgs fieldMap

  -- Build Label type
  let labelType ← mkAppM (mod.name ++ `Label) sortArgs

  -- Build Label expressions for each transition
  let defaultLabel := mkAppOptM ``default #[some labelType, none]
  let labelExprs ← (Array.range numTransitions).mapM fun i => do
    let trIdx := i + 1  -- Tags are 1-indexed (_tr1_tag, _tr2_tag, ...)
    let some tagExpr := transitionTags[trIdx]? | defaultLabel
    let some (actionName, tagValue) ← resolveActionFromTag model.ctx tagExpr tagToAction | defaultLabel
    let some labelExpr ← buildLabelFromAction mod sortArgs actionName trIdx tagValue specificParams anyActionParams | defaultLabel
    pure labelExpr

  return {
    ctx := model.ctx
    sortInstInfo, sortSubst
    extraSorts
    theoryExpr, theoryType
    stateType, stateExprs
    labelType, labelExprs
    extraVals
  }

/-! ## JSON Serialization -/

/-- Convert a VeilTrace to JSON matching the Trace.toJson format:
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
-/
unsafe def VeilTrace.toJson (vt : VeilTrace) : MetaM Json := do
  -- Build theory JSON
  let theoryJson ← evalExprToJson vt.theoryType vt.theoryExpr

  -- Build states array
  let mut statesArr : Array Json := #[]

  -- First state (initial, after_init)
  if h : 0 < vt.stateExprs.size then
    let stateJson ← evalExprToJson vt.stateType vt.stateExprs[0]
    statesArr := statesArr.push <| Json.mkObj [
      ("index", Json.num 0),
      ("fields", stateJson),
      ("transition", Json.str "after_init")
    ]

  -- Subsequent states with their transition labels
  for i in [1:vt.stateExprs.size] do
    if hi : i < vt.stateExprs.size then
      let stateJson ← evalExprToJson vt.stateType vt.stateExprs[i]
      let labelIdx := i - 1
      let labelJson ← if hl : labelIdx < vt.labelExprs.size then
        evalExprToJson vt.labelType vt.labelExprs[labelIdx]
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
      let nameStr := (← Meta.ppExpr nameExpr).pretty
      let concreteType := ((← Meta.inferType nameExpr).replaceFVars sortFVars sortTypes).replace
        fun e => if e.isProp then some (mkConst ``Bool) else none
      let adapted ← adaptSmtExprType valueExpr concreteType
      return (nameStr, ← evalExprToJson (← Meta.inferType adapted) adapted)

  return Json.mkObj [
    ("instantiation", instJson),
    ("theory", theoryJson),
    ("states", Json.arr statesArr),
    ("extraSorts", extraSortsJson),
    ("extraVals", extraValsJson)
  ]

/-- Convert VeilTrace to a ModelCheckingResult-like JSON format for TraceDisplayViewer.
    - For `sat trace` (isExpectedSat = true): returns `result: "found_trace"` with the trace
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
