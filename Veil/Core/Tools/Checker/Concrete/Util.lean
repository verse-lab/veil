import ProofWidgets.Component.GraphDisplay
import ProofWidgets.Component.HtmlDisplay
import Veil.Core.Tools.Checker.Concrete.DataStructure
import Lean

open Lean Elab Command Tactic Meta Term
open ProofWidgets Jsx

/- Collect the trace from the model checker. -/
def collectTrace [BEq β] [Repr β] [Hashable β] [Repr κ] (res : SearchContext α β κ)
: Array GraphDisplay.Vertex × Array GraphDisplay.Edge := Id.run do
  -- The bad states found by the model checker.
  let unsafeV := res.counterexample
  -- All the logs from the model checker.
  let edges := res.log
  let mut next_round := true
  -- goal is the list of states that need to be explored
  let mut goal := unsafeV.toArray
  -- T is the list of edges in the trace
  let mut T : Array (β × β × κ) := #[]
  -- seen is the list of states that have been seen, i.e., vertices in the trace.
  let mut seen : Array β := #[]

  -- Backward search to construct the counterexample trace
  while next_round do
    let l := edges.filter (fun (_, target, _) => goal.contains target)
    seen := seen ++ goal.filter (fun x => !seen.contains x)
    T := T ++ l.toArray
    let new_sources := l.map (fun (source, _, _) => source)
    let new_goal := new_sources.filter (fun x => !seen.contains x)
    goal := new_goal.toArray
    if goal.isEmpty then
      next_round := false

  let targets := T.map (fun (_, target, _) => target)
  let startStates := seen.filter (fun s => !targets.contains s)

  let vertices := seen.map (fun state =>
    let stateStr := s!"{repr state}"
    let isCounterExample := unsafeV.contains state
    let isStart := startStates.contains state
    { id := stateStr,
      label := if isCounterExample then
        -- counterexample node (red)
        <circle r={6} fill="#ff4444" stroke="#cc0000" strokeWidth={1} />
      else if isStart then
        -- start node (green)
        <circle r={6} fill="#44cc44" stroke="#008800" strokeWidth={1} />
      else
        -- normal node (default style)
        GraphDisplay.mkCircle,
      details? := Html.text s!"{stateStr}" : GraphDisplay.Vertex })

  let G := T.map (fun (src, tar, label) => (src, tar, s!"{repr label}")) -- convert label to string
  let graph_edges := G.map (fun (source, target, label) =>
    let simplifiedLabel :=
      -- Extract event name from labels like "Peterson.Label.evtA1 (Peterson.process.P1)"
      if (label.splitOn "Label.").length > 1 then
        let afterLabel := label.splitOn "Label."
        if afterLabel.length > 1 then
          let eventPart := afterLabel[1]!
          let eventName := eventPart.splitOn " " |>.head!
          eventName
        else
          let parts := label.split (· == '.')
          parts.getLast?.getD label
      else
        let parts := label.split (· == '.')
        parts.getLast?.getD label
    { source := s!"{repr source}", target := s!"{repr target}",
      label? := <foreignObject height={100} width={80}>
        <MarkdownDisplay contents={s!"{simplifiedLabel}"} />
      </foreignObject>,
      details? := Html.text label : GraphDisplay.Edge })

  return (vertices, graph_edges)


/- Collect the trace from the model checker. -/
def collectTrace' [BEq β] [Repr β] [Hashable β] [Repr κ] (res : SearchContext α β κ)
: List κ := Id.run do
  -- The bad states found by the model checker.
  let unsafeV := res.counterexample
  -- All the logs from the model checker.
  let edges := res.log
  let mut next_round := true
  -- goal is the list of states that need to be explored
  let mut goal := unsafeV
  -- T is the list of edges in the trace
  let mut T : List (β × β × κ) := []
  -- seen is the list of states that have been seen, i.e., vertices in the trace.
  let mut seen : List β := []

  -- Backward search to construct the counterexample trace
  while next_round do
    let l := edges.filter (fun (_, target, _) => goal.contains target)
    seen := seen ++ goal.filter (fun x => !seen.contains x)
    T := l ++ T
    let new_sources := l.map (fun (source, _, _) => source)
    let new_goal := new_sources.filter (fun x => !seen.contains x)
    goal := new_goal
    if goal.isEmpty then
      next_round := false

  return T.map (fun (_, _, act) => act)


/-- Create the expanded graph display. -/
def createExpandedGraphDisplay (vertices : Array GraphDisplay.Vertex) (edges : Array GraphDisplay.Edge) : Html :=
  <GraphDisplay
    vertices={vertices}
    edges={edges}
    forces={#[
      .link { distance? := some 60, strength? := some 0.2 },     -- Add link distance, reduce strength
      .manyBody { strength? := some (-50) },                     -- Add strong repulsion, prevent nodes from clustering
      .center { x? := some 0, y? := some 0, strength? := some 0.1 }, -- Add weak center force
      .collide { radius? := some 20, strength? := some 1.0 }      -- Prevent nodes from overlapping
    ]}
    showDetails={true}
  />


/- Below are functions for implementing an external frontend to display the model checker results. -/

def genConcreteStateStx : CommandElabM (TSyntax `command) := do
  let env ← getEnv
  let currentNS ← getCurrNamespace
  let stateNames := [currentNS ++ `State, `State]
  let mut sInfo : Option StructureInfo := none
  for stateName in stateNames do
    if env.contains stateName then
      if let some structInfo := getStructureInfo? env stateName then
        sInfo := some structInfo
        trace[veil.debug] "Found State structure: {stateName}"
        break
  let some structInfo := sInfo | throwError "Could not find State structure in any namespace"
  let some cst := env.find? structInfo.structName
    | throwError "Internal error: structure constant {structInfo.structName} not found"
  unless cst.isInductive do
    throwError "{structInfo.structName} is not an inductive/structure"
  let iinfo := cst.inductiveVal!
  let numParams := iinfo.numParams
  let ctorName := iinfo.ctors[0]? |>.getD (structInfo.structName ++ `mk)
  let some ctorCst := env.find? ctorName
    | throwError "Constructor {ctorName} not found for structure {structInfo.structName}"
  let .ctorInfo ctorInfo := ctorCst
    | throwError "Expected ctor info for {ctorName}"

  /- Open only the parameter binders to read their names and types -/
  let binders ← liftTermElabM do
    let paramNames := extractParamNames ctorInfo.type numParams

    forallBoundedTelescope ctorInfo.type numParams fun params _ => do
      let binderPairs ← params.zipIdx.mapM fun (param, idx) => do
        let ty ← inferType param
        let realParamName := paramNames[idx]!
        let paramIdent := mkIdent realParamName
        let tySyntax ← PrettyPrinter.delab ty
        trace[veil.debug] s!"Real param name: {realParamName}, paramIdent: {paramIdent}"
        trace[veil.info] s!"struct param {idx}: {← ppExpr param} : {← ppExpr ty}"

        let binder ← `(bracketedBinder| ($paramIdent : $tySyntax))
        /- `[Ord α]` instance should be provided, as we use `TreeSet`. -/
        let instOrd ← `(bracketedBinder| [Ord $paramIdent])
        pure #[binder]
      pure binderPairs.flatten

  /- Collect and generate a new structure with the same fields. -/
  let fields ← liftTermElabM do
    -- a) Generate field comparison - generate adaptive comparison code for each field
    let mut allFields : Array (TSyntax `Lean.Parser.Command.structSimpleBinder) := #[]
    for fieldName in structInfo.fieldNames do
      let fieldIdent := mkIdent fieldName
      trace[veil.debug] "Processing field: {fieldName}"
      trace[veil.debug] "fieldIdent: {fieldIdent}"
      let projName? : Option Name :=
        if env.contains fieldName then some fieldName
        else
          let candidate := structInfo.structName ++ fieldName
          if env.contains candidate then some candidate else none
      let some projName := projName?
        | throwError "Could not resolve projection constant for field {fieldName} in structure {structInfo.structName}"

      /- e.g., `projName := `Bakery.State.unchecked` -/
      trace[veil.debug] s!"Resolved projection name: {projName}"
      let some cinfo := env.find? projName
        | throwError "Internal error: constant info for {projName} not found"
      let pinfo? ← Lean.getProjectionFnInfo? projName
      let some pinfo := pinfo?
        | throwError "Failed to get projection metadata for {projName}"
      let numToOpen := pinfo.numParams + 1 -- structure parameters + self

      let structField ← Meta.forallBoundedTelescope cinfo.type numToOpen fun _ resultTy => do
        /- e.g., `resultTy := `State.unchecked : process → process → Bool` -/
        trace[veil.debug] s!"Type of field {fieldName}: {← ppExpr resultTy}"

        /- body is the return type -/
        let newFieldType ← Meta.forallTelescope resultTy fun xs body => do
          let isBool ← Meta.isDefEq body (Lean.mkConst `Bool)
          if isBool then trace[veil.debug] s!"This is a `relation` definition."

          for x in xs do
            let xTy ← inferType x
            trace[veil.debug] s!"Arg: {x}, type: {← ppExpr xTy}"
          trace[veil.debug] s!"Body after opening all args: {← ppExpr body}"

          let mut tupleType : Expr := panic! "tupleType not initialized"
          let mut cmpLam : Expr := panic! "cmpLam not initialized" -- Explict `cmp`
          if xs.size ≤ 1 then
            /- Now, xs.size = 0, i.e., `xs[0]!` is not allowed, while `body` conveys the type of the field.-/
            tupleType := body
            trace[veil.debug] s!"tupleType: {← ppExpr tupleType}"
            -- let mut cmpLam  ← mkLambdaFVars xs
          else
            /- Multiple params: `T₁ → T₂ → ... → Bool` ≈> `Std.TreeSet (T₁ × T₂ × ...)` -/
            tupleType ← inferType xs[0]!
            for i in [1:xs.size] do
              let argTy ← inferType xs[i]!
              tupleType ← mkAppM ``Prod #[tupleType, argTy]
            /- If the return type is not `Bool`, we need to add it to the tuple type. -/
            if !body.isConstOf `Bool then
              tupleType ← mkAppM ``Prod #[tupleType, body]
          /- [TODO]: use Std.TreeSet instead of List -/
          let treeSetExpr ← mkAppM ``List #[tupleType]
          pure treeSetExpr

        trace[veil.debug] s!"New field type for {fieldName}: {← ppExpr newFieldType}"
        let fieldTypeStx ← PrettyPrinter.delab newFieldType
        let structField ← `(Lean.Parser.Command.structSimpleBinder| $fieldIdent:ident : $fieldTypeStx)
        pure structField
      allFields := allFields.push structField
    pure allFields

  let structStx ← `(structure $(mkIdent `NewState) $binders* where
      $(mkIdent `mk):ident :: $[$fields]*
      deriving $(mkIdent ``Inhabited), $(mkIdent ``Nonempty))
  pure structStx
where
  /- Extract parameter names from the original type -/
  extractParamNames (ty : Expr) (count : Nat) : List Name :=
    if count = 0 then []
    else
      match ty with
      | Expr.forallE name _ body _ => name :: extractParamNames body (count - 1)
      | _ => []

elab "#createConcreteStateStructure" : command => do
  let structStx ← genConcreteStateStx
  trace[veil.debug] s!"Generated structure command: {structStx}"
  elabCommand structStx



/- Adapted from `Util.Display.lean`, `simple_deriving_repr_for` -/
open Lean Meta Elab Term Command in
elab "simple_deriving_hashable_for " t:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  let instanceCmd ← Command.runTermElabM fun _ => do
    `(instance [Repr $t]: Hashable $t where
        hash s := hash (toString (reprStr s)))
  elabCommand instanceCmd
