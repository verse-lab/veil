import Lean
import Veil.Base
import Veil.Tactic.Main
import Veil.DSL.Internals.Attributes
import Veil.DSL.Internals.StateExtensions
import Veil.Util.DSL
import Veil.Util.Display
import Veil.Util.SMT
import Veil.DSL.Specification.SpecDef

open Lean Elab Command Term Meta Lean.Parser Tactic.TryThis Lean.Core

inductive CheckStyle
  /-- Do not check any theorems. Used to only print suggestions. -/
  | noCheck
  /-- Check all theorems in one big check with indicator variables. -/
  | checkTheoremsWithIndicators
  /-- Check theorems individually. -/
  | checkTheoremsIndividually

inductive TheoremSuggestionStyle
  /-- Do not offer suggestions -/
  | doNotPrint
  /-- Suggest theorem statements for all theorems. -/
  | printAllTheorems
  /-- Suggests only theorems that were not proved automatically. -/
  | printUnverifiedTheorems

inductive ProofKind
  | checkedByLean
  | trustingSolver

instance : ToString ProofKind where
  toString kind := match kind with
    | .checkedByLean => ""
    | .trustingSolver => " (trusting solver)"

instance : ToJson ProofKind where
  toJson kind := match kind with
    | .checkedByLean => "checkedByLean"
    | .trustingSolver => "trustingSolver"

instance : FromJson ProofKind where
  fromJson? s := match s with
    | "checkedByLean" => .ok .checkedByLean
    | "trustingSolver" => .ok .trustingSolver
    | _ => .error s!"unknown proof kind: {s}"

inductive ProofResult
  | proven (kind : ProofKind)
  | notProven
deriving Inhabited

instance : ToJson ProofResult where
  toJson res := match res with
    | .proven kind => Json.arr #["proven", toJson kind]
    | .notProven => "not proven"

instance : FromJson ProofResult where
  fromJson? s := match s with
    | Json.arr #["proven", kind] => fromJson? kind >>= fun kind => .ok (.proven kind)
    | Json.str "not proven" => .ok .notProven
    | _ => .error s!"unknown proof result: {s}"

structure CheckTheoremResult where
  theoremId : TheoremIdentifier
  proofResult : ProofResult
  smtResult : SmtResult
  timeInMs : Nat
  modelStr : Option String
deriving Inhabited, ToJson, FromJson

abbrev CheckTheoremResultStringMarker := "[VEIL_CHECK_RESULT]\n"

instance : ToString ProofResult where
  toString res := match res with
    | .proven kind => s!"proven{kind}"
    | .notProven => "not proven"

def ProofResult.isProven (res : ProofResult) : Bool := match res with
  | .proven _ => true
  | .notProven => false

def ProofResult.isAdmitted (res : ProofResult) : Bool := match res with
  | .proven (.trustingSolver) => true
  | _ => false

def CheckInvariantsBehaviour := VCGenStyle × CheckStyle × TheoremSuggestionStyle
def CheckInvariantsBehaviour.default [Monad m] [MonadOptions m] : m CheckInvariantsBehaviour := do
  let vcGen := veil.vc_gen.get (← getOptions)
  return (vcGen, .checkTheoremsIndividually, .doNotPrint)

def CheckInvariantsBehaviour.question [Monad m] [MonadOptions m] : m CheckInvariantsBehaviour := do
  let vcGen := veil.vc_gen.get (← getOptions)
  return (vcGen, .noCheck, .printAllTheorems)

def CheckInvariantsBehaviour.exclamation [Monad m] [MonadOptions m] : m CheckInvariantsBehaviour := do
  let vcGen := veil.vc_gen.get (← getOptions)
  return (vcGen, .checkTheoremsIndividually, .printUnverifiedTheorems)

/--  Generate theorems to check in the initial state and after each action -/
def getAllChecks (isolates : NameHashSet := ∅) : CommandElabM (Array (Name × Expr) × Array ((Name × Expr) × (Name × Expr))) := Command.runTermElabM fun _ => do
    let mut invs := (← localSpecCtx.get).spec.invariants
    unless isolates.isEmpty do
      invs := invs.filter fun inv => isolates.any inv.isolates.contains
    let invNames := invs.map StateAssertion.name
    let actNames := ((<- localSpecCtx.get).spec.actions).map (fun s => s.name)
    let invNamesInds := invNames.map (fun name => (name, Lean.mkConst $ Name.mkSimple s!"invInd_{mkPrintableName name}"))
    let actNamesInds := actNames.map (fun name => (name, Lean.mkConst $ Name.mkSimple s!"actInd_{mkPrintableName name}"))
    let mut actChecks := #[]
    for inv in invNamesInds do
       for act in actNamesInds do
         actChecks := actChecks.push (inv, act)
    return (invNamesInds, actChecks)

/-- Generate theorems to check the given invariant clause in the initial
state and after each action. -/
def getChecksForInvariant (invName : Name) : CommandElabM (Array (Name × Expr) × Array ((Name × Expr) × (Name × Expr))) := Command.runTermElabM fun _ => do
    let actNames := ((<- localSpecCtx.get).spec.actions).map (fun s => s.name)
    let invNamesInd := (invName, Lean.mkConst $ Name.mkSimple s!"invInd_{mkPrintableName invName}")
    let actNamesInds := actNames.map (fun name => (name, Lean.mkConst $ Name.mkSimple s!"actInd_{mkPrintableName name}"))
    let mut actChecks := #[]
    for act in actNamesInds do
        actChecks := actChecks.push (invNamesInd, act)
    return (#[invNamesInd], actChecks)

/-- Generate therems to check all invariants after the given action. -/
def getChecksForAction (actName : Name) : CommandElabM (Array (Name × Expr) × Array ((Name × Expr) × (Name × Expr))) := Command.runTermElabM fun _ => do
    let invNames := (← localSpecCtx.get).spec.invariants.map StateAssertion.name
    let invNamesInds := invNames.map (fun name => (name, Lean.mkConst $ Name.mkSimple s!"invInd_{mkPrintableName name}"))
    let actNamesInd := (actName, Lean.mkConst $ Name.mkSimple s!"actInd_{mkPrintableName actName}")
    let mut invChecks := #[]
    for inv in invNamesInds do
        invChecks := invChecks.push (inv, actNamesInd)
    return (#[], invChecks)

def theoremSuggestionsForChecks (initIndicators : List Name) (actIndicators : List (Name × Option Name)) (vcStyle : VCGenStyle) (sorry_body: Bool := true): CommandElabM (Array (TheoremIdentifier × TSyntax `command)) := do
    Command.runTermElabM fun vs => do
      let (systemTp, stateTp, readerTp, rd, st, st', stateSimpH) := (← getSystemTpStx vs, ← getStateTpStx, ← getReaderTpStx, mkIdent `rd, mkIdent `st, mkIdent `st', mkIdent stateSimpHypName)
      let assertionArgs ← getSectionArgumentsStx vs
      let actionArgs ← getSectionArgumentsStx vs
      let mut theorems : Array (TheoremIdentifier × TSyntax `command) := #[]
      let meetsSpec := match vcStyle with
        | .transition => mkIdent ``TwoState.meetsSpecificationIfSuccessful
        | .wp => mkIdent ``VeilM.meetsSpecificationIfSuccessful

      -- Init + Action checks
      let init := initIndicators.reverse.map (fun invName => (initializerName, some invName))
      for (actName, invName) in init ++ actIndicators.reverse do
        let moduleName ← getCurrNamespace
        let (univBinders, args) ← do
          if actName != initializerName then
            let some args := (<- localSpecCtx.get).spec.actions.find? (moduleName ++ ·.name == actName)
              | throwError s!"action {actName} not found"
            match args.br with
            | some br => pure (← toBracketedBinderArray br, ← explicitBindersIdents br)
            | none => pure (#[], #[])
          else pure (#[], #[])

        let trName := match vcStyle with
          | .transition => toTwoStateName (toExtName actName)
          | .wp => (toExtName actName)

        if let .some invName := invName then
          let trStx ← `(@$(mkIdent trName) $actionArgs* $args*)
          let preStx ← if actName != initializerName then `(fun $rd $st => $(mkIdent ``And) (($systemTp).$(mkIdent `assumptions) $rd) (($systemTp).$(mkIdent `inv) $rd $st)) else `(fun $rd $st => ($systemTp).$(mkIdent `assumptions) $rd)
          let postStx ← match vcStyle with
            | .transition => `(fun $rd $st' => @$(mkIdent invName) $assertionArgs* $rd $st')
            | .wp => `(fun _ $rd $st' => @$(mkIdent invName) $assertionArgs* $rd $st')
          let trTpSyntax ← `(forall? $univBinders*, $meetsSpec $trStx $preStx $postStx)
          let trTpSyntax : TSyntax `term ← TSyntax.mk <$> (Elab.liftMacroM <| expandMacros trTpSyntax)
          let solveClause ← match vcStyle with
            | .transition => `(tacticSeq|solve_tr_clause $(mkIdent trName) $(mkIdent invName))
            | .wp => `(tacticSeq|solve_wp_clause $(mkIdent trName) $(mkIdent invName))
          let body ← if sorry_body then `(by sorry) else `(by $solveClause)
          let (tp, body) := (trTpSyntax, body)
          let thmName := match vcStyle with
            | .transition => mkTrTheoremName actName invName
            | .wp => mkTheoremName actName invName
          let thm ← `(@[invProof] theorem $(mkIdent thmName) : $tp := $body)
          theorems := theorems.push (⟨invName, if actName == initializerName then .none else actName, thmName⟩, thm)
        else -- check that the transition never throws an exception
          let (ex, True, exId) := (mkIdent `ex, mkIdent ``True, mkIdent `ExId)
          let extName := toWpExName $ toExtName actName
          let extStx ← `(@$(mkIdent extName) $actionArgs* $ex $args*)
          let extTpSyntax ←
            `(∀ ($ex : ExId) ($rd : $genericReader) ($st : $genericState), forall? $univBinders*,
              ($systemTp).$(mkIdent `assumptions) $rd → $extStx (fun _ _ _ => $True) $rd $st)
          let extTpSyntax : TSyntax `term ← TSyntax.mk <$> (Elab.liftMacroM <| expandMacros extTpSyntax)
          let body ← if sorry_body then `(by sorry) else `(by solve_wp_clause $(mkIdent extName))
          let (tp, body) := (extTpSyntax, body)
          let thmName := mkTheoremName actName `doesNotThrow
          let thm ← `(@[invProof] theorem $(mkIdent thmName) : $tp := $body)
          theorems := theorems.push (⟨.none, actName, thmName⟩, thm)

      return theorems

def theoremSuggestionsForIndicators (generateInitThms : Bool) (actIndicators invIndicators : List (Name × Expr)) (vcStyle : VCGenStyle) (sorry_body: Bool := false): CommandElabM (Array (TheoremIdentifier × TSyntax `command)) := do
  let (initIndicators, acts) ← Command.runTermElabM fun _ => do
    -- prevent code duplication
    let initIndicators ← invIndicators.mapM (fun (invName, _) => resolveGlobalConstNoOverloadCore invName)
    let actIndicators ← actIndicators.mapM (fun (actName, _) => resolveGlobalConstNoOverloadCore actName)
    let mut acts := #[]
    for actName in actIndicators do
      for invName in initIndicators do
        acts := acts.push (actName, some invName)
      /- pair `actName` with `none` corresponds to successful termination check for `actName` -/
      acts := acts.push (actName, none)
    return (initIndicators, acts)
  theoremSuggestionsForChecks (if generateInitThms then initIndicators else []) acts.toList vcStyle sorry_body

def checkIndividualTheorem (thmId : TheoremIdentifier) (cmd : TSyntax `command) : CommandElabM ProofResult := do
  let env ← getEnv
  -- If the theorem has been defined already, reuse the existing
  -- definition to figure out whether it's proven
  if (← resolveGlobalName thmId.theoremName).isEmpty then
    trace[veil.debug] "Checking theorem {thmId.theoremName} for the first time"
    elabCommand (← `(#guard_msgs(drop warning) in $(cmd)))
  else
    trace[veil.debug] "Theorem {thmId.theoremName} has been checked before; reusing result"
  -- Check the `Expr` for the given theorem
  let thFullName ← resolveGlobalConstNoOverloadCore thmId.theoremName
  let th ← getConstInfo thFullName
  let (isProven, proofKind) ← match th with
    | ConstantInfo.thmInfo attempt =>
      -- a synthetic sorry is one introduced by Lean when typechecking the proof script fails
      -- our tactics introduce a non-synthetic sorry when the solver says `unsat` and we trust the solver
      let isProven := !attempt.value.hasSyntheticSorry
      let proofKind := if attempt.value.hasSorry then ProofKind.trustingSolver else ProofKind.checkedByLean
      pure (isProven, proofKind)
    | _ => throwError s!"checkTheorem: expected {thmId.theoremName} to be a theorem"
  -- We only add the theorem to the environment if it successfully type-checks
  -- i.e. we restore the original environment if the theorem is not proven
  if !isProven then
    setEnv env
  let result := if isProven then .proven proofKind else .notProven
  return result

def Lean.MessageLog.containsSubStr (msgs : MessageLog) (substr : String) : CommandElabM Bool := do
  msgs.toList.anyM (fun msg => return String.isSubStrOf substr (← msg.data.toString))

def parseStrAsJson [Monad m] [MonadError m] (str : String) : m Json := do
  match Json.parse str with
  | .ok json => return json
  | .error err => throwError s!"could not parse {str} as Json: {err}"

def getExId (modelStrs : Array String) : Option Nat := Id.run do
  for modelStr in modelStrs do
    let modelStr := modelStr.splitOn "exId = "
    if modelStr.length >= 2 then
      let exIdStr := modelStr[1]!.takeWhile (·.isDigit)
      return exIdStr.toNat?
  return .none

def throwTerminationErrorAt (exId : ExId) (callerName : Name) : CommandElabM Unit := do
  let ctx ← assertsCtx.get
  let .some stx := ctx.map.get? exId
    | logError s!"Some assertion might fail when called from {callerName} but its exception id {exId} not found"
  logErrorAt stx s!"This assertion might fail when called from {callerName}"

def checkTheorems (stx : Syntax) (initChecks: Array (Name × Expr)) (invChecks: Array ((Name × Expr) × (Name × Expr))) (behaviour : CheckInvariantsBehaviour) :
  CommandElabM Unit := do
  liftCoreM errorOrWarnWhenSpecIsNeeded
  let actIndicators := (invChecks.map (fun (_, (act_name, ind_name)) => (act_name, ind_name))).toList.removeDuplicates
  let invIndicators := (invChecks.map (fun ((inv_name, ind_name), _) => (inv_name, ind_name))).toList.removeDuplicates
  let (vcStyle, _checkStyle, suggestionStyle) := behaviour
  let allTheorems ← theoremSuggestionsForIndicators (!initChecks.isEmpty) actIndicators invIndicators vcStyle
  match behaviour with
  | (_, .noCheck, .doNotPrint) => pure ()
  | (_, .noCheck, .printUnverifiedTheorems) => throwError "[checkTheorems] Cannot print unverified theorems without checking"
  | (_, .noCheck, .printAllTheorems) => displaySuggestion stx (allTheorems.map Prod.snd)
  | (_, .checkTheoremsIndividually, _) =>
    let processThm (theoremId : TheoremIdentifier) (cmd : TSyntax `command) : CommandElabM CheckTheoremResult := do
      -- save messages before elaboration
      let origMsgs := (<- get).messages
      let startTime := ← IO.monoMsNow
      let proofResult ← checkIndividualTheorem theoremId cmd
      let endTime := ← IO.monoMsNow
      -- messages after elaboration
      let msgs := (← get).messages
      let mut modelStr : Option String := .none
      let smtResult ← if proofResult.isProven then pure SmtResult.Unsat else
        -- The theorem is not proven; we need to figure out why:
        -- either solver returned `sat`, `unknown`, or there was an error
        let msgsTxt := String.intercalate "\n" (← msgs.toList.filterMapM (fun msg => if msg.severity == .error then msg.toString else pure none))
        let (hasSat, hasUnknown, hasFailure) := (← msgs.containsSubStr Veil.SMT.satGoalStr, ← msgs.containsSubStr Veil.SMT.unknownGoalStr, ← msgs.containsSubStr Veil.SMT.failureGoalStr)
        modelStr := if hasSat then .some $ (s!"{theoremId.theoremName}" ++ (getModelStr msgsTxt) ++ "\n") else .none
        pure $ match hasSat, hasUnknown, hasFailure with
        | true, false, false => SmtResult.Sat .none
        | false, true, false => SmtResult.Unknown msgsTxt
        | false, false, true => SmtResult.Failure msgsTxt
        | _, _, _ =>
          dbg_trace s!"[{theoremId.theoremName}] (isProveproofResultsult}, hasSat: {hasSat}, hasUnknown: {hasUnknown}, hasFailure: {hasFailure}) Unexpected messages: {msgsTxt}"
          unreachable!
      -- restore messages (similar to `#guard_msgs`)
      modify fun st => { st with messages := origMsgs }
      let checkResult := { theoremId, proofResult, smtResult, timeInMs := endTime - startTime, modelStr }
      let jsonStr := (toJson checkResult).pretty
      -- we use this to communicate results to the main thread
      if Elab.async.get (← getOptions) then
        logInfo s!"{CheckTheoremResultStringMarker}{jsonStr}"
      return checkResult

    -- Compute results for all theorems
    let results ← do
      if Elab.async.get (← getOptions) then
        -- Prepare tasks for parallel execution (but don't execute them yet)
        let cancelTk ← IO.CancelToken.new
        let tasks : Array (Unit → BaseIO Language.SnapshotTree) ← allTheorems.mapM (fun (thmId, cmd) => do
          wrapAsyncAsSnapshot (fun () => do let _ ← processThm thmId cmd) cancelTk (desc := s!"{thmId.theoremName}"))
        let tasks := Array.toList $ ← tasks.mapM (fun task => BaseIO.asTask (task ()))
        -- Execute tasks in parallel and collect results
        let allTasks ← BaseIO.mapTasks (fun snaptree => return snaptree) tasks
        let trees := allTasks.get
        let results := trees.mapM (fun tree => do
          let msgsTxt := String.intercalate "\n" (← tree.element.diagnostics.msgLog.toList.filterMapM (fun msg => do
            let msgStr ← msg.toString
            if msg.severity == .information && msgStr.startsWith CheckTheoremResultStringMarker then
              pure $ msgStr.stripPrefix CheckTheoremResultStringMarker
            else pure none))
          let json ← parseStrAsJson msgsTxt
          let mut checkResult : Option CheckTheoremResult := .none
          match fromJson? json with
          | .ok cr => checkResult := .some cr
          | .error err => throwError s!"could not parse {msgsTxt} as CheckTheoremResult: {err}"
          pure checkResult.get!
        )
        results
      else
        let results ← allTheorems.mapM (fun (thmId, cmd) => processThm thmId cmd)
        pure results.toList

    -- Extract information for display from results
    let mut initIdAndResults := #[]
    let mut thmIdAndResults := #[]
    let mut modelStrs := #[]
    let mut (admittedTheorems, unprovenTheorems) := (#[], #[])

    -- If we're running in async mode, we need to add the theorems to the
    -- environment manually. If we run without proof reconstruction, we
    -- don't have to call the SMT solver again (we just admit the theorems).
    -- With proof reconstruction, we re-do the work, unfortunately.
    let theoremsToAdd ← do
      if Elab.async.get (← getOptions) then
        let sorry_body := if veil.smt.reconstructProofs.get (← getOptions) then false else true
        pure $ (← theoremSuggestionsForIndicators (!initChecks.isEmpty) actIndicators invIndicators vcStyle sorry_body) |>.toList |> Std.HashMap.ofList
      else
        pure $ Std.HashMap.emptyWithCapacity 0

    for result in results do
      let {theoremId, proofResult, smtResult, timeInMs, modelStr} := result
      -- The async code we currently have does not actually add the
      -- theorems to the environment, so we add proven theorems manually
      -- with a `sorry` body.
      if proofResult.isProven && Elab.async.get (← getOptions) then
        let .some cmd := theoremsToAdd.get? theoremId
          | throwError s!"theorem {theoremId.theoremName} not found in allTheoremsSorry"
        if (← resolveGlobalName theoremId.theoremName).isEmpty then
          elabCommand $ ← `(#guard_msgs(drop warning) in $(cmd))
      if theoremId.actName.isNone then
          initIdAndResults := initIdAndResults.push (theoremId, (smtResult, .some timeInMs))
      else
        thmIdAndResults := thmIdAndResults.push (theoremId, (smtResult, .some timeInMs))
      if let .some modelStr := modelStr then
        modelStrs := modelStrs.push modelStr
      if proofResult.isAdmitted then
        admittedTheorems := admittedTheorems.push theoremId
      if !proofResult.isProven then
        unprovenTheorems := unprovenTheorems.push theoremId
      if theoremId.invName.isNone then
        if let .some exId := getExId modelStrs then
          throwTerminationErrorAt exId theoremId.actName.get!

    -- Display results
    let initMsgs ← getInitCheckResultMessages initIdAndResults.toList
    let actMsgs ← getActCheckResultMessages thmIdAndResults.toList
    let checkMsgs := initMsgs ++ actMsgs
    let modelMsgs := if modelStrs.isEmpty || (!veil.printCounterexamples.get (← getOptions)) then [] else ["\nCounter-examples", "================\n"] ++ modelStrs.toList
    let msg := ("\n".intercalate (checkMsgs.toList ++ modelMsgs))
    logInfo msg
    match suggestionStyle with
    | .doNotPrint => pure ()
    | .printAllTheorems => displaySuggestion stx (allTheorems.map Prod.snd)
    | .printUnverifiedTheorems =>
      let unverifiedTheoremIds := ((initIdAndResults ++ thmIdAndResults).filter (fun res => match res with
        | (_, .Unsat, _) => false
        | _ => true)).map (fun (id, _) => id)
      let unverifiedTheorems := (allTheorems.filter (fun (id, _) => unverifiedTheoremIds.any (fun id' => id == id'))).map Prod.snd
      displaySuggestion stx unverifiedTheorems
    if !unprovenTheorems.isEmpty && (!veil.printCounterexamples.get (← getOptions)) then
      logInfo s!"Run with `set_option veil.printCounterexamples true` to print counter-examples."
    if !admittedTheorems.isEmpty then
      -- let admittedTheoremsStr := String.intercalate ", " (admittedTheorems.toList.map (fun id => id.theoremName.toString))
      let theoremStr := if admittedTheorems.size == 1 then "one theorem" else s!"{admittedTheorems.size} theorems"
      logWarning s!"Trusting the SMT solver for {theoremStr}."
    if !unprovenTheorems.isEmpty then
      let theoremStr := if unprovenTheorems.size == 1 then "one clause is" else s!"{unprovenTheorems.size} clauses are"
      let str := s!"The invariant is not inductive: {theoremStr} not preserved!"
      if veil.failedCheckThrowsError.get (← getOptions) then
        throwError str
      else
        logWarning str
  | (.wp, .checkTheoremsWithIndicators, _) => throwError "[checkTheorems] wp style is not supported for checkTheoremsWithIndicators"
  | (.transition, .checkTheoremsWithIndicators, _) =>
    let (msg, initRes, actRes) ← Command.runTermElabM fun vs => do
      let (systemTp, stateTp, readerTp, rd, st, st') := (← getSystemTpStx vs, ← getStateTpStx, ← getReaderTpStx, mkIdent `rd, mkIdent `st, mkIdent `st')
      let sectionArgs ← getSectionArgumentsStx vs
      -- get the syntax of the transitions
      let actStxList : Array Term ← actIndicators.toArray.mapM (fun (actName, indName) => do
        let actName ← resolveGlobalConstNoOverloadCore actName
        let tr := mkIdent $ toTrName actName
        let .some indName := indName.constName? | throwError s!"indicator {indName} not found"
        `($(mkIdent indName) ∧ (@$tr $sectionArgs* $rd $st $st'))
      )
      let invStxList : Array Term ← invIndicators.toArray.mapM (fun (invName, indName) => do
        let invName ← resolveGlobalConstNoOverloadCore invName
        let .some indName := indName.constName? | throwError s!"indicator {indName} not found"
        `(($(mkIdent indName) → @$(mkIdent invName) $sectionArgs* $rd $st'))
      )
      let invariants ← repeatedAnd invStxList
      let _actions ← repeatedOr actStxList
      let allIndicators := List.append invIndicators actIndicators
      let withTimeout := veil.smt.timeout.get (← getOptions)

      -- Init checks
      let initParams ← Array.mapM (fun (_, e) => do
        return ← `(bracketedBinder| ($(mkIdent e.constName!) : Prop))
      ) $ invIndicators.toArray
      let initTpStx ← `(∀ $[$initParams]* ($rd : $readerTp) ($st' : $stateTp), ($systemTp).$(mkIdent `assumptions) $rd $st' → ($systemTp).$(mkIdent `init) $rd $st' → $invariants)
      trace[veil] "init check: {initTpStx}"
      let initCmd ← translateExprToSmt $ (← elabTerm initTpStx none)
      trace[veil.debug] "SMT init check: {initCmd}"
      let initRes ← querySolverWithIndicators initCmd withTimeout (initChecks.map (fun a => #[a]))
      let initMsgs ← getInitCheckResultMessages $ initRes.map (fun (l, res) => match l with
      | [invName] => (⟨invName, .none, mkTheoremName `init invName⟩, (res, .none))
      | _ => unreachable!)

      -- Action checks
      let actParams ← Array.mapM (fun (_, e) => do
        return ← `(bracketedBinder| ($(mkIdent e.constName!) : Prop))
      ) $ allIndicators.toArray
      let actTpStx ← `(∀ $[$actParams]* ($rd : $readerTp) ($st $st' : $stateTp), ($systemTp).$(mkIdent `assumptions) $rd $st → ($systemTp).$(mkIdent `inv) $rd $st → $_actions → $invariants)
      trace[veil] "action check: {actTpStx}"
      let actCmd ← translateExprToSmt $ (← elabTerm actTpStx none)
      trace[veil.debug] "SMT action check: {actCmd}"
      let actRes ← querySolverWithIndicators actCmd withTimeout (invChecks.map (fun (a, b) => #[a, b]))
      let actMsgs ← getActCheckResultMessages $ actRes.map (fun (l, res) => match l with
      | [actName, invName] => (⟨actName, invName, mkTheoremName actName invName⟩, (res, .none))
      | _ => unreachable!)

      let msg := (String.intercalate "\n" initMsgs.toList) ++ "\n" ++ (String.intercalate "\n" actMsgs.toList) ++ "\n"
      return (msg, initRes, actRes)

    -- Display result of checking
    logInfo msg

    -- Admit proven theorems
    let provenInit := (initRes.filter (fun (_, res) => match res with
      | .Unsat => true
      | _ => false)).map (fun (l, _) => match l with | [invName] => invName | _ => unreachable!)
    let provenActs := (actRes.filter (fun (_, res) => match res with
        | .Unsat => true
        | _ => false)).map (fun (l, _) => match l with | [actName, invName] => (invName, actName) | _ => unreachable!)
    let verifiedTheorems := (← theoremSuggestionsForChecks provenInit provenActs vcStyle)
    for (name, cmd) in verifiedTheorems do
      let resolved ← resolveGlobalName name.theoremName
      if resolved.isEmpty then
        elabCommand cmd
      else
        logInfo s!"{name.theoremName} was proven previously"
    -- Display if needed
    match suggestionStyle with
    | .doNotPrint => pure ()
    | .printAllTheorems => displaySuggestion stx (allTheorems.map Prod.snd)
    | .printUnverifiedTheorems =>
        let neededInit := (initRes.filter (fun (_, res) => match res with
        | .Unsat => false
        | _ => true)).map (fun (l, _) => match l with | [invName] => invName | _ => unreachable!)
        let neededActs := (actRes.filter (fun (_, res) => match res with
          | .Unsat => false
          | _ => true)).map (fun (l, _) => match l with | [actName, invName] => (invName, actName) | _ => unreachable!)
        let unverifiedTheorems ← theoremSuggestionsForChecks neededInit neededActs vcStyle
        displaySuggestion stx (unverifiedTheorems.map Prod.snd) (preMsg := msg)

/- ## `#check_invariants` -/

/-- Check all invariants and print result of each check. Uses `wp` VC
style. -/
syntax "#check_invariants" : command
/-- Suggest theorems to check all invariants. Uses `wp` VC style. -/
syntax "#check_invariants?" : command
/-- Check all invariants and suggest only theorems that
were not proved automatically. Uses `wp` VC style. -/
syntax "#check_invariants!" : command

/-- Check all invariants in specified isolates and print result of
each check. Uses `wlp` VC style. -/
syntax "#check_isolate" ident : command
/-- Suggest theorems to check all invariants in isolates. Uses `wlp`
VC style. -/
syntax "#check_isolate?" ident : command
/-- Check all invariants in isolates and suggest only theorems that
were not proved automatically. Uses `wlp` VC style. -/
syntax "#check_isolate!" ident : command

/-- Check all invariants in a specified isolate and print result of
each check. Uses `wlp` VC style. -/
syntax "#check_isolates" ident* : command
/-- Suggest theorems to check all invariants in the isolate. Uses `wlp`
VC style. -/
syntax "#check_isolates?" ident* : command
/-- Check all invariants in the isolate and suggest only theorems that
were not proved automatically. Uses `wlp` VC style. -/
syntax "#check_isolates!" ident* : command


/-- Legacy code: generates a mega-query with indicator variables and
checks each action-invariant pair with a separate `check-sat-assuming`
query. -/
syntax "#check_invariants_indicators" : command

/-- Prints output similar to that of Ivy's `ivy_check` command. -/
def checkInvariants (stx : Syntax) (behaviour : CheckInvariantsBehaviour)
  (isolate : NameHashSet := ∅) : CommandElabM Unit := do
  liftCoreM errorOrWarnWhenSpecIsNeeded
  let (initChecks, actChecks) ← getAllChecks isolate
  checkTheorems stx initChecks actChecks behaviour

def checkIsolate (stx : Syntax) (behaviour : CheckInvariantsBehaviour)
  (isolates : Array Ident) : CommandElabM Unit := do
  for iso in isolates do
    unless (<- localSpecCtx.getIsolates).isolateStore.contains iso.getId do
      throwErrorAt iso s!"Isolate {iso.getId} not found in the current context."
  checkInvariants stx behaviour (isolate := Std.HashSet.ofArray <| isolates.map TSyntax.getId)

elab_rules : command
  | `(command| #check_invariants)  => do checkInvariants (← getRef) (behaviour := ← CheckInvariantsBehaviour.default)
  | `(command| #check_invariants?) => do checkInvariants (← getRef) (behaviour := ← CheckInvariantsBehaviour.question)
  | `(command| #check_invariants!) => do checkInvariants (← getRef) (behaviour := ← CheckInvariantsBehaviour.exclamation)
  | `(command| #check_isolate $is)  => do checkIsolate (← getRef) (behaviour := ← CheckInvariantsBehaviour.default) (isolates := #[is])
  | `(command| #check_isolate? $is) => do checkIsolate (← getRef) (behaviour := ← CheckInvariantsBehaviour.question) (isolates := #[is])
  | `(command| #check_isolate! $is) => do checkIsolate (← getRef) (behaviour := ← CheckInvariantsBehaviour.exclamation) (isolates := #[is])
  | `(command| #check_isolates $is*)  => do checkIsolate (← getRef) (behaviour := ← CheckInvariantsBehaviour.default) (isolates := is)
  | `(command| #check_isolates? $is*) => do checkIsolate (← getRef) (behaviour := ← CheckInvariantsBehaviour.question) (isolates := is)
  | `(command| #check_isolates! $is*) => do checkIsolate (← getRef) (behaviour := ← CheckInvariantsBehaviour.exclamation) (isolates := is)
  | `(command| #check_invariants_indicators) => do checkInvariants (← getRef) (behaviour := (.transition, .checkTheoremsWithIndicators, .doNotPrint))

/- ## `#check_invariant` -/
syntax "#check_invariant" ident : command
syntax "#check_invariant?" ident : command
syntax "#check_invariant!" ident : command

/-- Prints output similar to that of Ivy's `ivy_check` command limited to a single invariant. -/
def checkInvariant (stx : Syntax) (invName : TSyntax `ident) (behaviour : CheckInvariantsBehaviour) : CommandElabM Unit := do
  liftCoreM errorOrWarnWhenSpecIsNeeded
  let (initChecks, actChecks) ← getChecksForInvariant invName.getId
  checkTheorems stx initChecks actChecks behaviour

elab_rules : command
  | `(command| #check_invariant $invName)  => do checkInvariant (← getRef) invName (behaviour := ← CheckInvariantsBehaviour.default)
  | `(command| #check_invariant? $invName) => do checkInvariant (← getRef) invName (behaviour := ← CheckInvariantsBehaviour.question)
  | `(command| #check_invariant! $invName) => do checkInvariant (← getRef) invName (behaviour := ← CheckInvariantsBehaviour.exclamation)

/- ## `#check_action` -/
syntax "#check_action" ident : command
syntax "#check_action?" ident : command
syntax "#check_action!" ident : command

/-- Prints output similar to that of Ivy's `ivy_check` command limited to a single action. -/
def checkAction (stx : Syntax) (actName : TSyntax `ident) (behaviour : CheckInvariantsBehaviour) : CommandElabM Unit := do
  liftCoreM errorOrWarnWhenSpecIsNeeded
  let (initChecks, actChecks) ← getChecksForAction actName.getId
  checkTheorems stx initChecks actChecks behaviour

elab_rules : command
  | `(command| #check_action $actName)  => do checkAction (← getRef) actName (behaviour := ← CheckInvariantsBehaviour.default)
  | `(command| #check_action? $actName) => do checkAction (← getRef) actName (behaviour := ← CheckInvariantsBehaviour.question)
  | `(command| #check_action! $actName) => do checkAction (← getRef) actName (behaviour := ← CheckInvariantsBehaviour.exclamation)

open Tactic in
/-- Try to solve the goal using one of the already proven invariant clauses,
    i.e. one of those marked with `@[invProof]` (via `#check_invariants`). -/
elab "already_proven" : tactic => withMainContext do
  let clauses := (← localSpecCtx.get).establishedClauses.toArray
  let tacs ← clauses.mapM (fun cl => `(tactic|(try apply $(mkIdent cl) <;> assumption)))
  let attempt ← `(tactic| solve $[| $tacs:tactic]*)
  evalTactic attempt

elab "prove_inv_init" proof:term : command => do
  liftCoreM errorOrWarnWhenSpecIsNeeded
  elabCommand $ <- Command.runTermElabM fun _ => do
    let stateTp <- getStateTpStx
    let readerTp <- getReaderTpStx
    let invInit := mkIdent ``RelationalTransitionSystem.invInit
    `(theorem $(mkIdent `inv_init) : $invInit (σ := $stateTp) (ρ := $readerTp) :=
       by unfold $invInit
          -- simp only [initSimp, invSimp]
          intros $(mkIdent `st)
          exact $proof)

elab "prove_inv_safe" proof:term : command => do
  liftCoreM errorOrWarnWhenSpecIsNeeded
  elabCommand $ <- Command.runTermElabM fun _ => do
    let stateTp <- getStateTpStx
    let readerTp <- getReaderTpStx
    let invSafe := mkIdent ``RelationalTransitionSystem.invSafe
    `(theorem $(mkIdent `safety_init) : $invSafe (σ := $stateTp) (ρ := $readerTp) :=
       by unfold $invSafe;
          -- simp only [initSimp, safeSimp]
          intros $(mkIdent `st);
          exact $proof)

elab "prove_inv_inductive" proof:term : command => do
  liftCoreM errorOrWarnWhenSpecIsNeeded
  elabCommand $ <- Command.runTermElabM fun _ => do
    let stateTp <- getStateTpStx
    let readerTp <- getReaderTpStx
    let invInductive := mkIdent ``RelationalTransitionSystem.isInductive
    let inv := mkIdent ``RelationalTransitionSystem.inv
    `(theorem $(mkIdent `inv_inductive) : $invInductive (σ := $stateTp) (ρ := $readerTp) $inv :=
      by unfold $invInductive;
        --  intros $(mkIdent `st) $(mkIdent `st')
        --  simp only [actSimp, invSimp, safeSimp]
         exact $proof)
