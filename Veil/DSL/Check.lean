import Lean
import Veil.Tactic
import Veil.DSL.Attributes
import Veil.DSL.StateExtensions
import Veil.DSL.Util
import Veil.DSL.DisplayUtil
import Veil.DSL.SMTUtil

open Lean Elab Command Term Meta Lean.Parser Tactic.TryThis Lean.Core

/-- We support two styles of verification condition generation:
  - `wlp`, which is what Ivy does
  - `transition`, which is what mypyvy does

  The `transition` style is more general, but `wlp` generates smaller, usually
  better queries.
-/
inductive VCGenStyle
  | wlp
  | transition

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

def CheckInvariantsBehaviour := VCGenStyle × CheckStyle × TheoremSuggestionStyle
def CheckInvariantsBehaviour.default (style : VCGenStyle := .wlp) : CheckInvariantsBehaviour := (style, .checkTheoremsIndividually, .doNotPrint)
def CheckInvariantsBehaviour.question (style : VCGenStyle := .wlp) : CheckInvariantsBehaviour := (style, .noCheck, .printAllTheorems)
def CheckInvariantsBehaviour.exclamation (style : VCGenStyle := .wlp) : CheckInvariantsBehaviour := (style, .checkTheoremsIndividually, .printUnverifiedTheorems)

/--  Generate theorems to check in the initial state and after each action -/
def getAllChecks : CommandElabM (Array (Name × Expr) × Array ((Name × Expr) × (Name × Expr))) := Command.runTermElabM fun _ => do
    let invNames := (← localSpecCtx.get).spec.invariants.map StateAssertion.name
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

def mkTheoremName (actName : Name) (invName : Name) : Name := s!"{actName}_{invName.components.getLast!}".toName

def theoremSuggestionsForChecks (initIndicators : List Name) (actIndicators : List (Name × Name)) (vcStyle : VCGenStyle) (sorry_body: Bool := true): CommandElabM (Array (TheoremIdentifier × TSyntax `command)) := do
    Command.runTermElabM fun vs => do
      let (systemTp, stateTp, st, st') := (← getSystemTpStx vs, ← getStateTpStx, mkIdent `st, mkIdent `st')
      let sectionArgs ← getSectionArgumentsStx vs
      let mut theorems : Array (TheoremIdentifier × TSyntax `command) := #[]
      -- Init checks
      for invName in initIndicators.reverse do
        let invStx ← `(@$(mkIdent invName) $sectionArgs*)
        let initTpStx ← `(∀ ($st : $stateTp), ($systemTp).$(mkIdent `assumptions) $st → ($systemTp).$(mkIdent `init) $st → $invStx $st)
        let body ← if sorry_body then `(by (unhygienic intros); exact sorry) else `(by (unhygienic intros); solve_clause [$(mkIdent `initSimp)])
        let thmName := mkTheoremName `init invName
        let thm ← `(@[invProof] theorem $(mkIdent thmName) : $initTpStx := $body)
        theorems := theorems.push (⟨invName, .none, thmName⟩, thm)
      -- Action checks
      for (actName, invName) in actIndicators.reverse do
        let (tp, body) ← match vcStyle with
        | .transition =>
          let trName := toTrName actName
          let invStx ← `(@$(mkIdent invName) $sectionArgs*)
          let trStx ← `(@$(mkIdent trName) $sectionArgs*)
          let trTpSyntax ← `(∀ ($st $st' : $stateTp), ($systemTp).$(mkIdent `assumptions) $st → ($systemTp).$(mkIdent `inv) $st → $trStx $st $st' → $invStx $st')
          let body ← if sorry_body then `(by (unhygienic intros); exact sorry) else `(by (unhygienic intros); solve_clause [$(mkIdent trName)])
          pure (trTpSyntax, body)
        | .wlp =>
          let extName := toExtName actName
          let moduleName <- getCurrNamespace
          let some args := (<- localSpecCtx.get).spec.actions.find? (moduleName ++ ·.name == actName)
            | throwError s!"action {actName} not found"
          let (univBinders, args) ← match args.br with
          | some br => pure (← toBracketedBinderArray br, ← existentialIdents br)
          | none => pure (#[], #[])
          let invStx ← `(fun _ ($st' : $stateTp) => @$(mkIdent invName) $sectionArgs*  $st')
          let extStx ← `(@$(mkIdent extName) $sectionArgs* $args*)
          let extTpSyntax ← `(∀ ($st : $stateTp), forall? $univBinders*, ($systemTp).$(mkIdent `assumptions) $st → ($systemTp).$(mkIdent `inv) $st → $extStx $st $invStx)
          let body ← if sorry_body then `(by (unhygienic intros); exact sorry) else `(by solve_wlp_clause $(mkIdent extName) $(mkIdent invName))
          pure (extTpSyntax, body)
        let thmName := mkTheoremName actName invName
        let thm ← `(@[invProof] theorem $(mkIdent thmName) : $tp := $body)
        theorems := theorems.push (⟨invName, .some actName, thmName⟩, thm)
      return theorems

def theoremSuggestionsForIndicators (generateInitThms : Bool) (actIndicators invIndicators : List (Name × Expr)) (vcStyle : VCGenStyle) : CommandElabM (Array (TheoremIdentifier × TSyntax `command)) := do
  let (initIndicators, acts) ← Command.runTermElabM fun _ => do
    -- prevent code duplication
    let initIndicators ← invIndicators.mapM (fun (invName, _) => resolveGlobalConstNoOverloadCore invName)
    let actIndicators ← actIndicators.mapM (fun (actName, _) => resolveGlobalConstNoOverloadCore actName)
    let mut acts := #[]
    for actName in actIndicators do
      for invName in initIndicators do
        acts := acts.push (actName, invName)
    return (initIndicators, acts)
  theoremSuggestionsForChecks (if generateInitThms then initIndicators else []) acts.toList vcStyle (sorry_body := False)

def checkIndividualTheorem (thmId : TheoremIdentifier) (cmd : TSyntax `command) : CommandElabM Bool := do
  let env ← getEnv
  -- If the theorem has been defined already, reuse the existing
  -- definition to figure out whether it's proven
  if (← resolveGlobalName thmId.theoremName).isEmpty then
    trace[dsl.debug] "Checking theorem {thmId.theoremName} for the first time"
    elabCommand (← `(#guard_msgs(drop warning) in $(cmd)))
  else
    trace[dsl.debug] "Theorem {thmId.theoremName} has been checked before; reusing result"
  -- Check the `Expr` for the given theorem
  let thFullName ← resolveGlobalConstNoOverloadCore thmId.theoremName
  let th ← getConstInfo thFullName
  let isProven ← match th with
    | ConstantInfo.thmInfo attempt => pure <| !attempt.value.hasSyntheticSorry
    | _ => throwError s!"checkTheorem: expected {thmId.theoremName} to be a theorem"
  -- We only add the theorem to the environment if it successfully type-checks
  -- i.e. we restore the original environment if the theorem is not proven
  if !isProven then
    setEnv env
  return isProven

def Lean.MessageLog.containsSubStr (msgs : MessageLog) (substr : String) : CommandElabM Bool := do
  msgs.toList.anyM (fun msg => return String.isSubStrOf substr (← msg.data.toString))

def checkTheorems (stx : Syntax) (initChecks: Array (Name × Expr)) (invChecks: Array ((Name × Expr) × (Name × Expr))) (behaviour : CheckInvariantsBehaviour := CheckInvariantsBehaviour.default) :
  CommandElabM Unit := do
  let actIndicators := (invChecks.map (fun (_, (act_name, ind_name)) => (act_name, ind_name))).toList.removeDuplicates
  let invIndicators := (invChecks.map (fun ((inv_name, ind_name), _) => (inv_name, ind_name))).toList.removeDuplicates
  let (vcStyle, checkStyle, suggestionStyle) := behaviour
  let mut allTheorems ← theoremSuggestionsForIndicators (!initChecks.isEmpty) actIndicators invIndicators vcStyle
  match behaviour with
  | (_, .noCheck, .doNotPrint) => pure ()
  | (_, .noCheck, .printUnverifiedTheorems) => throwError "[checkTheorems] Cannot print unverified theorems without checking"
  | (_, .noCheck, .printAllTheorems) => displaySuggestion stx (allTheorems.map Prod.snd)
  | (_, .checkTheoremsIndividually, _) =>
    let mut initIdAndResults := #[]
    let mut thmIdAndResults := #[]
    for (thmId, cmd) in allTheorems do
      -- save messages before elaboration
      let origMsgs := (<- get).messages
      let isProven ← checkIndividualTheorem thmId (← `(#guard_msgs(drop warning) in $(cmd)))
      let msgs := (← get).messages
      let result ← if isProven then pure SmtResult.Unsat else
        -- The theorem is not proven; we need to figure out why:
        -- either solver returned `sat`, `unknown`, or there was an error
        let msgsTxt := String.intercalate "\n" (← msgs.toList.mapM (fun msg => msg.toString))
        let (hasSat, hasUnknown, hasFailure) := (← msgs.containsSubStr Smt.satGoalStr, ← msgs.containsSubStr Smt.unknownGoalStr, ← msgs.containsSubStr Smt.failureGoalStr)
        pure $ match hasSat, hasUnknown, hasFailure with
        | true, false, false => SmtResult.Sat .none
        | false, true, false => SmtResult.Unknown msgsTxt
        | false, false, true => SmtResult.Failure msgsTxt
        | _, _, _ =>
          dbg_trace s!"[{thmId.theoremName}] (isProven: {isProven}, hasSat: {hasSat}, hasUnknown: {hasUnknown}, hasFailure: {hasFailure}) Unexpected messages: {msgsTxt}"
          unreachable!
      if thmId.actName.isNone then
        initIdAndResults := initIdAndResults.push (thmId, result)
      else
        thmIdAndResults := thmIdAndResults.push (thmId, result)
      -- restore messages (similar to `#guard_msgs`)
      modify fun st => { st with messages := origMsgs }
    let initMsgs := getInitCheckResultMessages initIdAndResults.toList
    let msgs := getActCheckResultMessages thmIdAndResults.toList
    let msgs := initMsgs ++ msgs
    logInfo ("\n".intercalate msgs.toList)
    match suggestionStyle with
    | .doNotPrint => pure ()
    | .printAllTheorems => displaySuggestion stx (allTheorems.map Prod.snd)
    | .printUnverifiedTheorems =>
      let unverifiedTheoremIds := (thmIdAndResults.filter (fun res => match res with
        | (_, .Unsat) => false
        | _ => true)).map (fun (id, _) => id)
      let unverifiedTheorems := (allTheorems.filter (fun (id, _) => unverifiedTheoremIds.any (fun id' => id == id'))).map Prod.snd
      displaySuggestion stx unverifiedTheorems
  | (.wlp, .checkTheoremsWithIndicators, _) => throwError "[checkTheorems] wlp style is not supported for checkTheoremsWithIndicators"
  | (.transition, .checkTheoremsWithIndicators, _) =>
    let (msg, initRes, actRes) ← Command.runTermElabM fun vs => do
      let (systemTp, stateTp, st, st') := (← getSystemTpStx vs, ← getStateTpStx, mkIdent `st, mkIdent `st')
      let sectionArgs ← getSectionArgumentsStx vs
      -- get the syntax of the transitions
      let actStxList : Array Term ← actIndicators.toArray.mapM (fun (actName, indName) => do
        let actName ← resolveGlobalConstNoOverloadCore actName
        let tr := mkIdent $ toTrName actName
        let .some indName := indName.constName? | throwError s!"indicator {indName} not found"
        `($(mkIdent indName) ∧ (@$tr $sectionArgs* $st $st'))
      )
      let invStxList : Array Term ← invIndicators.toArray.mapM (fun (invName, indName) => do
        let invName ← resolveGlobalConstNoOverloadCore invName
        let .some indName := indName.constName? | throwError s!"indicator {indName} not found"
        `(($(mkIdent indName) → @$(mkIdent invName) $sectionArgs* $st'))
      )
      let invariants ← repeatedAnd invStxList
      let _actions ← repeatedOr actStxList
      let allIndicators := List.append invIndicators actIndicators
      let withTimeout := auto.smt.timeout.get (← getOptions)

      -- Init checks
      let initParams ← Array.mapM (fun (_, e) => do
        return ← `(bracketedBinder| ($(mkIdent e.constName!) : Prop))
      ) $ invIndicators.toArray
      let initTpStx ← `(∀ $[$initParams]* ($st' : $stateTp), ($systemTp).$(mkIdent `assumptions) $st' → ($systemTp).$(mkIdent `init) $st' → $invariants)
      trace[dsl] "init check: {initTpStx}"
      let initCmd ← translateExprToSmt $ (← elabTerm initTpStx none)
      trace[dsl.debug] "SMT init check: {initCmd}"
      let initRes ← querySolverWithIndicators initCmd withTimeout (initChecks.map (fun a => #[a]))
      let initMsgs := getInitCheckResultMessages $ initRes.map (fun (l, res) => match l with
      | [invName] => (⟨invName, .none, mkTheoremName `init invName⟩, res)
      | _ => unreachable!)

      -- Action checks
      let actParams ← Array.mapM (fun (_, e) => do
        return ← `(bracketedBinder| ($(mkIdent e.constName!) : Prop))
      ) $ allIndicators.toArray
      let actTpStx ← `(∀ $[$actParams]* ($st $st' : $stateTp), ($systemTp).$(mkIdent `assumptions) $st → ($systemTp).$(mkIdent `inv) $st → $_actions → $invariants)
      trace[dsl] "action check: {actTpStx}"
      let actCmd ← translateExprToSmt $ (← elabTerm actTpStx none)
      trace[dsl.debug] "SMT action check: {actCmd}"
      let actRes ← querySolverWithIndicators actCmd withTimeout (invChecks.map (fun (a, b) => #[a, b]))
      let actMsgs := getActCheckResultMessages $ actRes.map (fun (l, res) => match l with
      | [actName, invName] => (⟨actName, invName, mkTheoremName actName invName⟩, res)
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
      -- `drop warning` to not show the sorry warning; `drop error` in case it's been defined before
      elabCommand (← `(#guard_msgs(drop warning, drop error) in $(cmd)))

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

/-- Check all invariants and print result of each check. Uses `wlp` VC
style. -/
syntax "#check_invariants" : command
/-- Suggest theorems to check all invariants. Uses `wlp` VC style. -/
syntax "#check_invariants?" : command
/-- Check all invariants and suggest only theorems that
were not proved automatically. Uses `wlp` VC style. -/
syntax "#check_invariants!" : command

/-- Check all invariants and print result of each check. Uses `tr` VC
style. -/
syntax "#check_invariants_tr" : command
/-- Suggest theorems to check all invariants. Uses `tr` VC style. -/
syntax "#check_invariants_tr?" : command
/-- Check all invariants and suggest only theorems that
were not proved automatically. Uses `tr` VC style. -/
syntax "#check_invariants_tr!" : command

/-- Legacy code: generates a mega-query with indicator variables and
checks each action-invariant pair with a separate `check-sat-assuming`
query. -/
syntax "#check_invariants_indicators" : command

/-- Prints output similar to that of Ivy's `ivy_check` command. -/
def checkInvariants (stx : Syntax) (behaviour : CheckInvariantsBehaviour := CheckInvariantsBehaviour.default) : CommandElabM Unit := do
  liftCoreM errorIfStateNotDefined
  let (initChecks, actChecks) ← getAllChecks
  checkTheorems stx initChecks actChecks behaviour

elab_rules : command
  | `(command| #check_invariants)  => do checkInvariants (← getRef) (behaviour := .default)
  | `(command| #check_invariants?) => do checkInvariants (← getRef) (behaviour := .question)
  | `(command| #check_invariants!) => do checkInvariants (← getRef) (behaviour := .exclamation)
  | `(command| #check_invariants_tr)  => do checkInvariants (← getRef) (behaviour := .default .transition)
  | `(command| #check_invariants_tr?) => do checkInvariants (← getRef) (behaviour := .question .transition)
  | `(command| #check_invariants_tr!) => do checkInvariants (← getRef) (behaviour := .exclamation .transition)
  | `(command| #check_invariants_indicators) => do checkInvariants (← getRef) (behaviour := (.transition, .checkTheoremsWithIndicators, .doNotPrint))

/- ## `#check_invariant` -/
syntax "#check_invariant" ident : command
syntax "#check_invariant?" ident : command
syntax "#check_invariant!" ident : command

/-- Prints output similar to that of Ivy's `ivy_check` command limited to a single invariant. -/
def checkInvariant (stx : Syntax) (invName : TSyntax `ident) (behaviour : CheckInvariantsBehaviour := CheckInvariantsBehaviour.default) : CommandElabM Unit := do
  liftCoreM errorIfStateNotDefined
  let (initChecks, actChecks) ← getChecksForInvariant invName.getId
  checkTheorems stx initChecks actChecks behaviour

elab_rules : command
  | `(command| #check_invariant $invName)  => do checkInvariant (← getRef) invName (behaviour := .default)
  | `(command| #check_invariant? $invName) => do checkInvariant (← getRef) invName (behaviour := .question)
  | `(command| #check_invariant! $invName) => do checkInvariant (← getRef) invName (behaviour := .exclamation)

/- ## `#check_action` -/
syntax "#check_action" ident : command
syntax "#check_action?" ident : command
syntax "#check_action!" ident : command

/-- Prints output similar to that of Ivy's `ivy_check` command limited to a single action. -/
def checkAction (stx : Syntax) (actName : TSyntax `ident) (behaviour : CheckInvariantsBehaviour := CheckInvariantsBehaviour.default) : CommandElabM Unit := do
  liftCoreM errorIfStateNotDefined
  let (initChecks, actChecks) ← getChecksForAction actName.getId
  checkTheorems stx initChecks actChecks behaviour

elab_rules : command
  | `(command| #check_action $actName)  => do checkAction (← getRef) actName (behaviour := .default)
  | `(command| #check_action? $actName) => do checkAction (← getRef) actName (behaviour := .question)
  | `(command| #check_action! $actName) => do checkAction (← getRef) actName (behaviour := .exclamation)

open Tactic in
/-- Try to solve the goal using one of the already proven invariant clauses,
    i.e. one of those marked with `@[invProof]` (via `#check_invariants`). -/
elab "already_proven" : tactic => withMainContext do
  let clauses := (← localSpecCtx.get).establishedClauses.toArray
  let tacs ← clauses.mapM (fun cl => `(tactic|(try apply $(mkIdent cl) <;> assumption)))
  let attempt ← `(tactic| solve $[| $tacs:tactic]*)
  evalTactic attempt

elab "prove_inv_init" proof:term : command => do
  liftCoreM errorIfStateNotDefined
  elabCommand $ <- Command.runTermElabM fun _ => do
    let stateTp <- getStateTpStx
    let invInit := mkIdent ``RelationalTransitionSystem.invInit
    `(theorem $(mkIdent `inv_init) : $invInit (σ := $stateTp) :=
       by unfold $invInit
          -- simp only [initSimp, invSimp]
          intros $(mkIdent `st)
          exact $proof)

elab "prove_inv_safe" proof:term : command => do
  liftCoreM errorIfStateNotDefined
  elabCommand $ <- Command.runTermElabM fun _ => do
    let stateTp <- getStateTpStx
    let invSafe := mkIdent ``RelationalTransitionSystem.invSafe
    `(theorem $(mkIdent `safety_init) : $invSafe (σ := $stateTp) :=
       by unfold $invSafe;
          -- simp only [initSimp, safeSimp]
          intros $(mkIdent `st);
          exact $proof)

elab "prove_inv_inductive" proof:term : command => do
  liftCoreM errorIfStateNotDefined
  elabCommand $ <- Command.runTermElabM fun _ => do
    let stateTp <- getStateTpStx
    let invInductive := mkIdent ``RelationalTransitionSystem.invInductive
    `(theorem $(mkIdent `inv_inductive) : $invInductive (σ := $stateTp) :=
      by unfold $invInductive;
        --  intros $(mkIdent `st) $(mkIdent `st')
        --  simp only [actSimp, invSimp, safeSimp]
         exact $proof)
