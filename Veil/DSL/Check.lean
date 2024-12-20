import Lean
import Veil.Tactic
import Veil.DSL.Attributes
import Veil.DSL.StateExtensions
import Veil.DSL.Util
import Veil.DSL.DisplayUtil
import Veil.DSL.SMTUtil

open Lean Elab Command Term Meta Lean.Parser Tactic.TryThis

def checkTheorem (theoremName : Name) (cmd : TSyntax `command): CommandElabM Bool := do
  withTraceNode `dsl.perf.checkInvariants (fun _ => return m!"elab {theoremName} definition") do
  let env ← getEnv
  -- FIXME: I think we want to run `elabCommand` without `withLogging`
  elabCommand cmd
  -- Check the `Expr` for the given theorem
  let th ← getConstInfo theoremName
  let isProven ← match th with
    | ConstantInfo.thmInfo attempt => pure <| !attempt.value.hasSyntheticSorry
    | _ => throwError s!"checkTheorem: expected {theoremName} to be a theorem"
  -- We only add the theorem to the environment if it successfully type-checks
  -- i.e. we restore the original environment if the theorem is not proven
  if !isProven then
    setEnv env
  return isProven

inductive CheckType
  | init
  | action (actName : Name)
deriving BEq

/-- `(invName, theoremName, checkTheorem, failedTheorem)` -/
abbrev SingleCheckT   := (Name × Name × TSyntax `command × TSyntax `command)
abbrev InitChecksT    := Array SingleCheckT
abbrev ActionChecksT  := InitChecksT
abbrev ActionsChecksT := Array (Name × ActionChecksT)

/--  Generate theorems to check in the initial state and after each action -/
def getAllChecks : CommandElabM (Array (Name × Expr) × Array ((Name × Expr) × (Name × Expr))) := Command.runTermElabM fun vs => do
    let invNames := (← localSpecCtx.get).spec.invariants.map StateAssertion.name
    let actNames := ((<- localSpecCtx.get).spec.transitions).map (fun s => s.name)
    let invNamesInds := invNames.map (fun name => (name, Lean.mkConst $ Name.mkSimple s!"invInd_{mkPrintableName name}"))
    let actNamesInds := actNames.map (fun name => (name, Lean.mkConst $ Name.mkSimple s!"actInd_{mkPrintableName name}"))
    let mut actChecks := #[]
    for inv in invNamesInds do
       for act in actNamesInds do
         actChecks := actChecks.push (inv, act)
    return (invNamesInds, actChecks)

/-- Generate theorems to check the given invariant clause in the initial
state and after each action. -/
def getChecksForInvariant (invName : Name) : CommandElabM (Array (Name × Expr) × Array ((Name × Expr) × (Name × Expr))) := Command.runTermElabM fun vs => do
    let actNames := ((<- localSpecCtx.get).spec.transitions).map (fun s => s.name)
    let invNamesInd := (invName, Lean.mkConst $ Name.mkSimple s!"invInd_{mkPrintableName invName}")
    let actNamesInds := actNames.map (fun name => (name, Lean.mkConst $ Name.mkSimple s!"actInd_{mkPrintableName name}"))
    let mut actChecks := #[]
    for act in actNamesInds do
        actChecks := actChecks.push (invNamesInd, act)
    return (#[invNamesInd], actChecks)

/-- Generate therems to check all invariants after the given action. -/
def getChecksForAction (actName : Name) : CommandElabM (Array (Name × Expr) × Array ((Name × Expr) × (Name × Expr))) := Command.runTermElabM fun vs => do
    let invNames := (← localSpecCtx.get).spec.invariants.map StateAssertion.name
    let invNamesInds := invNames.map (fun name => (name, Lean.mkConst $ Name.mkSimple s!"invInd_{mkPrintableName name}"))
    let actNamesInd := (actName, Lean.mkConst $ Name.mkSimple s!"actInd_{mkPrintableName actName}")
    let mut invChecks := #[]
    for inv in invNamesInds do
        invChecks := invChecks.push (inv, actNamesInd)
    return (#[], invChecks)

inductive CheckInvariantsBehaviour
  /-- `#check_invariants` -/
  | checkTheorems
  /-- `#check_invariants?` -/
  | printTheorems
  /-- `#check_invariants!` -/
  | printAndCheckTheorems

def theoremSuggestionsForIndicators (generateInitThms : Bool) (actIndicators invIndicators : List (Name × Expr)) : CommandElabM (Array (TSyntax `command)) := do
  Command.runTermElabM fun vs => do
    let ge ← getEnv
    let (systemTp, stateTp, st, st') := (← getSystemTpStx vs, ← getStateTpStx vs, mkIdent `st, mkIdent `st')
    let mut theorems := #[]
    for (invName, _) in invIndicators do
      let .some _ := ge.find? invName
        | throwError s!"invariant {invName} not found"
      let invStx ← PrettyPrinter.delab $ mkAppN (mkConst invName) vs
      if generateInitThms then
        let initTpStx ← `(∀ ($st' : $stateTp), ($systemTp).$(mkIdent `init) $st' → $invStx $st')
        let thm ← `(@[invProof] theorem $(mkIdent s!"init_{invName}".toName) : $initTpStx := by unhygienic intros; solve_clause [$(mkIdent `initSimp)])
        theorems := theorems.push thm
      for (actName, _) in actIndicators do
        let .some _ := ge.find? actName
          | throwError s!"action {actName} not found"
        let actStx ← PrettyPrinter.delab $ mkAppN (mkConst actName) vs
        let actTpSyntax ← `(∀ ($st $st' : $stateTp), ($systemTp).$(mkIdent `inv) $st → $actStx $st $st' → $invStx $st')
        let thm ← `(@[invProof] theorem $(mkIdent s!"{actName}_{invName}".toName) : $actTpSyntax := by unhygienic intros; solve_clause [$(mkIdent actName)])
        theorems := theorems.push thm
    return theorems

def checkTheorems (stx : Syntax) (initChecks: Array (Name × Expr)) (invChecks: Array ((Name × Expr) × (Name × Expr))) (behaviour : CheckInvariantsBehaviour := .checkTheorems) :
  CommandElabM Unit := do
  let ge ← getEnv
  let actIndicators := (invChecks.map (fun (_, (act_name, ind_name)) => (act_name, ind_name))).toList.removeDuplicates
  let invIndicators := (invChecks.map (fun ((inv_name, ind_name), _) => (inv_name, ind_name))).toList.removeDuplicates
  let mut theorems ← theoremSuggestionsForIndicators (!initChecks.isEmpty) actIndicators invIndicators
  match behaviour with
  | .printTheorems => displaySuggestion stx theorems
  | .checkTheorems | .printAndCheckTheorems =>
    let msg ← Command.runTermElabM fun vs => do
      let (systemTp, stateTp, st, st') := (← getSystemTpStx vs, ← getStateTpStx vs, mkIdent `st, mkIdent `st')
      let actStxList ← actIndicators.mapM (fun (actName, indName) => do
        let .some _ := ge.find? actName
          | throwError s!"action {actName} not found"
        let act ← mkConst actName
        pure (mkAnd (mkApp2 (mkAppN act vs) (mkConst st.getId) (mkConst st'.getId)) indName)
        )
      let invStxList ← invIndicators.mapM (fun (invName, indName) => do
        let .some _ := ge.find? invName
          | throwError s!"invariant {invName} not found"
        let inv ← mkConst invName
        pure (mkOr (mkApp (mkAppN inv vs) (mkConst st'.getId)) (mkNot indName))
      )
      let _actions ← PrettyPrinter.delab $ mkOrN actStxList
      let invariants ← PrettyPrinter.delab $ Lean.mkAndN invStxList
      let allIndicators := List.append invIndicators actIndicators
      let timeout := auto.smt.timeout.get (← getOptions)

      -- Init checks
      let initParams ← Array.mapM (fun (_, e) => do
        return ← `(bracketedBinder| ($(mkIdent e.constName!) : Prop))
      ) $ invIndicators.toArray
      -- EK: We're using `st'` and not st because `invariants` is already phrased in terms of `st'`.
      let initTpStx ← `(∀ $[$initParams]* ($st' : $stateTp), ($systemTp).$(mkIdent `init) $st' → $invariants)
      trace[dsl] "init check: {initTpStx}"
      let initCmd ← translateExprToSmt $ (← elabTerm initTpStx none)
      trace[dsl.debug] "SMT init check: {initCmd}"
      let initRes ← querySolverWithIndicators initCmd timeout (initChecks.map (fun a => #[a]))
      let initMsgs := getInitCheckResultMessages $ initRes.map (fun (l, res) => match l with
        | [invName] => (invName, match res with
          | .Unsat _ => true
          | _ => false)
        | _ => unreachable!)

      -- Action checks
      let actParams ← Array.mapM (fun (_, e) => do
        return ← `(bracketedBinder| ($(mkIdent e.constName!) : Prop))
      ) $ allIndicators.toArray
      let actTpStx ← `(∀ $[$actParams]* ($st $st' : $stateTp), ($systemTp).$(mkIdent `inv) $st → $_actions → $invariants)
      trace[dsl] "action check: {actTpStx}"
      let actCmd ← translateExprToSmt $ (← elabTerm actTpStx none)
      trace[dsl.debug] "SMT action check: {actCmd}"
      let actRes ← querySolverWithIndicators actCmd timeout (invChecks.map (fun (a, b) => #[a, b]))
      let actMsgs := getActCheckResultMessages $ actRes.map (fun (l, res) => match l with
        | [actName, invName] => (invName, actName, match res with
          | .Unsat _ => true
          | _ => false)
        | _ => unreachable!)

      let msg := (String.intercalate "\n" initMsgs.toList) ++ "\n" ++ (String.intercalate "\n" actMsgs.toList) ++ "\n"
      pure msg
    match behaviour with
      | .checkTheorems => dbg_trace msg
      | .printAndCheckTheorems => displaySuggestion stx theorems (preMsg := msg)
      | _ => unreachable!


/- ## `#check_invariants` -/
/-- Check all invariants and print result of each check. -/
syntax "#check_invariants" : command
/-- Suggest theorems to check all invariants. -/
syntax "#check_invariants?" : command
/-- Check all invariants, print the result of each check, and suggest
theorems corresponding to the result of these checks. Theorems that
could not be proven have their proofs replaced with `sorry`. -/
syntax "#check_invariants!" : command

/-- Prints output similar to that of Ivy's `ivy_check` command. -/
def checkInvariants (stx : Syntax) (behaviour : CheckInvariantsBehaviour := .checkTheorems) : CommandElabM Unit := do
  let (initChecks, actChecks) ← getAllChecks
  checkTheorems stx initChecks actChecks behaviour

elab_rules : command
  | `(command| #check_invariants%$tk) => checkInvariants tk (behaviour := .checkTheorems)
  | `(command| #check_invariants?%$tk) => checkInvariants tk (behaviour := .printTheorems)
  | `(command| #check_invariants!%$tk) => checkInvariants tk (behaviour := .printAndCheckTheorems)


/- ## `#check_invariant` -/
syntax "#check_invariant" ident : command
syntax "#check_invariant?" ident : command
syntax "#check_invariant!" ident : command

/-- Prints output similar to that of Ivy's `ivy_check` command limited to a single invariant. -/
def checkInvariant (stx : Syntax) (invName : TSyntax `ident) (behaviour : CheckInvariantsBehaviour := .checkTheorems) : CommandElabM Unit := do
  let (initChecks, actChecks) ← getChecksForInvariant invName.getId
  checkTheorems stx initChecks actChecks behaviour

elab_rules : command
  | `(command| #check_invariant%$tk $invName) => checkInvariant tk invName (behaviour := .checkTheorems)
  | `(command| #check_invariant?%$tk $invName) => checkInvariant tk invName (behaviour := .printTheorems)
  | `(command| #check_invariant!%$tk $invName) => checkInvariant tk invName (behaviour := .printAndCheckTheorems)

/- ## `#check_action` -/
syntax "#check_action" ident : command
syntax "#check_action?" ident : command
syntax "#check_action!" ident : command

/-- Prints output similar to that of Ivy's `ivy_check` command limited to a single action. -/
def checkAction (stx : Syntax) (actName : TSyntax `ident) (behaviour : CheckInvariantsBehaviour := .checkTheorems) : CommandElabM Unit := do
  let (initChecks, actChecks) ← getChecksForAction (toTrIdent actName).getId
  checkTheorems stx initChecks actChecks behaviour

elab_rules : command
  | `(command| #check_action%$tk $actName) => checkAction tk actName (behaviour := .checkTheorems)
  | `(command| #check_action?%$tk $actName) => checkAction tk actName (behaviour := .printTheorems)
  | `(command| #check_action!%$tk $actName) => checkAction tk actName (behaviour := .printAndCheckTheorems)

open Tactic in
/-- Try to solve the goal using one of the already proven invariant clauses,
    i.e. one of those marked with `@[invProof]` (via `#check_invariants`). -/
elab "already_proven" : tactic => withMainContext do
  let clauses := (← localSpecCtx.get).establishedClauses.toArray
  let tacs ← clauses.mapM (fun cl => `(tactic|(try apply $(mkIdent cl) <;> assumption)))
  let attempt ← `(tactic| solve $[| $tacs:tactic]*)
  evalTactic attempt

elab "prove_inv_init" proof:term : command => do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- PrettyPrinter.delab (<- stateTp vs)
    `(theorem $(mkIdent `inv_init) : invInit (σ := $stateTp) :=
       by unfold invInit
          -- simp only [initSimp, invSimp]
          intros $(mkIdent `st)
          exact $proof)

elab "prove_inv_safe" proof:term : command => do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp   <- PrettyPrinter.delab (<- stateTp vs)
    `(theorem $(mkIdent `safety_init) : invSafe (σ := $stateTp) :=
       by unfold invSafe;
          -- simp only [initSimp, safeSimp]
          intros $(mkIdent `st);
          exact $proof)

elab "prove_inv_inductive" proof:term : command => do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp   <- PrettyPrinter.delab (<- stateTp vs)
    `(theorem $(mkIdent `inv_inductive) : invInductive (σ := $stateTp) :=
      by unfold invInductive invInit invConsecution;
        --  intros $(mkIdent `st) $(mkIdent `st')
        --  simp only [actSimp, invSimp, safeSimp]
         exact $proof)
