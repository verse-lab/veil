import Lean
import Lean.Meta.Tactic.TryThis
import LeanSts.Tactic
import LeanSts.DSL.StateExtensions
import LeanSts.DSL.Util

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

def getSystemTpStx (vs : Array Expr) : TermElabM Term := do
  let systemTp ← PrettyPrinter.delab $ mkAppN (mkConst (← localSpecCtx.get).spec.name) vs
  return systemTp

def getStateTpStx (vs : Array Expr) : TermElabM Term := do
  let stateTp ← PrettyPrinter.delab (← stateTp vs)
  return stateTp

inductive CheckType
  | init
  | action (actName : Name)
deriving BEq

/-- `(invName, theoremName, checkTheorem, failedTheorem)` -/
abbrev SingleCheckT   := (Name × Name × TSyntax `command × TSyntax `command)
abbrev InitChecksT    := Array SingleCheckT
abbrev ActionChecksT  := InitChecksT
abbrev ActionsChecksT := Array (Name × ActionChecksT)

/-- Generate the check theorem for the given invariant an `CheckType` (either `init` or `action`) -/
def getCheckFor (invName : Name) (ct : CheckType) (vs : Array Expr) : TermElabM SingleCheckT := do
  let env ← getEnv
  let .some _ := env.find? invName
    | throwError s!"Invariant {invName} not found"
  let inv ← Term.mkConst invName

  let (systemTp, stateTp, st, st') := (← getSystemTpStx vs, ← getStateTpStx vs, mkIdent `st, mkIdent `st')
  let property ← PrettyPrinter.delab $ mkAppN inv vs

  let (tpStx, thName, proofScript) ← match ct with
  | .init => do
      let initTpStx ← `(∀ ($st : $stateTp), ($systemTp).$(mkIdent `init)  $st → $property $st)
      let initThmName := s!"init_{invName}".toName
      let proofScript ← `(by unhygienic intros; solve_clause [$(mkIdent `initSimp)])
      pure (initTpStx, initThmName, proofScript)
  | .action actName => do
      let .some _ := (← getEnv).find? actName
        | throwError s!"action {actName} not found"
      let act ← Term.mkConst actName
      let actStx ← PrettyPrinter.delab $ mkAppN act vs
      let actTpStx ← `(∀ ($st $st' : $stateTp), ($systemTp).$(mkIdent `inv) $st → $actStx $st $st' → $property $st')
      let actThName := s!"{actName}_{invName}".toName
      let actId := Lean.mkIdent actName
      let proofScript ← `(by unhygienic intros; solve_clause [$actId])
      pure (actTpStx, actThName, proofScript)
  let checkTheorem ← `(@[invProof] theorem $(mkIdent thName) : $tpStx := $proofScript)
  let failedTheorem ← `(@[invProof] theorem $(mkIdent thName) : $tpStx := sorry)
  return (invName, (thName, checkTheorem, failedTheorem))

/--  Generate theorems to check in the initial state and after each action -/
def getAllChecks : CommandElabM (InitChecksT × ActionsChecksT) := do
  let (initChecks, actChecks) ← Command.runTermElabM fun vs => do
    let invNames := (← localSpecCtx.get).spec.invariants.map StateAssertion.name
    let actNames := ((<- localSpecCtx.get).spec.transitions).map (fun s => s.name)
    let mut initChecks := #[]
    let mut actChecks := #[]
    -- (1) Collect checks that invariants hold in the initial state
    for invName in invNames do
      initChecks := initChecks.push (← getCheckFor invName CheckType.init vs)
    -- (2) Collect checks that invariants hold after each action
    for actName in actNames do
        let mut checks := #[]
        for invName in invNames do
          checks := checks.push (← getCheckFor invName (CheckType.action actName) vs)
        actChecks := actChecks.push (actName, checks)
    pure (initChecks, actChecks)
  return (initChecks, actChecks)

/-- Generate theorems to check the given invariant clause in the initial
state and after each action. -/
def getChecksForInvariant (invName : Name) : CommandElabM (InitChecksT × ActionsChecksT) := do
  let (initChecks, actChecks) ← Command.runTermElabM fun vs => do
    let actNames := ((<- localSpecCtx.get).spec.transitions).map (fun s => s.name)
    let initChecks := #[← getCheckFor invName CheckType.init vs]
    let actChecks ← actNames.mapM fun actName => do
      let checks := #[← getCheckFor invName (CheckType.action actName) vs]
      return (actName, checks)
    pure (initChecks, actChecks)
  return (initChecks, actChecks)

/-- Generate therems to check all invariants after the given action. -/
def getChecksForAction (actName : Name) : CommandElabM (InitChecksT × ActionsChecksT) := do
  let (initChecks, actChecks) ← Command.runTermElabM fun vs => do
    let invNames := (← localSpecCtx.get).spec.invariants.map StateAssertion.name
    let invChecks ← invNames.mapM (fun invName => do return (← getCheckFor invName (CheckType.action actName) vs))
    pure (#[], #[(actName, invChecks)])
  return (initChecks, actChecks)

inductive CheckInvariantsBehaviour
  /-- `#check_invariants` -/
  | checkTheorems
  /-- `#check_invariants?` -/
  | printTheorems
  /-- `#check_invariants!` -/
  | printAndCheckTheorems

def checkTheorems (stx : Syntax) (initChecks : ActionChecksT) (actChecks : ActionsChecksT) (behaviour : CheckInvariantsBehaviour := .checkTheorems) : CommandElabM Unit := do
  let mut theorems := #[] -- collect Lean expression to report for `#check_invariants?` and `#check_invariants!`
  match behaviour with
  | .printTheorems =>
    let actInvChecks := Array.flatten $ actChecks.map (fun (_, actChecks) => actChecks)
    for (_, (_, thCmd, _)) in (initChecks ++ actInvChecks) do
      theorems := theorems.push thCmd
    displaySuggestion stx theorems
  | .checkTheorems | .printAndCheckTheorems =>
    let mut msgs := #[]
    if !initChecks.isEmpty then
      msgs := msgs.push "Initialization must establish the invariant:"
    for (invName, (thName, thCmd, sorryThm)) in initChecks do
      let success ← checkTheorem thName thCmd
      msgs := msgs.push s!"  {invName} ... {if success then "✅" else "❌"}"
      let thm := if success then thCmd else sorryThm
      theorems := theorems.push thm
    if !actChecks.isEmpty then
      msgs := msgs.push "The following set of actions must preserve the invariant:"
    for (actName, invChecks) in actChecks do
      msgs := msgs.push s!"  {actName}"
      for (invName, (thName, thCmd, sorryThm)) in invChecks do
        let success ← checkTheorem thName thCmd
        msgs := msgs.push s!"    {invName} ... {if success then "✅" else "❌"}"
        let thm := if success then thCmd else sorryThm
        theorems := theorems.push thm
    let msg := (String.intercalate "\n" msgs.toList) ++ "\n"
    match behaviour with
    | .checkTheorems => dbg_trace msg
    | .printAndCheckTheorems => displaySuggestion stx theorems (preMsg := msg)
    | _ => unreachable!
  where displaySuggestion (stx : Syntax) (theorems : Array (TSyntax `command)) (preMsg : Option String := none) := do
    Command.liftTermElabM do
    let cmd ← constructCommands theorems
    let suggestion : Suggestion := {
      suggestion := cmd
      preInfo? := preMsg
      toCodeActionTitle? := .some (fun _ => "Replace with explicit proofs.")
    }
    addSuggestion stx suggestion (header := "")

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
