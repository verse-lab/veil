import Lean
import Veil.Util.DSL
import Veil.DSL.Specification.SpecDef
import Veil.Tactic.Main

open Lean Elab Command Term Meta Lean.Parser Tactic.TryThis Lean.Core

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
    let inv := mkIdent ``RelationalTransitionSystem.inv
    let invInit := mkIdent ``RelationalTransitionSystem.invInit
    `(theorem $(mkIdent `inv_init) : $invInit (σ := $stateTp) (ρ := $readerTp) $inv :=
       by unfold $invInit
          -- simp only [initSimp, invSimp]
          intros $(mkIdent `rd) $(mkIdent `st)
          exact $proof)

elab "prove_inv_safe" proof:term : command => do
  liftCoreM errorOrWarnWhenSpecIsNeeded
  elabCommand $ <- Command.runTermElabM fun _ => do
    let stateTp <- getStateTpStx
    let readerTp <- getReaderTpStx
    let invSafe := mkIdent ``RelationalTransitionSystem.invSafe
    `(theorem $(mkIdent `safety_init) : $invSafe (σ := $stateTp) (ρ := $readerTp) :=
       by unfold $invSafe
          -- simp only [initSimp, safeSimp]
          intros $(mkIdent `rd) $(mkIdent `st)
          exact $proof)

elab "prove_inv_inductive" proof:term : command => do
  liftCoreM errorOrWarnWhenSpecIsNeeded
  elabCommand $ <- Command.runTermElabM fun _ => do
    let stateTp <- getStateTpStx
    let readerTp <- getReaderTpStx
    let invInductive := mkIdent ``RelationalTransitionSystem.isInductive
    let inv := mkIdent ``RelationalTransitionSystem.inv
    `(theorem $invInductiveIdent : $invInductive (σ := $stateTp) (ρ := $readerTp) $inv :=
      by unfold $invInductive;
        --  intros $(mkIdent `st) $(mkIdent `st')
        --  simp only [actSimp, invSimp, safeSimp]
         exact $proof)

/-- Generates the theorem that the conjunction of all clauses is an
inductive invariant. This also generates the theorem that the
conjunction of all invariant clauses is an invariant.

Call this only if the appropriate sub-theorems have been proven in
`transition` style semantics. -/
def genInductiveInvariantTheorem : CommandElabM Unit := do
  liftCoreM errorOrWarnWhenSpecIsNeeded
  let vd ← getNonGenericStateParameters
  let (invInductive, invInv) ← Command.runTermElabM fun _ => do
    let stateTp <- getStateTpStx
    let readerTp <- getReaderTpStx
    let isInductive := mkIdent ``RelationalTransitionSystem.isInductive
    let inv := mkIdent ``RelationalTransitionSystem.inv
    let invInductive ← `(theorem $invInductiveIdent $[$vd]* : $isInductive (σ := $stateTp) (ρ := $readerTp) $inv := by
    constructor
    . intro rd st has $(mkIdent `hinit)
      sdestruct_goal <;> already_proven_init
    . intro rd st st' has $(mkIdent `hinv) $(mkIdent `hnext)
      sts_induction <;> sdestruct_goal <;> already_proven_next_tr)
    trace[veil.debug] invInductive

    let isInvariant := mkIdent ``RelationalTransitionSystem.isInvariant
    let invInv ← `(theorem $(mkIdent $ propInvariantName `inv) $[$vd]* : $isInvariant (σ := $stateTp) (ρ := $readerTp) $inv := by
      apply $(mkIdent ``RelationalTransitionSystem.inductive_is_invariant); apply $invInductiveIdent)
    return (invInductive, invInv)
  let moduleName ← getCurrNamespace
  if (← resolveGlobalName (moduleName ++ invInductiveName)).isEmpty then
    elabCommand invInductive
  elabCommand invInv

def genInvariantTheorems : CommandElabM Unit := do
  liftCoreM errorOrWarnWhenSpecIsNeeded
  let vd ← getNonGenericStateParameters
  let cmds ← Command.runTermElabM fun vs => do
    let stateTp <- getStateTpStx
    let readerTp <- getReaderTpStx
    let isInvariant := mkIdent ``RelationalTransitionSystem.isInvariant
    let allClauses := (← localSpecCtx.get).spec.invariants
    let topLevelArgs ← getNonGenericStateAndReaderArguments (← getSectionArgumentsStx vs)
    let assertionArgs ← getSectionArgumentsStxWithConcreteState vs
    let mut cmds := #[]
    for clause in allClauses do
      let clauseName := stripFirstComponent clause.name
      let inv ← `(@$(mkIdent clause.name) $assertionArgs*)
      let invInv ← `(theorem $(mkIdent $ propInvariantName clauseName) $[$vd]* : $isInvariant (σ := $stateTp) (ρ := $readerTp) $inv := by
        have hx := @$(mkIdent $ propInvariantName `inv) $topLevelArgs*; revert hx
        simp only [$(mkIdent `invSimpTopLevel):ident]; unfold $(mkIdent `Invariant)
        simp only [← $(mkIdent ``RelationalTransitionSystem.invariant_merge):ident, $(mkIdent ``and_imp):ident]
        intros; assumption)
      cmds := cmds.push invInv
    return cmds
  for cmd in cmds do
    trace[veil.debug] cmd
    elabCommand cmd

def generateAuxiliaryTheorems : CommandElabM Unit := do
  genInductiveInvariantTheorem
  genInvariantTheorems

elab "#gen_auxiliary_theorems" : command => do
  generateAuxiliaryTheorems
