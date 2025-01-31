import Lean
import Veil.Tactic
import Veil.DSL.Check

open Lean Elab Command Term Meta Lean.Parser Tactic.TryThis Lean.Core

-- adapted from `theoremSuggestionsForChecks`
def theoremSuggestionsForChecks' (initIndicators : List Name) (actIndicators : List (Name × Name)) (vcStyle : VCGenStyle) (sorry_body: Bool := true): CommandElabM (Array (TheoremIdentifier × TSyntax `command)) := do
    Command.runTermElabM fun vs => do
      let (systemTp, stateTp, st, st') := (← getSystemTpStx vs, ← getStateTpStx, mkIdent `st, mkIdent `st')
      let sectionArgs ← getSectionArgumentsStx vs
      let mut theorems : Array (TheoremIdentifier × TSyntax `command) := #[]
      -- Action checks
      for (actName, invName) in actIndicators.reverse do
        let (tp, body) ← do
          let trName := toTrName actName
          let invStx ← `(@$(mkIdent invName) $sectionArgs*)
          let trStx ← `(@$(mkIdent trName) $sectionArgs*)
          let trTpSyntax ← `(∀ ($st $st' : $stateTp), ($systemTp).$(mkIdent `assumptions) $st → ($systemTp).$(mkIdent `inv) $st → $trStx $st $st' → $invStx $st')

          let extName := toExtName actName
          let moduleName <- getCurrNamespace
          let some args := (<- localSpecCtx.get).spec.actions.find? (moduleName ++ ·.name == actName)
            | throwError s!"action {actName} not found"
          let (univBinders, args) ← match args.br with
          | some br => pure (← toBracketedBinderArray br, ← existentialIdents br)
          | none => pure (#[], #[])

          let body ← do
            let name1 := actName ++ `act_tr_eq
            let name2 := mkTheoremName actName invName
            let name3 := `forall_exists_index
            let name4 := `triple_sound'_ret_unit'
            `(tacticSeq|
              rw [← $(mkIdent name1)] ; dsimp
              (try simp only [$(mkIdent name3):ident])
              have h := @$(mkIdent name2) $sectionArgs*
              intro st st' hassu hinv $args*
              specialize h st ; specialize h $args* ; specialize h hassu hinv
              have hthis := $(mkIdent name4):ident _ h
              apply hthis)
          pure (trTpSyntax, body)
        let thmName := mkTheoremName (toTrName actName) invName
        let thm ← `(@[invProof] theorem $(mkIdent thmName) : $tp := by $body)
        theorems := theorems.push (⟨invName, .some actName, thmName⟩, thm)
      return theorems

-- adapted from `theoremSuggestionsForIndicators`; the only change is to call `theoremSuggestionsForChecks'` instead of the `'`-free one
def theoremSuggestionsForIndicators' (generateInitThms : Bool) (actIndicators invIndicators : List (Name × Expr)) (vcStyle : VCGenStyle) : CommandElabM (Array (TheoremIdentifier × TSyntax `command)) := do
  let (initIndicators, acts) ← Command.runTermElabM fun _ => do
    -- prevent code duplication
    let initIndicators ← invIndicators.mapM (fun (invName, _) => resolveGlobalConstNoOverloadCore invName)
    let actIndicators ← actIndicators.mapM (fun (actName, _) => resolveGlobalConstNoOverloadCore actName)
    let mut acts := #[]
    for actName in actIndicators do
      for invName in initIndicators do
        acts := acts.push (actName, invName)
    return (initIndicators, acts)
  theoremSuggestionsForChecks' (if generateInitThms then initIndicators else []) acts.toList vcStyle (sorry_body := False)

-- adapted from `checkInvariants` and `checkTheorems`
-- FIXME: enhance this function, and all related functions, by handling error better, avoiding repeating code, etc.
def recoverInvariantsInTrStyle : CommandElabM Unit := do
  let (_, invChecks) ← getAllChecks
  let actIndicators := (invChecks.map (fun (_, (act_name, ind_name)) => (act_name, ind_name))).toList.removeDuplicates
  let invIndicators := (invChecks.map (fun ((inv_name, ind_name), _) => (inv_name, ind_name))).toList.removeDuplicates
  let allTheorems ← theoremSuggestionsForIndicators' false actIndicators invIndicators .transition
  for (thmId, cmd) in allTheorems do
    elabCommand (← `(#guard_msgs(drop warning) in $(cmd)))

syntax "#recover_invariants_in_tr" : command

elab_rules : command
  | `(command| #recover_invariants_in_tr)  => recoverInvariantsInTrStyle

open Tactic in
def elabAlreadyProven (trName : Name) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let ty ← g.getType
  let ty ← instantiateMVars ty      -- this is usually required
  let inv := ty.getAppFn'
  let .some (invName, _) := inv.const? | throwError "the goal {ty} is not about an invariant clause? got {inv}, expect it to be a const"
  let thmName := mkTheoremName trName invName
  let attempt ← `(tactic| (apply $(mkIdent thmName) <;> assumption) )
  evalTactic attempt

elab "already_proven_init" : tactic => elabAlreadyProven `init

open Tactic in
elab "already_proven_next_tr" : tactic => withMainContext do
  -- being slightly smart
  let .some ld := (← getLCtx).findFromUserName? `hnext | throwError "cannot find hnext!"
  let tr := ld.type.getAppFn'
  let .some (trName, _) := tr.const? | throwError "hnext is not a premise about .tr? got {tr}, expect it to be a .tr"
  elabAlreadyProven trName
