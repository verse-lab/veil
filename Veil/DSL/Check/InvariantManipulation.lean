import Lean
import Veil.Tactic.Main
import Veil.DSL.Check.Main

open Lean Elab Command Term Meta Lean.Parser Tactic.TryThis Lean.Core

def mkTheoremFullActionName (actName : Name) (invName : Name) : Name := s!"{actName}_{invName.components.getLast!}".toName
def mkTrTheoremName (actName : Name) (invName : Name) : Name := s!"{actName.components.getLast!}.tr_{invName.components.getLast!}".toName

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
        let thmName := mkTrTheoremName actName invName
        let thm ← `(@[invProof] theorem $(mkIdent thmName) : $tp := by $body)
        trace[veil.debug] "{thm}"
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
  let thmName := if trName == `init then mkTheoremName trName invName else mkTheoremFullActionName trName invName
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

-- NOTE: when run this, the user must (1) have proven `inv_inductive` using `prove_inv_inductive`
-- and (2) ensure that the assumptions of the protocol are trivial (e.g., by putting assumptions into a typeclass)
elab "#split_invariants" : command => do
  let allClauses := (← localSpecCtx.get).spec.invariants
  if allClauses.isEmpty then return

  let (tempvars, thmType, subThmTypes) ← Command.runTermElabM fun vs => do
    let allClauses := (← localSpecCtx.get).spec.invariants
    let allClauses := allClauses.toList
    let invExprs := allClauses.map (fun x => mkAppN x.expr vs)
    let invNames := allClauses.map StateAssertion.name
    -- need to reverse. kind of weird
    let invExprs := invExprs.reverse
    let invNames := invNames.reverse
    let invExprs ← invExprs.mapM (fun x => mkAppM ``RelationalTransitionSystem.isInvariant #[x])
    let invConj := mkAndN invExprs
    let thmType ← mkForallFVars vs invConj
    let subThmTypes ← invExprs.mapM (fun x => mkForallFVars vs x)
    -- need to instantiate mvar
    let thmType ← instantiateMVars thmType
    let subThmTypes ← subThmTypes.mapM instantiateMVars
    let tempvars ← vs.mapM (fun x => x.fvarId!.getUserName)
    pure (tempvars, thmType, invNames.zip subThmTypes)

  let moduleName ← getCurrNamespace

  -- prove the conjunction first
  let conjunctionThmName := moduleName ++ `inv_split_base
  Command.liftTermElabM do
    let thmName1 := ``RelationalTransitionSystem.invariant_merge
    let thmName2 := ``RelationalTransitionSystem.invInductive_to_isInvariant
    let thmName3 := `inv_inductive
    simpleAddThm conjunctionThmName thmType
      `(tacticSeq|
        intros ; repeat rw [@$(mkIdent thmName1):ident]
        apply $(mkIdent thmName2)
        next => intro _ _ ; simp [invSimp]
        next => apply $(mkIdent thmName3))

  -- then prove all sub invariants
  for (invName, subThmType) in subThmTypes do
    let subThmName := moduleName ++ invName ++ `is_inv
    Command.liftTermElabM do
      -- FIXME: better solution?
      let tempvars := tempvars.map Lean.mkIdent
      let thmName1 := `inv_split_base
      simpleAddThm subThmName subThmType
        `(tacticSeq|
          intro $tempvars* ; have hh := @$(mkIdent thmName1) $tempvars*
          revert hh ; simp only [and_imp] ; intros ; assumption
        )     -- avoid having a tactic spliting at hyp
