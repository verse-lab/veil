import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Module.VCGen

open Lean Elab Command

namespace Veil

abbrev ReachableInvariantSubstitutions := Std.HashMap Name Term

private def parseReachableInvariantSubstitution
    (stx : TSyntax `reachableInvariantSubstitution) :
    CommandElabM (Name × Term) := do
  match stx with
  | `(reachableInvariantSubstitution| $id:ident := $term:term) =>
      return (id.getId, term)
  | _ => throwUnsupportedSyntax

private def parseReachableInvariantSubstitutions
    (substs : Array (TSyntax `reachableInvariantSubstitution)) :
    CommandElabM ReachableInvariantSubstitutions := do
  let mut result : ReachableInvariantSubstitutions := {}
  for subst in substs do
    let (name, term) ← parseReachableInvariantSubstitution subst
    if result.contains name then
      throwErrorAt subst "duplicate substitution for module sort {name}"
    result := result.insert name term
  return result

private def validateReachableInvariantSubstitutions
    (mod : Module) (substs : ReachableInvariantSubstitutions) : CommandElabM Unit := do
  let sortNames := Std.HashSet.ofArray mod.sortNames
  for (name, _) in substs.toArray do
    unless sortNames.contains name do
      throwError "#gen_reachable_invariants only supports substitutions for module sorts; `{name}` is not a sort parameter of module {mod.name}"

private def substitutedSortAssumptionNames (substs : ReachableInvariantSubstitutions) :
    Std.HashSet Name := Id.run do
  let mut names := Std.HashSet.emptyWithCapacity
  for (name, _) in substs.toArray do
    names := names.insert (name.appendAfter "_dec_eq")
    names := names.insert (name.appendAfter "_inhabited")
  return names

private def termMentionsAny (term : Term) (names : Std.HashSet Name) : Bool :=
  Option.isSome <| term.raw.find? fun stx => names.contains stx.getId

private def reachableInvariantBinders
    (mod : Module) (substs : ReachableInvariantSubstitutions) :
    CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let substitutedSorts := Std.HashSet.ofArray (substs.toArray.map (·.1))
  let substitutedSortAssumptions := substitutedSortAssumptionNames substs
  mod.parameters.filterMapM fun p => do
    match p.kind with
    | .sort _ =>
        if substitutedSorts.contains p.name then
          pure none
        else
          some <$> (mkImplicitBinder (← p.binder))
    | .userParameter =>
        some <$> (mkImplicitBinder (← p.binder))
    | .moduleTypeclass .sortAssumption =>
        if substitutedSortAssumptions.contains p.name then
          pure none
        else
          some <$> p.binder
    | .moduleTypeclass .userDefined =>
        if termMentionsAny p.type substitutedSorts then
          pure none
        else
          some <$> p.binder
    | _ =>
        pure none

private def uninterpretedArgsWithSubstitutions
    (mod : Module) (substs : ReachableInvariantSubstitutions) :
    CommandElabM (Array Term) := do
  mod.parameters.filterMapM fun p => do
    match p.kind with
    | .sort _ | .userParameter =>
        match substs[p.name]? with
        | some term => pure (some term)
        | none => pure (some (⟨mkIdent p.name⟩ : Term))
    | _ => pure none

private def trTheoremName (actName invName : Name) : Name :=
  Name.mkSimple s!"{actName}_{invName}_tr"

private def trTheoremNamesForAction (mod : Module) (actName : Name) : Array Name :=
  mod.invariants.map fun inv => trTheoremName actName inv.name

private def initializerTrTheoremNames (mod : Module) : Array Name :=
  trTheoremNamesForAction mod initializerName

private def actionTrTheoremNames (mod : Module) : Array Name :=
  mod.actions.flatMap fun act => trTheoremNamesForAction mod act.name

private def ensureTheoremAvailable (name : Name) : CommandElabM Unit := do
  try
    discard <| liftTermElabM <| resolveGlobalConstNoOverloadCore name
  catch _ =>
    throwError "missing theorem `{name}` required by #gen_reachable_invariants; make sure the defining module ran #check_invariants and #gen_theorems"

private def ensureRequiredTheoremsAvailable (mod : Module) : CommandElabM Unit := do
  for name in initializerTrTheoremNames mod ++ actionTrTheoremNames mod do
    ensureTheoremAvailable name

private def mkRelationalTransitionSystemTerm
    (mod : Module) (substs : ReachableInvariantSubstitutions) : CommandElabM Term := do
  let args ← uninterpretedArgsWithSubstitutions mod substs
  `(term| $(mkIdent assembledRTSName) $args*)

private def mkSpecializedTheoryTerm
    (mod : Module) (substs : ReachableInvariantSubstitutions) : CommandElabM Term := do
  let args ← uninterpretedArgsWithSubstitutions mod substs
  `(term| $(mkIdent theoryName) $args*)

private def mkSpecializedFieldAbstractTerm
    (mod : Module) (substs : ReachableInvariantSubstitutions) : CommandElabM Term := do
  let args ← uninterpretedArgsWithSubstitutions mod substs
  `(term| $(mkIdent fieldAbstractDispatcherName) $args*)

private def mkSpecializedStateTerm
    (mod : Module) (substs : ReachableInvariantSubstitutions) : CommandElabM Term := do
  let fieldTerm ← mkSpecializedFieldAbstractTerm mod substs
  `(term| $(mkIdent stateName) $fieldTerm)

private def mkNamedTermArg
    (name : Name) (term : Term) :
    CommandElabM (TSyntax `Lean.Parser.Term.namedArgument) :=
  `(Lean.Parser.Term.namedArgument| ($(mkIdent name) := $term:term))

private def mkAppWithNamedAndPositionalArgs
    (name : Name) (namedArgs : Array (TSyntax `Lean.Parser.Term.namedArgument))
    (positionalArgs : Array Term) : Term :=
  let args := namedArgs.map (·.raw) ++ positionalArgs.map (·.raw)
  ⟨mkNode `Lean.Parser.Term.app #[mkIdent name, mkNullNode args]⟩

private def mkSpecializedDeclarationNamedArgs
    (mod : Module) (substs : ReachableInvariantSubstitutions)
    : CommandElabM (Array (TSyntax `Lean.Parser.Term.namedArgument)) := do
  let theoryTerm ← mkSpecializedTheoryTerm mod substs
  let stateTerm ← mkSpecializedStateTerm mod substs
  let fieldTerm ← mkSpecializedFieldAbstractTerm mod substs
  let mut args := #[]
  args := args.push (← mkNamedTermArg environmentTheoryName theoryTerm)
  args := args.push (← mkNamedTermArg environmentStateName stateTerm)
  for p in mod.parameters do
    match p.kind with
    | .sort _ | .userParameter =>
        let term ← match substs[p.name]? with
          | some term => pure term
          | none => pure (⟨mkIdent p.name⟩ : Term)
        args := args.push (← mkNamedTermArg p.name term)
    | _ => pure ()
  args := args.push (← mkNamedTermArg fieldConcreteTypeName fieldTerm)
  return args

private def mkInvariantsPredicate
    (mod : Module) (substs : ReachableInvariantSubstitutions) : CommandElabM Term := do
  let namedArgs ← mkSpecializedDeclarationNamedArgs mod substs
  let th := mkIdent `th
  let st := mkIdent `st
  let body := mkAppWithNamedAndPositionalArgs assembledInvariantsName namedArgs
    #[(⟨th⟩ : Term), (⟨st⟩ : Term)]
  `(term| fun $th:ident $st:ident => $body)

private def mkInvariantPredicate
    (mod : Module) (substs : ReachableInvariantSubstitutions) (invName : Name) :
    CommandElabM Term := do
  let namedArgs ← mkSpecializedDeclarationNamedArgs mod substs
  let th := mkIdent `th
  let st := mkIdent `st
  let body := mkAppWithNamedAndPositionalArgs invName namedArgs
    #[(⟨th⟩ : Term), (⟨st⟩ : Term)]
  `(term| fun $th:ident $st:ident => $body)

private def mkGeneratedInvariantTheoremName : Name :=
  assembledInvariantsName ++ `is_inv

private def mkSpecializedTrTheoremTerm
    (mod : Module) (substs : ReachableInvariantSubstitutions)
    (theoremName : Name) (positionalArgs : Array Term) : CommandElabM Term := do
  let namedArgs ← mkSpecializedDeclarationNamedArgs mod substs
  pure <| mkAppWithNamedAndPositionalArgs theoremName namedArgs positionalArgs

private def mkInitPreservationProofArm
    (mod : Module) (substs : ReachableInvariantSubstitutions)
    (theoremName : Name) : CommandElabM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  let hpresTerm ← mkSpecializedTrTheoremTerm mod substs theoremName #[]
  `(tacticSeq|
    have hpres := $hpresTerm
    unfold $(mkIdent ``Transition.meetsSpecificationIfSuccessfulAssuming)
      $(mkIdent ``Transition.meetsSpecificationIfSuccessful)
      $(mkIdent ``Transition.triple) at hpres
    exact hpres th default s ⟨has, trivial⟩ (by
      simp only [nextSimp]
      exact hinit))

private def mkActionPreservationProofArm
    (mod : Module) (substs : ReachableInvariantSubstitutions)
    (theoremName : Name) (actionArgs : Array Ident) :
    CommandElabM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  let actionTerms := actionArgs.map fun id => (⟨id⟩ : Term)
  let hpresTerm ← mkSpecializedTrTheoremTerm mod substs theoremName actionTerms
  `(tacticSeq|
    have hpres := $hpresTerm
    unfold $(mkIdent ``Transition.meetsSpecificationIfSuccessfulAssuming)
      $(mkIdent ``Transition.meetsSpecificationIfSuccessful)
      $(mkIdent ``Transition.triple) at hpres
    exact hpres th s s' ⟨has, ih⟩ (by
      simp only [nextSimp]
      exact htr))

private partial def mkConjunctionProof
    (proofs : Array (TSyntax `Lean.Parser.Tactic.tacticSeq)) :
    CommandElabM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  match proofs[0]? with
  | none => `(tacticSeq| trivial)
  | some proof =>
      if proofs.size == 1 then
        pure proof
      else
        let rest := proofs.extract 1 proofs.size
        let restProof ← mkConjunctionProof rest
        let proofTac ← `(tactic| ($proof:tacticSeq))
        let restProofTac ← `(tactic| ($restProof:tacticSeq))
        `(tacticSeq|
          constructor
          · $proofTac:tactic
          · $restProofTac:tactic)

private def mkActionCaseAlt
    (mod : Module) (substs : ReachableInvariantSubstitutions)
    (act : ProcedureSpecification) :
    CommandElabM (TSyntax `Lean.Parser.Tactic.inductionAlt) := do
  let actionArgs := act.params.map fun p => mkIdent p.name
  let proofArms ← mod.invariants.mapM fun inv =>
    mkActionPreservationProofArm mod substs (trTheoremName act.name inv.name) actionArgs
  let conjunctionProof ← mkConjunctionProof proofArms
  let conjunctionProofTac ← `(tactic| ($conjunctionProof:tacticSeq))
  `(Lean.Parser.Tactic.inductionAlt|
    | $(mkIdent act.name):ident $actionArgs:ident* =>
        simp only [nextSimp] at htr
        dsimp [$(mkIdent assembledInvariantsName):ident]
        $conjunctionProofTac:tactic)

private def mkActionCasesTactic
    (mod : Module) (substs : ReachableInvariantSubstitutions) :
    CommandElabM (TSyntax `tactic) := do
  let alts ← mod.actions.mapM fun act => mkActionCaseAlt mod substs act
  `(tactic| cases label with $[$alts]*)

private def invariantHypIdent (invName : Name) : Ident :=
  mkIdent (Name.mkSimple s!"h_{invName.getString!}")

private def mkProjectionDestructProof
    (mod : Module) (invName : Name) :
    CommandElabM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  if mod.invariants.size == 1 then
    `(tacticSeq| exact h)
  else
    let hNames := mod.invariants.map fun inv => invariantHypIdent inv.name
    let hTarget := invariantHypIdent invName
    `(tacticSeq|
      rcases h with ⟨ $[$hNames],* ⟩
      exact $hTarget:ident)

private def mkReachableInvariantsTheorem
    (mod : Module) (binders : Array (TSyntax `Lean.Parser.Term.bracketedBinder))
    (substs : ReachableInvariantSubstitutions) (rtsTerm : Term) : CommandElabM Command := do
  let initProofArms ← (initializerTrTheoremNames mod).mapM fun thm =>
    mkInitPreservationProofArm mod substs thm
  let initConjunctionProof ← mkConjunctionProof initProofArms
  let initConjunctionProofTac ← `(tactic| ($initConjunctionProof:tacticSeq))
  let actionCases ← mkActionCasesTactic mod substs
  let invPredicate ← mkInvariantsPredicate mod substs
  let thmName := mkIdent mkGeneratedInvariantTheoremName
  `(command|
    open Classical in
    theorem $thmName $[$binders]* :
        $(mkIdent ``RelationalTransitionSystem.isInvariant) $rtsTerm $invPredicate := by
      intro th st hr
      induction hr with
      | init s has hinit =>
          simp only [nextSimp] at hinit
          dsimp [$(mkIdent assembledInvariantsName):ident]
          $initConjunctionProofTac:tactic
      | step s s' hreach hnext ih =>
          have has := $(mkIdent ``RelationalTransitionSystem.reachable_assumptions) _ _ _ hreach
          rcases hnext with ⟨label, htr⟩
          $actionCases:tactic)

private def mkProjectionTheorem
    (mod : Module) (binders : Array (TSyntax `Lean.Parser.Term.bracketedBinder))
    (substs : ReachableInvariantSubstitutions) (rtsTerm : Term)
    (invName : Name) : CommandElabM Command := do
  let thmName := mkIdent (invName ++ `is_inv)
  let invPredicate ← mkInvariantPredicate mod substs invName
  let destructProof ← mkProjectionDestructProof mod invName
  let destructTactic ← `(tactic| ($destructProof:tacticSeq))
  `(command|
    open Classical in
    theorem $thmName $[$binders]* :
        $(mkIdent ``RelationalTransitionSystem.isInvariant) $rtsTerm $invPredicate := by
      intro th st hr
      have h := $(mkIdent mkGeneratedInvariantTheoremName) th st hr
      dsimp [$(mkIdent assembledInvariantsName):ident] at h
      $destructTactic:tactic)

def Module.generateReachableInvariantTheorems
    (mod : Module) (substs : ReachableInvariantSubstitutions) : CommandElabM Unit := do
  mod.throwIfSpecNotFinalized
  validateReachableInvariantSubstitutions mod substs
  ensureRequiredTheoremsAvailable mod
  let binders ← reachableInvariantBinders mod substs
  let rtsTerm ← mkRelationalTransitionSystemTerm mod substs
  elabCommand (← mkReachableInvariantsTheorem mod binders substs rtsTerm)
  for inv in mod.invariants do
    elabCommand (← mkProjectionTheorem mod binders substs rtsTerm inv.name)

def elabGenReachableInvariantsCommand (stx : Syntax) : CommandElabM Unit := do
  let mod ← getCurrentModule (errMsg := "You cannot #gen_reachable_invariants outside of a Veil module!")
  match stx with
  | `(command| #gen_reachable_invariants) =>
      mod.generateReachableInvariantTheorems {}
  | `(command| #gen_reachable_invariants with $substs:reachableInvariantSubstitution,*) =>
      mod.generateReachableInvariantTheorems (← parseReachableInvariantSubstitutions substs)
  | _ => throwUnsupportedSyntax

end Veil
