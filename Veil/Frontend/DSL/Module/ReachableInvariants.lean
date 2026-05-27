import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Module.VCGen

open Lean Elab Command

namespace Veil

private def generatedInvariantsTheoremName : Name :=
  assembledInvariantsName ++ `is_inv

/-! ## Substitution Parsing & Validation -/

private def parseReachableInvariantSubstitutions
    (substs : Array (TSyntax `reachableInvariantSubstitution)) :
    CommandElabM ParameterSubst := do
  let mut result : ParameterSubst := {}
  for stx in substs do
    match stx with
    | `(reachableInvariantSubstitution| $id:ident := $term:term) =>
        let name := id.getId
        if result.contains name then
          throwErrorAt stx "duplicate substitution for module sort {name}"
        result := result.insert name term
    | _ => throwUnsupportedSyntax
  return result

private def validateReachableInvariantSubstitutions
    (mod : Module) (substs : ParameterSubst) : CommandElabM Unit := do
  let sortNames := Std.HashSet.ofArray mod.sortNames
  for (name, _) in substs do
    unless sortNames.contains name do
      throwError "#gen_reachable_invariants only supports substitutions for module sorts; \
        `{name}` is not a sort parameter of module {mod.name}"

/-! ## TR-Theorem Availability Check -/

private def ensureTheoremAvailable (name : Name) : CommandElabM Unit := do
  try
    discard <| liftTermElabM <| resolveGlobalConstNoOverloadCore name
  catch _ =>
    throwError "missing theorem `{name}` required by #gen_reachable_invariants; \
      make sure the defining module ran #check_invariants and #gen_theorems"

private def ensureRequiredTheoremsAvailable (mod : Module) : CommandElabM Unit := do
  for inv in mod.invariants do
    ensureTheoremAvailable (trTheoremName initializerName inv.name)
    for act in mod.actions do
      ensureTheoremAvailable (trTheoremName act.name inv.name)

/-! ## Generation Context -/

private structure GenCtx where
  mod : Module
  substs : ParameterSubst
  /-- Implicit binders surrounding both the outer and projection theorems
  (sorts/userParams as implicit, typeclass instances as `[ ]`). -/
  binders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)
  /-- Named-arg list `(ρ := Theory ⟨sorts⟩)(σ := State ⟨...⟩)(<sortName> := <subst>)…(χ := …)`
  used to instantiate the system-bound parameters at every call site. -/
  namedArgs : Array (TSyntax `Lean.Parser.Term.namedArgument)
  /-- The fully-applied `assembledRTS` term used in the theorem statement. -/
  rtsTerm : Term

/-- Build `head <uninterpretedArgs>` for definitions parameterized only by
sorts/userParameters (e.g. `Theory`, `FieldAbstractType`, `assembledRTS`). -/
private def mkUninterpretedApp (uninterpretedArgs : Array Term) (head : Name) :
    CommandElabM Term :=
  `(term| $(mkIdent head) $uninterpretedArgs*)

private def mkNamedArg (name : Name) (term : Term) :
    CommandElabM (TSyntax `Lean.Parser.Term.namedArgument) :=
  `(Lean.Parser.Term.namedArgument| ($(mkIdent name) := $term:term))

/-- Apply a head `name` to a mix of named and positional args. Lean's
quotation syntax can mix the two inside a `term|`, but only for a fixed
shape; for dynamically-sized arrays we hand-build the `Term.app` node. -/
private def mkAppWithNamedAndPositionalArgs
    (name : Name) (namedArgs : Array (TSyntax `Lean.Parser.Term.namedArgument))
    (positionalArgs : Array Term) : Term :=
  let args := namedArgs.map (·.raw) ++ positionalArgs.map (·.raw)
  ⟨mkNode `Lean.Parser.Term.app #[mkIdent name, mkNullNode args]⟩

private def mkGenCtx (mod : Module) (substs : ParameterSubst) : CommandElabM GenCtx := do
  -- Binders: sorts/userParams become implicit; typeclass binders are kept
  -- unless they're substituted away or their type depends on a substituted
  -- sort (in which case Lean re-synthesizes the instance at the call site).
  let binders ← mod.parameters.filterMapM fun p => do
    match p.kind with
    | .sort _ | .userParameter =>
        match ← p.binderSubst? substs with
        | some b => some <$> mkImplicitBinder b
        | none => pure none
    | .moduleTypeclass .sortAssumption | .moduleTypeclass .userDefined =>
        p.binderSubst? substs
    | _ => pure none
  -- Args for sort/userParameter positions, after substitution.
  let uninterpretedArgs ← mod.parameters.filterMapM fun p => do
    match p.kind with
    | .sort _ | .userParameter => some <$> p.argSubst substs
    | _ => pure none
  -- Concrete instantiations for the system-bound parameters (ρ, σ, χ).
  -- `theoryName`, `fieldAbstractDispatcherName`, and `stateName` aren't
  -- registered as derived definitions, so we apply them positionally to
  -- the uninterpreted args. The RTS *is* registered (with `.stateLike`
  -- base + inhabited/user-defined extras), so we go through the registry.
  let theoryTerm ← mkUninterpretedApp uninterpretedArgs theoryName
  let fieldTerm ← mkUninterpretedApp uninterpretedArgs fieldAbstractDispatcherName
  let stateTerm ← `(term| $(mkIdent stateName) $fieldTerm)
  let rtsKind := DeclarationKind.derivedDefinition .stateLike
    (Std.HashSet.ofArray #[assembledAssumptionsName, assembledInitName, assembledNextName])
  let rtsArgs ← mod.declarationAllArgsSubst substs assembledRTSName rtsKind
  let rtsTerm ← `(term| @$(mkIdent assembledRTSName) $rtsArgs*)
  -- Build the named-arg list: ρ, σ, each sort/userParam, χ.
  let mut namedArgs := #[
    ← mkNamedArg environmentTheoryName theoryTerm,
    ← mkNamedArg environmentStateName stateTerm]
  for p in mod.parameters do
    match p.kind with
    | .sort _ | .userParameter =>
        namedArgs := namedArgs.push (← mkNamedArg p.name (← p.argSubst substs))
    | _ => pure ()
  namedArgs := namedArgs.push (← mkNamedArg fieldConcreteTypeName fieldTerm)
  return { mod, substs, binders, namedArgs, rtsTerm }

/-- Apply `head` (e.g. `assembledInvariantsName` or an individual `invName`)
to the system-bound named args, then to `th` and `st`, as a 2-arg predicate
`fun th st => @head <namedArgs>* th st`. -/
private def GenCtx.mkInvariantPredicate (ctx : GenCtx) (head : Name) : CommandElabM Term := do
  let th := mkIdent `th
  let st := mkIdent `st
  let body := mkAppWithNamedAndPositionalArgs head ctx.namedArgs
    #[(⟨th⟩ : Term), (⟨st⟩ : Term)]
  `(term| fun $th:ident $st:ident => $body)

/-! ## Preservation Proof Arms -/

private def GenCtx.mkTrTheoremApp
    (ctx : GenCtx) (actName invName : Name) (positional : Array Term) : Term :=
  mkAppWithNamedAndPositionalArgs (trTheoremName actName invName) ctx.namedArgs positional

private def mkInitArm (ctx : GenCtx) (invName : Name) :
    CommandElabM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  let hpresApp := ctx.mkTrTheoremApp initializerName invName (positional := #[])
  `(tacticSeq|
    have hpres := $hpresApp
    unfold $(mkIdent ``Transition.meetsSpecificationIfSuccessfulAssuming)
      $(mkIdent ``Transition.meetsSpecificationIfSuccessful)
      $(mkIdent ``Transition.triple) at hpres
    exact hpres th default s ⟨has, trivial⟩ (by
      simp only [nextSimp]
      exact hinit))

private def mkActionArm
    (ctx : GenCtx) (actName invName : Name) (actionArgs : Array Ident) :
    CommandElabM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  let positional := actionArgs.map fun id => (⟨id⟩ : Term)
  let hpresApp := ctx.mkTrTheoremApp actName invName (positional := positional)
  `(tacticSeq|
    have hpres := $hpresApp
    unfold $(mkIdent ``Transition.meetsSpecificationIfSuccessfulAssuming)
      $(mkIdent ``Transition.meetsSpecificationIfSuccessful)
      $(mkIdent ``Transition.triple) at hpres
    exact hpres th s s' ⟨has, ih⟩ (by
      simp only [nextSimp]
      exact htr))

/-- Combine per-invariant arms into a right-nested conjunction proof,
matching the layout of `repeatedAnd` in `assembleAssertions`. -/
private def mkConjunctionProof
    (proofs : Array (TSyntax `Lean.Parser.Tactic.tacticSeq)) :
    CommandElabM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  if proofs.isEmpty then return ← `(tacticSeq| trivial)
  proofs.pop.foldrM (init := proofs.back!) fun p acc =>
    `(tacticSeq|
      constructor
      · ($p:tacticSeq)
      · ($acc:tacticSeq))

/-! ## Step Case (action induction) -/

private def mkActionCaseAlt (ctx : GenCtx) (act : ProcedureSpecification) :
    CommandElabM (TSyntax `Lean.Parser.Tactic.inductionAlt) := do
  let actionArgs := act.params.map fun p => mkIdent p.name
  let arms ← ctx.mod.invariants.mapM fun inv => mkActionArm ctx act.name inv.name actionArgs
  let conjunction ← mkConjunctionProof arms
  let conjunctionTac ← `(tactic| ($conjunction:tacticSeq))
  `(Lean.Parser.Tactic.inductionAlt|
    | $(mkIdent act.name):ident $actionArgs:ident* =>
        simp only [nextSimp] at htr
        dsimp [$(mkIdent assembledInvariantsName):ident]
        $conjunctionTac:tactic)

private def mkActionCasesTactic (ctx : GenCtx) : CommandElabM (TSyntax `tactic) := do
  let alts ← ctx.mod.actions.mapM (mkActionCaseAlt ctx)
  `(tactic| cases label with $[$alts]*)

/-! ## Outer Theorem -/

private def mkReachableInvariantsTheorem (ctx : GenCtx) : CommandElabM Command := do
  let initArms ← ctx.mod.invariants.mapM fun inv => mkInitArm ctx inv.name
  let initConjunction ← mkConjunctionProof initArms
  let initConjunctionTac ← `(tactic| ($initConjunction:tacticSeq))
  let actionCases ← mkActionCasesTactic ctx
  let invPredicate ← ctx.mkInvariantPredicate assembledInvariantsName
  let thmName := mkIdent generatedInvariantsTheoremName
  let binders := ctx.binders
  let rtsTerm := ctx.rtsTerm
  `(command|
    open Classical in
    theorem $thmName $[$binders]* :
        $(mkIdent ``RelationalTransitionSystem.isInvariant) $rtsTerm $invPredicate := by
      intro th st hr
      induction hr with
      | init s has hinit =>
          simp only [nextSimp] at hinit
          dsimp [$(mkIdent assembledInvariantsName):ident]
          $initConjunctionTac:tactic
      | step s s' hreach hnext ih =>
          have has := $(mkIdent ``RelationalTransitionSystem.reachable_assumptions) _ _ _ hreach
          rcases hnext with ⟨label, htr⟩
          $actionCases:tactic)

/-! ## Projection Theorems -/

private def invariantHypIdent (invName : Name) : Ident :=
  mkIdent (Name.mkSimple s!"h_{invName.getString!}")

private def mkProjectionDestructProof (mod : Module) (invName : Name) :
    CommandElabM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  if mod.invariants.size == 1 then
    `(tacticSeq| exact h)
  else
    let hNames := mod.invariants.map fun inv => invariantHypIdent inv.name
    let hTarget := invariantHypIdent invName
    `(tacticSeq|
      rcases h with ⟨ $[$hNames],* ⟩
      exact $hTarget:ident)

private def mkProjectionTheorem (ctx : GenCtx) (invName : Name) : CommandElabM Command := do
  let thmName := mkIdent (invName ++ `is_inv)
  let invPredicate ← ctx.mkInvariantPredicate invName
  let destructProof ← mkProjectionDestructProof ctx.mod invName
  let destructTac ← `(tactic| ($destructProof:tacticSeq))
  let binders := ctx.binders
  let rtsTerm := ctx.rtsTerm
  `(command|
    open Classical in
    theorem $thmName $[$binders]* :
        $(mkIdent ``RelationalTransitionSystem.isInvariant) $rtsTerm $invPredicate := by
      intro th st hr
      have h := $(mkIdent generatedInvariantsTheoremName) th st hr
      dsimp [$(mkIdent assembledInvariantsName):ident] at h
      $destructTac:tactic)

/-! ## Entry Points -/

def Module.generateReachableInvariantTheorems
    (mod : Module) (substs : ParameterSubst) : CommandElabM Unit := do
  mod.throwIfSpecNotFinalized
  validateReachableInvariantSubstitutions mod substs
  ensureRequiredTheoremsAvailable mod
  let ctx ← mkGenCtx mod substs
  elabCommand (← mkReachableInvariantsTheorem ctx)
  for inv in mod.invariants do
    elabCommand (← mkProjectionTheorem ctx inv.name)

def elabGenReachableInvariantsCommand (stx : Syntax) : CommandElabM Unit := do
  let mod ← getCurrentModule
    (errMsg := "You cannot #gen_reachable_invariants outside of a Veil module!")
  match stx with
  | `(command| #gen_reachable_invariants) =>
      mod.generateReachableInvariantTheorems {}
  | `(command| #gen_reachable_invariants with $substs:reachableInvariantSubstitution,*) =>
      mod.generateReachableInvariantTheorems (← parseReachableInvariantSubstitutions substs)
  | _ => throwUnsupportedSyntax

end Veil
