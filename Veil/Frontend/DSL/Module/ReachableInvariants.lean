module

public meta import Veil.Frontend.DSL.Module.Util
public meta import Veil.Frontend.DSL.Action.Semantics.Theorems

/-!
Reachability theorems, adapted from the dissertation branch. Action VCs assume
the entire invariant conjunction, so all its clauses must be established before
any projection can be exported. Existing reachability proofs can supply clauses
(in particular, trusted invariants) that do not have induction VCs.
-/

public meta section

open Lean Elab Command

namespace Veil

private def invariantTheoremName (name : Name) : Name := name ++ `is_inv

private def preservationTheoremName (act inv : Name) : Name :=
  Name.mkSimple s!"{act}_{inv}"

private def initializationTheoremName (inv : Name) : Name :=
  (preservationTheoremName initializerName inv).appendAfter "_tr"

private def theoremExists (name : Name) : CommandElabM Bool := do
  return (← getEnv).contains ((← getCurrNamespace) ++ name)

/-- This is deliberately about proof availability, not the verifier's success
status: trusted clauses have no VCs, and users can supply proofs themselves. -/
private def hasRequiredTheorems (mod : Module) : CommandElabM Bool := do
  if ← theoremExists (invariantTheoremName assembledInvariantsName) then return true
  for inv in mod.invariants do
    if ← theoremExists (invariantTheoremName inv.name) then continue
    let required := #[initializationTheoremName inv.name] ++
      mod.actions.map (fun act => preservationTheoremName act.name inv.name)
    for name in required do
      unless ← theoremExists name do return false
  return true

private structure GenCtx where
  mod : Module
  binders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)
  namedArgs : Array (TSyntax `Lean.Parser.Term.namedArgument)
  rtsTerm : Term

private def mkNamedArg (name : Name) (term : Term) :
    CommandElabM (TSyntax `Lean.Parser.Term.namedArgument) :=
  `(Lean.Parser.Term.namedArgument| ($(mkIdent name) := $term:term))

private def GenCtx.app (ctx : GenCtx) (name : Name) (positional : Array Term) : Term :=
  let args := ctx.namedArgs.map (·.raw) ++ positional.map (·.raw)
  ⟨mkNode `Lean.Parser.Term.app #[mkIdent name, mkNullNode args]⟩

private def mkGenCtx (mod : Module) : CommandElabM GenCtx := do
  let binders ← mod.parameters.filterMapM fun p => do
    match p.kind with
    | .sort _ | .userParameter => some <$> (mkImplicitBinder (← p.binder))
    | .moduleTypeclass .sortAssumption =>
        -- The concrete RTS binds Inhabited, but chooses DecidableEq
        -- classically. Its transitions and these VC applications must use
        -- the same instances, including inside the monadic action terms.
        if (p.type.raw.find? (·.getId == ``Inhabited)).isSome then some <$> p.binder
        else pure none
    | .moduleTypeclass .userDefined => some <$> p.binder
    | _ => pure none
  let args ← mod.uninterpretedParamIdents
  let theoryTerm ← `(term| $(mkIdent theoryName) $args*)
  let fieldTerm ← `(term| $(mkIdent fieldAbstractDispatcherName) $args*)
  let stateTerm ← `(term| $(mkIdent stateName) $fieldTerm)
  -- The RTS takes only sorts/user parameters and inferred typeclass instances.
  let rtsTerm ← `(term| $(mkIdent assembledRTSName) $args*)
  let mut namedArgs := #[
    ← mkNamedArg environmentTheoryName theoryTerm,
    ← mkNamedArg environmentStateName stateTerm]
  for p in mod.parameters do
    match p.kind with
    | .sort _ | .userParameter =>
        namedArgs := namedArgs.push (← mkNamedArg p.name (← p.arg))
    | _ => pure ()
  namedArgs := namedArgs.push (← mkNamedArg fieldConcreteTypeName fieldTerm)
  return { mod, binders, namedArgs, rtsTerm }

private def GenCtx.statement (ctx : GenCtx) (predicate : Name) : CommandElabM Term := do
  let th := mkIdent (← liftCoreM <| mkFreshUserName `th)
  let st := mkIdent (← liftCoreM <| mkFreshUserName `st)
  let body := ctx.app predicate #[⟨th⟩, ⟨st⟩]
  `(term| RelationalTransitionSystem.isInvariant $(ctx.rtsTerm) (fun $th $st => $body))

private def mkConjunctionProof (proofs : Array (TSyntax `Lean.Parser.Tactic.tacticSeq)) :
    CommandElabM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  if proofs.isEmpty then return ← `(tacticSeq| trivial)
  proofs.pop.foldrM (init := proofs.back!) fun p acc =>
    `(tacticSeq|
      constructor
      · ($p:tacticSeq)
      · ($acc:tacticSeq))

private def existingInvariantProof (inv : Name) : CommandElabM (TSyntax `Lean.Parser.Tactic.tacticSeq) :=
  `(tacticSeq| exact $(mkIdent (invariantTheoremName inv)) _ _ hcurrent)

private def mkInitArm (ctx : GenCtx) (inv : Name) :
    CommandElabM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  if ← theoremExists (invariantTheoremName inv) then return ← existingInvariantProof inv
  let hpres := ctx.app (initializationTheoremName inv) #[]
  `(tacticSeq|
    exact $hpres th default s ⟨has, trivial⟩ (by
      simpa only [nextSimp] using hinit))

private def mkActionArm (ctx : GenCtx) (act inv : Name) (args : Array Ident) :
    CommandElabM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  if ← theoremExists (invariantTheoremName inv) then return ← existingInvariantProof inv
  let hpres := ctx.app (preservationTheoremName act inv) (args.map (fun id => ⟨id⟩))
  -- Main's Next uses the monadic transition, including for native transitions.
  -- WP ↔ monadic TR is valid here without identifying a raw native relation
  -- with its framed transition on an arbitrary ambient state.
  `(tacticSeq|
    have hpres := $hpres
    rw [← Transition.meetsSpecificationIfSuccessfulAssuming_eq] at hpres
    exact hpres th s s' ⟨has, ih⟩ (by
      simpa only [nextSimp, ← VeilM.toTransitionDerived_sound] using htr))

private def mkActionCase (ctx : GenCtx) (act : ProcedureSpecification) :
    CommandElabM (TSyntax `Lean.Parser.Tactic.inductionAlt) := do
  let args ← act.params.mapM (fun _ => mkIdent <$> liftCoreM (mkFreshUserName `arg))
  let arms ← ctx.mod.invariants.mapM (fun inv => mkActionArm ctx act.name inv.name args)
  let proof ← mkConjunctionProof arms
  `(Lean.Parser.Tactic.inductionAlt|
    | $(mkIdent act.name):ident $args:ident* =>
        ($proof:tacticSeq))

private def mkReachabilityProof (ctx : GenCtx) : CommandElabM Term := do
  let initArms ← ctx.mod.invariants.mapM (fun inv => mkInitArm ctx inv.name)
  let initProof ← mkConjunctionProof initArms
  let actionCases ← ctx.mod.actions.mapM (mkActionCase ctx)
  `(term| by
    intro th st hr
    induction hr with
    | init s has hinit =>
        have hcurrent := RelationalTransitionSystem.reachable.init
          (sys := $(ctx.rtsTerm)) (th := th) s has hinit
        ($initProof:tacticSeq)
    | step s s' hreach hnext ih =>
        have has := RelationalTransitionSystem.reachable_assumptions _ _ _ hreach
        have hcurrent := RelationalTransitionSystem.reachable.step s s' hreach hnext
        rcases hnext with ⟨label, htr⟩
        cases label with $[$actionCases]*)

private def mkProjectionProof (ctx : GenCtx) (clauses : Array StateAssertion) : CommandElabM Term := do
  let hypotheses := ctx.mod.invariants.mapIdx (fun i _ => mkIdent (.mkSimple s!"h_inv_{i}"))
  let arms ← clauses.mapM fun clause => do
    let some i := ctx.mod.invariants.findIdx? (·.name == clause.name)
      | throwError "unknown invariant clause {clause.name}"
    `(tacticSeq| exact $(hypotheses[i]!):ident)
  let proof ← mkConjunctionProof arms
  let destruct ← if hypotheses.size == 1 then
      `(tactic| have $(hypotheses[0]!):ident := h)
    else if hypotheses.isEmpty then `(tactic| skip)
    else `(tactic| rcases h with ⟨$[$hypotheses],*⟩)
  `(term| by
    intro th st hr
    have h := $(mkIdent (invariantTheoremName assembledInvariantsName)) th st hr
    $destruct:tactic
    ($proof:tacticSeq))

/-- Elaborate synchronously without error recovery, then let the kernel check
the declaration. Failed generation must never reserve a name with a sorry. -/
private def addInvariantTheorem (ctx : GenCtx) (predicate : Name)
    (proof : CommandElabM Term) : CommandElabM Unit := do
  let name := invariantTheoremName predicate
  let statement ← ctx.statement predicate
  let proof ← proof
  liftTermElabM <| Term.elabBinders ctx.binders fun xs => do
    let typ ← Term.withSynthesize (postpone := .no) <| Term.withoutErrToSorry <|
      Term.elabType (← `(term| open Classical in $statement))
    let typ ← instantiateMVars typ
    let closedType ← Meta.mkForallFVars xs typ
    if closedType.hasMVar || closedType.hasFVar || closedType.hasSorry then
      throwError "could not determine type of reachable-invariant theorem `{name}`"
    let fullName := (← getCurrNamespace) ++ name
    if let some info := (← getEnv).find? fullName then
      unless ← Meta.isDefEq info.type closedType do
        throwError "cannot generate reachable-invariant theorem `{fullName}` because a declaration with that name already exists with a different type"
      return
    let witness ← Term.withSynthesize (postpone := .no) <| Term.withoutErrToSorry <|
      Term.elabTermEnsuringType (← `(term| by classical exact $proof)) typ
    -- Resolve inferred arguments before abstracting the module parameters;
    -- assignments can themselves contain references to those local binders.
    let witness ← instantiateMVars witness
    let witness ← Meta.mkLambdaFVars xs witness
    if witness.hasMVar || witness.hasFVar || witness.hasSyntheticSorry then
      throwError "failed to prove reachable-invariant theorem `{fullName}`"
    discard <| addVeilTheorem name closedType witness

/-- Generate the conjunction and its projections when all dependencies exist.
Missing proofs leave reachability theorems undeclared. This performs no solver
work and never treats a trusted invariant as a proof. -/
def Module.generateReachableInvariantTheorems (mod : Module) : CommandElabM Unit := do
  mod.throwIfSpecNotFinalized
  unless ← hasRequiredTheorems mod do return
  let saved ← getEnv
  try
    let ctx ← mkGenCtx mod
    -- Validate supplied reachability proofs before using them as dependencies.
    for inv in mod.invariants do
      if ← theoremExists (invariantTheoremName inv.name) then
        addInvariantTheorem ctx inv.name (mkProjectionProof ctx #[inv])
    addInvariantTheorem ctx assembledInvariantsName (mkReachabilityProof ctx)
    for inv in mod.invariants do
      addInvariantTheorem ctx inv.name (mkProjectionProof ctx #[inv])
    addInvariantTheorem ctx assembledSafetiesName
      (mkProjectionProof ctx mod.safeties)
  catch ex =>
    setEnv saved
    throw ex

end Veil
