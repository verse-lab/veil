import Lentil

/-! # Proof-Mode Extensions for Veil Liveness Proofs

Utilities and tactics used by the Veil liveness pipeline that build on top of
Lentil's proof mode but aren't (yet) part of Lentil proper. -/

namespace Veil.Liveness

open TLA TLA.ProofMode LentilLib

universe u

/-! ## Soundness theorems for `tsplit_by_persistency` -/

section soundness

variable {σ : Type u}

/-- Internal helper used to prove the user-facing
`Entails_split_by_persistency`. Side conditions are passed as explicit args so
the public theorem can derive them from the index data. -/
private theorem Entails_split_by_persistency_aux
  {hyps : List (NamedPred σ)} {goal : pred σ}
  (HP HQ : List (NamedPred σ)) (gpParts gqParts : List (pred σ))
  (hHPincl : (mapHypPreds TLA.always HP).map NamedPred.pred ⊆ hyps.map NamedPred.pred)
  (hHQincl : HQ.map NamedPred.pred ⊆ hyps.map NamedPred.pred)
  (hGoal : ((repeatedAnd gpParts) ∧ (repeatedAnd gqParts)) |-tla- (goal))
  (hp : Entails (mapHypPreds TLA.always HP) (repeatedAnd gpParts))
  (hq : Entails ((mapHypPreds TLA.always HP) ++ HQ) (repeatedAnd gqParts)) :
  Entails hyps goal := by
  apply Entails_trans hGoal
  rw [Entails_and_split] ; constructor
  · apply Entails_drop_hyps _ hHPincl hp
  · apply Entails_drop_hyps (_ ++ HQ) (by grind) hq

/-- The complement of `s` in `[0, n)`, in canonical (ascending) order. -/
private def complementOfIndices (s : List Nat) (n : Nat) : List Nat :=
  (List.range n).filter (fun i => !s.contains i)

private theorem complementOfIndices_mem (s : List Nat) (n i : Nat) :
  i ∈ complementOfIndices s n ↔ i < n ∧ i ∉ s := by
  simp [complementOfIndices, List.mem_range]

/-- Reflexive index-based form, in the spirit of `Entails_rcases_*_by_idx` in
`Lentil.ProofMode.Tactics.RCases`. The partition of `hyps` is described by
`HPidxs` (persistent) and `HQidxs` (the rest), and the partition of
`goalParts` (the goal's `tla_and` conjuncts) is described by `GPidxs`
(persistent); `gqParts` is automatically the complement, so `gpParts` and
`gqParts` together cover `goalParts` no matter which `GPidxs` the call site
picks. Every `heq` side condition reduces to `rfl` when the call site supplies
matching `HP`, `HQ`, `gpParts`, `gqParts`, so the tactic discharges them with
`(by rfl)`. -/
theorem Entails_split_by_persistency
  {hyps : List (NamedPred σ)} {goalParts : List (pred σ)}
  {HP HQ : List (NamedPred σ)} {gpParts gqParts : List (pred σ)}
  (HPidxs HQidxs GPidxs : List Nat)
  (heq1 : HPidxs.filterMap (hyps[·]?) = mapHypPreds TLA.always HP)
  (heq2 : HQidxs.filterMap (hyps[·]?) = HQ)
  (heq3 : GPidxs.filterMap (goalParts[·]?) = gpParts)
  (heq4 : (complementOfIndices GPidxs goalParts.length).filterMap (goalParts[·]?) = gqParts)
  (hp : Entails (mapHypPreds TLA.always HP) (repeatedAnd gpParts))
  (hq : Entails ((mapHypPreds TLA.always HP) ++ HQ) (repeatedAnd gqParts)) :
  Entails hyps (repeatedAnd goalParts) := by
  refine Entails_split_by_persistency_aux HP HQ gpParts gqParts ?_ ?_ ?_ hp hq <;> try grind
  -- hGoal: (rep gp ∧ rep gq) |-tla- rep goalParts.
  -- gp ∪ gq cover all of goalParts because (GPidxs, complement) partition [0, len).
  rw [← heq3, ← heq4, ← repeatedAnd_append, ← List.filterMap_append]
  apply repeatedAnd_subset_implies
  simp only [List.subset_def, List.mem_append, List.mem_filterMap, complementOfIndices_mem]
  intro a hin ; rw [List.mem_iff_getElem?] at hin
  grind

-- FIXME: Well, this should be somewhere? Or `private`?
theorem Entails_true {σ : Type u} {hyps : List (NamedPred σ)} : Entails hyps (TLA.tla_true : pred σ) :=
  fun _ _ => True.intro

end soundness

/-! ## Helper: find proof-mode hyps containing given constants -/

section helpers

open Lean Meta Elab Tactic

/-- Inspect the current proof-mode `Entails` goal and return the names of those
named hypotheses whose predicate expression contains any constant from `consts`
anywhere in its expression tree. The input `consts` may be unresolved
(short) names; they are resolved against the current scope before comparison.
Returns `[]` if the goal is not an `Entails` sequent or no hypothesis matches. -/
def findTemporalHypsContaining (consts : List Name) : TacticM (List String) := do
  let resolved ← consts.mapM resolveGlobalConstNoOverloadCore
  let some (_, hyps) ← recognizeEntailsHypsFromGoal | return []
  return hyps.filterMap fun (name, pred) =>
    let usedConsts := pred.getUsedConstantsAsSet
    if resolved.any fun c => usedConsts.contains c then
      some name
    else
      none

end helpers

/-! ## The `tsplit_by_persistency` tactic -/

section tactic

open Lean Meta Elab Tactic

-- FIXME: Also appearing in `ModalityMisc`
private def peelAlways? (p : Expr) : Option Expr :=
  if p.getAppFn'.isConstOf ``TLA.always then
    if h : p.isApp = true then some (p.appArg h) else none
  else
    none

/-- Implementation of `tsplit_by_persistency`. -/
def elabTlaSplitByPersistency : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let target ← g.getType
  let target ← cleanupAnnotAndMore target
  let_expr TLA.ProofMode.Entails σExpr hypsExpr goalExpr := target
    | throwError "tsplit_by_persistency: goal is not an Entails sequent, but {target}"
  let some (hypTy, hyps) ← recognizeHypsList hypsExpr
    | throwError "tsplit_by_persistency: failed to read the hypotheses from the goal"
  -- Partition hyps by persistence; record indices into `hyps` for each partition.
  let mut hpIdxs : Array Nat := #[]
  let mut hqIdxs : Array Nat := #[]
  let mut hpStrippedPairs : Array (String × Expr) := #[]
  let mut hqPairs : Array (String × Expr) := #[]
  for ((nm, pred), idx) in hyps.zipIdx do
    match peelAlways? pred with
    | some pred' =>
      hpIdxs := hpIdxs.push idx
      hpStrippedPairs := hpStrippedPairs.push (nm, pred')
    | none =>
      hqIdxs := hqIdxs.push idx
      hqPairs := hqPairs.push (nm, pred)
  -- Partition goal conjuncts by persistence; record indices into `goalParts` for `GPidxs`.
  let goalParts ← TLA.Expr.splitAndIntoParts goalExpr
  let mut gpIdxs : Array Nat := #[]
  let mut gpParts : Array Expr := #[]
  let mut gqParts : Array Expr := #[]
  for (e, idx) in goalParts.zipIdx do
    if (peelAlways? e).isSome then
      gpIdxs := gpIdxs.push idx
      gpParts := gpParts.push e
    else
      gqParts := gqParts.push e
  -- Build expressions for the explicit theorem arguments.
  let predTy ← mkAppM ``TLA.pred #[σExpr]
  let natTy := mkConst ``Nat
  let gpListExpr ← mkListLit predTy gpParts.toList
  let gqListExpr ← mkListLit predTy gqParts.toList
  let goalPartsListExpr ← mkListLit predTy goalParts
  let hpStrippedListExpr ← toHypsList hypTy hpStrippedPairs.toList
  let hqListExpr ← toHypsList hypTy hqPairs.toList
  let hpIdxsListExpr ← mkListLit natTy (hpIdxs.toList.map toExpr)
  let hqIdxsListExpr ← mkListLit natTy (hqIdxs.toList.map toExpr)
  let gpIdxsListExpr ← mkListLit natTy (gpIdxs.toList.map toExpr)
  -- Apply `Entails_split_by_persistency` with all data fixed; heqs become rfl.
  let thmExpr ← mkAppOptM ``Entails_split_by_persistency
    #[σExpr, hypsExpr, goalPartsListExpr,
      hpStrippedListExpr, hqListExpr,
      gpListExpr, gqListExpr,
      hpIdxsListExpr, hqIdxsListExpr, gpIdxsListExpr ]
  /-
  let rfl1 ← mkEqRefl (← mkFreshExprMVar hypTy)
  let rfl2 ← mkEqRefl (← mkFreshExprMVar hypTy)
  let listPredTy ← mkAppM ``List #[predTy]
  let rfl3 ← mkEqRefl (← mkFreshExprMVar listPredTy)
  let rfl4 ← mkEqRefl (← mkFreshExprMVar listPredTy)
  let newGoals ← g.apply (mkAppN thmExpr #[rfl1, rfl2, rfl3, rfl4])
  -/
  let newGoals ← g.apply thmExpr
  let newGoals ← newGoals.filterM fun g' => do
    (do let _ ← g'.applyRfl ; pure false) <|>
    (do
      let [] ← g'.applyConst ``Entails_true | failure
      pure false) <|>
    (pure true)
  replaceMainGoal newGoals
  postDSimpAfterApplyingReflectionTheorem
    #[``mapHypPreds, ``List.map, ``List.cons_append, ``List.nil_append,
      ``ProofMode.repeatedAnd, ``LentilLib.List.foldrD]
  /-
  match newGoals with
  | g1 :: g2 :: g3 :: g4 :: rest =>
    let dischargeRfl (mv : MVarId) : TacticM (List MVarId) := do
      try Tactic.run mv (evalTactic (← `(tactic| rfl))) catch _ => pure [mv]
    let dischargeTrivial (mv : MVarId) : TacticM (List MVarId) := do
      try
        Tactic.run mv (evalTactic (← `(tactic|
          (intro _ _ ; trivial))))
      catch _ => pure [mv]
    let r1 ← dischargeRfl g1
    let r2 ← dischargeRfl g2
    let r3 ← dischargeRfl g3
    let r4 ← dischargeRfl g4
    -- If gpParts is empty, hp is trivial; if gqParts is empty, hq is trivial.
    let rest ← match rest with
      | [hp, hq] =>
        let hpRem ← if gpParts.isEmpty then dischargeTrivial hp else pure [hp]
        let hqRem ← if gqParts.isEmpty then dischargeTrivial hq else pure [hq]
        pure (hpRem ++ hqRem)
      | _ => pure rest
    setGoals (r1 ++ r2 ++ r3 ++ r4 ++ rest)
    postDSimpAfterApplyingReflectionTheorem
      #[``mapHypPreds, ``List.map, ``List.cons_append, ``List.nil_append]
  | _ =>
    throwError
      "tsplit_by_persistency: unexpected number of subgoals ({newGoals.length})"
  -/

/--
`tsplit_by_persistency` operates on a proof-mode `Entails` goal. It
partitions the named hyps into the persistent ones (`HP`, whose predicate is
`□ p`) and the rest (`HQ`), and partitions the goal's `tla_and` conjuncts into
the persistent (`gpParts`) and non-persistent (`gqParts`) parts. It then leaves
up to two subgoals:

- `(mapHypPreds TLA.always HP) ++ HQ |- repeatedAnd gqParts` — the "step"
  obligation (HP still carries `□`; peel later with `treplace` /
  `always_weaken`).
- `mapHypPreds TLA.always HP |- repeatedAnd gpParts` — the "persistence"
  obligation (HQ dropped; HP retains `□`).

If `gpParts` is empty, only the step subgoal is produced; if `gqParts` is empty,
only the persistence subgoal is produced. The remaining subgoals are surfaced;
the four `heq` side conditions are discharged by `rfl`.
-/
elab "tsplit_by_persistency" : tactic => elabTlaSplitByPersistency

end tactic

end Veil.Liveness
