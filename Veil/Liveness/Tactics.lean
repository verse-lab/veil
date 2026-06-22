import Veil.Liveness.TLABridge
import Veil.Liveness.ProofModeExtensions
import Veil.Frontend.DSL.Tactic
import Veil.Frontend.DSL.Module.Names
import Veil.Frontend.DSL.Util
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Frontend.DSL.Module.Util.Basic
import Veil.Util.Theorems

/-! # Tactics for Liveness Proofs

-/

open TLA Lean Elab Tactic Meta

namespace Veil.Liveness

open Veil

/-! ## Hypothesis-finding helpers -/

/-- Find the first hypothesis whose type **contains** a constant with the given name
    anywhere in the expression tree. Returns `none` if not found. -/
private def findHypContainingConst (nm : Name) : TacticM (Option FVarId) := do
  let lctx ← getLCtx
  for ldecl in lctx do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    if ty.find? (fun e => e.isConstOf nm) |>.isSome then
      return some ldecl.fvarId
  return none

/-- Find all hypotheses whose type **contains** a constant with the given name
    anywhere in the expression tree. -/
private def findHypsContainingConst (nm : Name) : TacticM (Array FVarId) := do
  let lctx ← getLCtx
  let mut hyps := #[]
  for ldecl in lctx do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    if ty.find? (fun e => e.isConstOf nm) |>.isSome then
      hyps := hyps.push ldecl.fvarId
  return hyps

/-- Find the first hypothesis whose type's **head function** (outermost applied constant,
    after stripping foralls) is the given constant. Returns `none` if not found. -/
private def findHypHeadedByConst (nm : Name) : TacticM (Option FVarId) := do
  let lctx ← getLCtx
  for ldecl in lctx do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    -- Strip leading foralls
    let body := ty.getForallBody
    if body.getAppFn'.isConstOf nm then
      return some ldecl.fvarId
  return none

private def getHypDeclByFinding (finder : Name → TacticM (Option FVarId)) (nm : Name) : TacticM (Option LocalDecl) := do
  let fullName ← resolveGlobalConstNoOverloadCore nm
  let some fv ← finder fullName | return none
  fv.getDecl

private def getHypDeclsByFinding (finder : Name → TacticM (Array FVarId)) (nm : Name) : TacticM (Array LocalDecl) := do
  let fullName ← resolveGlobalConstNoOverloadCore nm
  let fvs ← finder fullName
  fvs.mapM fun fv => fv.getDecl

private def localContextOrTargetContainsAnyConst (consts : Array Name) : TacticM Bool := do
  let resolved ← consts.mapM resolveGlobalConstNoOverloadCore
  let goal ← getMainGoal
  let target ← goal.getType
  if exprContainsAnyConst resolved target then
    return true
  goal.withContext do
  let lctx ← getLCtx
  for ldecl in lctx do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    if exprContainsAnyConst resolved ty then
      return true
  return false
where
  exprContainsAnyConst (consts : Array Name) (e : Expr) : Bool :=
    let usedConsts := e.getUsedConstantsAsSet
    consts.any usedConsts.contains

/-- Find a hypothesis using `finder` on `findName`, then apply the transition
    abstraction theorem `trAbsName` to it and `veil_dsimp only`.
    Returns `true` if a matching hypothesis was found and narrowed. -/
private def applyTransitionAbstract
    (finder : Name → TacticM (Option FVarId))
    (findName trAbsName : Name) : DesugarTacticM Bool := veilWithMainContext do
  let some hyp ← getHypDeclByFinding finder findName | return false
  let hypId := mkIdent hyp.userName
  let trAbsId ← Lean.mkIdent <$> resolveGlobalConstNoOverloadCore trAbsName
  veilEvalTactic (← `(tactic| apply $trAbsId at $hypId ; veil_dsimp only at $hypId:ident))
  return true

/-! ## Proof pipeline overview

After reducing temporal proof obligations to the safety fragment, the common
liveness proof pipeline follows these steps:

1. **Narrow**: Unfold `NextStep` to `NextTr`, apply transition weakening
   theorems (`.tr_abstract`) to hypotheses containing `NextTr` or specific actions, rewrite `Invariants`
   with `core_simplified_eq`, simplify enabledness with `enabledSimp`, apply
   `LocalRProp.core_eq`, and simplify assumptions with `invSimp`.
2. **Generalize**: Concretize abstract state and fields
   (`__veil_concretize_state_wp`, `__veil_concretize_fields_wp`).
3. **Unfold**: Unfold `Invariants.core_simplified` and `LocalRProp.core`
   definitions, plus field label coercions.
4. **Neutralize**: Normalize decidable instances
   (`__veil_neutralize_decidable_inst`).
5. **Simplify**: Apply Classical simplification with `invSimp`, `smtSimp`,
   `ghostRelSimp` (via `elabSimplifyBeforeConcretizeWp`).
6. **FOL**: First-order logic simplification (`veil_fol !`).
7. **SMT**: Discharge remaining goals with SMT (`veil_smt`).
-/

/-! ## Syntax registration

Internal sub-tactics use `__` prefix. -/

syntax "__liveness_drop_init" : tactic
syntax "__liveness_drop_invariants" : tactic
syntax "__liveness_reduce_to_safety" : tactic
syntax "__liveness_narrow_localrprop" : tactic
-- syntax "__liveness_narrow_next" : tactic
syntax "__liveness_narrow_enabled" : tactic
syntax "__liveness_narrow_invariants" : tactic
syntax "__liveness_narrow_assumptions" : tactic
syntax "__liveness_unfold_assumptions_core" : tactic
syntax "__liveness_unfold_invariants_core" : tactic
syntax "__liveness_narrow_init" : tactic
syntax "__liveness_narrow_action" : tactic
syntax "__unveil_temporal_prepare_premises" : tactic

/-- Unveil a temporal proof obligation into a field-exposed first-order shape.
This tactic is intended only for goals that can obviously be reduced by
`tfinite_window` to facts about states in a finite prefix of one trace. -/
syntax (name := unveil_temporal) "unveil_temporal" : tactic

/-- Solve a temporal proof obligation by unveiling it, then running FOL-ization and `veil_solve`. -/
syntax (name := veil_solve_temporal) "veil_solve_temporal" : tactic

/-! ## Step 1: Dropping conjuncts from the behavior

These run inside Lentil's proof mode (the goal is an `Entails` sequent).
They find the proof-mode hypothesis whose pred contains `Init` /
`Invariants` and clear it with `tclear`. Self-skip if no match. -/

private def keepHypsByContainingConsts (consts : List Name) : DesugarTacticM Unit :=
  veilWithMainContext do
    let names ← findTemporalHypsContaining consts
    unless names.isEmpty do
      let idents := names.toArray.map (fun n => Lean.mkIdent (Lean.Name.mkSimple n))
      veilEvalTactic (← `(tactic| tclear *- $[$idents:ident]*))

/-
/-- Drop the proof-mode hypothesis containing `Init` (typically `⌜Init⌝`). -/
def elabLivenessDropInit : DesugarTacticM Unit :=
  dropHypsByContainingConsts [assembledInitName]

/-- Drop the proof-mode hypothesis containing `Invariants` (typically `□⌜Invariants⌝`). -/
def elabLivenessDropInvariants : DesugarTacticM Unit :=
  dropHypsByContainingConsts [assembledInvariantsName]
-/

/-! ## Step 1b: Reduce to safety fragment -/

/-- Introduce finite-window premises, repeatedly split conjunction goals, and
    introduce any implication premises exposed by those splits. This lets later
    narrowing see facts such as `act.ext.tr` when the original goal looked like
    `_ ∧ (act.ext.tr → _)`. -/
def elabUnveilTemporalPreparePremises : DesugarTacticM Unit := veilWithMainContext do
  veilEvalTactic (← `(tacticSeq|
    intros
    expose_names
    repeat' ((fail_if_no_progress (constructorm* _ ∧ _)) <;> intros <;> expose_names)))

-- FIXME: This is outdated
/-- Reduce a temporal goal to the safety fragment using `tsplit_by_persistency`
    (which peels `□` off the persistent proof-mode hyps for the non-persistent
    goal subgoal), then `texit; tfinite_window` to land in first-order. -/
def elabLivenessReduceToSafety : DesugarTacticM Unit := veilWithMainContext do
  veilEvalTactic (← `(tacticSeq|
    tsplit_by_persistency
    tsimp -$(mkIdent `failIfUnchanged) only [$(mkIdent ``TLA.always_implies):ident,
      ← $(mkIdent ``TLA.always_and):ident, $(mkIdent ``TLA.and_imp):ident]
    tmonotone
    trevert_all
    tfinite_window))
  elabUnveilTemporalPreparePremises

/-! ## Finding-based narrowing tactics (Step 2)

All of the following tactics internally search the local context.
If nothing matching is found, they act as `skip` (no error, no effect).

They use `DesugarTacticM` following the convention in `Veil/Frontend/DSL/Tactic.lean`,
and call `veilEvalTactic` (not `evalTactic`) so that sub-steps are recorded for
desugaring when `set_option veil.desugarTactic true`. -/

/-- Find hypothesis headed by `Assumptions` and rewrite using `Assumptions.core_simplified_eq`.
    Self-skips if no such hypothesis is found. -/
def elabLivenessNarrowAssumptions : DesugarTacticM Unit := veilWithMainContext do
  let some hyp ← getHypDeclByFinding findHypHeadedByConst assembledAssumptionsName | return
  let coreSimplifiedEq ← Lean.mkIdent <$> (resolveGlobalConstNoOverloadCore <| toCoreSimplifiedEqName assembledAssumptionsName)
  veilEvalTactic (← `(tactic| rw [$coreSimplifiedEq:ident] at $(mkIdent hyp.userName):ident))

/-- Apply `LocalRProp.core_eq` as a simp lemma to narrow `LocalRProp` instances
    to their `core` form. Automatically collects module parameters from the
    current module to construct `@LocalRProp.core_eq param1 param2 ...`. -/
def elabLivenessNarrowLocalRProp : DesugarTacticM Unit := veilWithMainContext do
  let mod ← getCurrentModule (errMsg := "liveness_narrow_localrprop: not inside a Veil module")
  let coreEq ← Lean.mkIdent <$> resolveGlobalConstNoOverloadCore (localRPropTCName ++ `core_eq)
  let paramIds : Array Ident := mod.parameters.map fun p => mkIdent p.name
  let term ← `(@$coreEq $paramIds*)
  veilEvalTactic (← `(tactic| veil_simp only [$term:term] at *))

-- /-- Find hypothesis containing `NextStep`/`NextTr` and apply `Next.tr_abstract` + `veil_dsimp only`.
--     Self-skips if no such hypothesis is found. -/
-- def elabLivenessNarrowNext : DesugarTacticM Unit := do
--   let _ ← applyTransitionAbstract findHypContainingConst
--     assembledNextTrName (toTransitionAbstractName assembledNextName)

/-- If the local context or target mentions enabledness, simplify using
    `enabledSimp` (including TLA/Transition bridging and action-local enabled
    equations). Self-skips if no enabledness constant is present. -/
def elabLivenessNarrowEnabled : DesugarTacticM Unit := veilWithMainContext do
  let shouldSimplify ← localContextOrTargetContainsAnyConst
    #[``TLA.tla_enabled, ``TLA.enabled, ``Transition.enabled]
  if shouldSimplify then
    veilEvalTactic (← `(tactic| veil_simp only [$(mkIdent `enabledSimp):ident] at *))

/-- Find hypothesis headed by `Invariants` and rewrite using `Invariants.core_simplified_eq`.
    Self-skips if no such hypothesis is found. -/
def elabLivenessNarrowInvariants : DesugarTacticM Unit := veilWithMainContext do
  let some hyp ← getHypDeclByFinding findHypHeadedByConst assembledInvariantsName | return
  let coreSimplifiedEq ← Lean.mkIdent <$> (resolveGlobalConstNoOverloadCore <| toCoreSimplifiedEqName assembledInvariantsName)
  veilEvalTactic (← `(tactic| rw [$coreSimplifiedEq:ident] at $(mkIdent hyp.userName):ident))

/-- Find hypothesis headed by `Assumptions.core_simplified` and unfold it with
    `veil_dsimp only [Assumptions.core_simplified]`. Self-skips if not found. -/
def elabLivenessUnfoldAssumptionsCore : DesugarTacticM Unit := veilWithMainContext do
  let some hyp ← getHypDeclByFinding findHypHeadedByConst (toCoreSimplifiedName assembledAssumptionsName) | return
  let coreSimplId ← Lean.mkIdent <$> resolveGlobalConstNoOverloadCore (toCoreSimplifiedName assembledAssumptionsName)
  veilEvalTactic (← `(tactic| veil_dsimp only [$coreSimplId:ident] at $(mkIdent hyp.userName):ident))

-- FIXME: This is too specific (meaning only applies to `Invariants`); better merged
-- with some other handling
/-- Find hypothesis headed by `Invariants.core_simplified` and unfold it with
    `veil_dsimp only [Invariants.core_simplified]`. Self-skips if not found. -/
def elabLivenessUnfoldInvariantsCore : DesugarTacticM Unit := veilWithMainContext do
  let some hyp ← getHypDeclByFinding findHypHeadedByConst (toCoreSimplifiedName assembledInvariantsName) | return
  let coreSimplId ← Lean.mkIdent <$> resolveGlobalConstNoOverloadCore (toCoreSimplifiedName assembledInvariantsName)
  veilEvalTactic (← `(tactic| veil_dsimp only [$coreSimplId:ident] at $(mkIdent hyp.userName):ident))

/-- Find hypothesis containing `Init` and apply narrowing:
    unfold Init, cases σ_inhabited, apply initializer.ext.tr_abstract.
    Self-skips if no such hypothesis is found. -/
def elabLivenessNarrowInit : DesugarTacticM Unit := veilWithMainContext do
  let some hyp ← getHypDeclByFinding findHypContainingConst assembledInitName | return
  let hypId := mkIdent hyp.userName
  let initId ← Lean.mkIdent <$> resolveGlobalConstNoOverloadCore assembledInitName
  -- unfold Init at h ; cases σ_inhabited ; expose_names
  -- FIXME: Need better heuristic to find σ_inhabited
  let σ_inh := mkIdent `σ_inhabited
  veilEvalTactic (← `(tactic| unfold $initId at $hypId:ident ; cases $σ_inh:ident ; expose_names))
  -- apply initializer.ext.tr_abstract at h ; veil_dsimp only at h
  -- (After cases, the hypothesis name may have changed; re-find it)
  let _ ← applyTransitionAbstract findHypHeadedByConst
    (toTransitionName (toExtName initializerName)) (toTransitionAbstractName (toExtName initializerName))

/-- General handling of both `Next` and other non-`Init` actions. -/
def elabLivenessNarrowAction : DesugarTacticM Unit := veilWithMainContext do
  let mod ← getCurrentModule (errMsg := "liveness_narrow_action: not inside a Veil module")
  let nextStepHyps ← getHypDeclsByFinding findHypsContainingConst assembledNextStepName
  unless nextStepHyps.isEmpty do
    let nextStepHypIds := nextStepHyps.map fun hyp => mkIdent hyp.userName
    veilEvalTactic (← `(tactic| unfold $assembledNextStep:ident at $[$nextStepHypIds:ident]*))
  veilWithMainContext do
  let nextHyps ← getHypDeclsByFinding findHypsContainingConst assembledNextTrName
  let nextHyp? := nextHyps[0]?
  let duplicateNextHyps : Array Ident := nextHyps.drop 1 |>.map fun hyp => mkIdent hyp.userName
  unless duplicateNextHyps.isEmpty do
    veilEvalTactic (← `(tactic| clear $[$duplicateNextHyps:ident]*))
  let mut posActHyps : Array Name := #[]
  let mut negActHyps : Array (Name × Nat) := #[]
  let actions := mod.actions
  for (act, idx) in actions.zipIdx do
    -- NOTE: Here assume that an `act.ext.tr` will not appear in both positive and negative positions
    let nm := toTransitionName <| toExtName act.name
    let some hyp ← getHypDeclByFinding findHypContainingConst nm | continue
    let ty ← instantiateMVars hyp.type
    if ty.getAppFn'.isConstOf ``Not then
      negActHyps := negActHyps.push (hyp.userName, idx)
    else
      posActHyps := posActHyps.push act.name
  -- Eventually, the negative ones will be cleared
  let toClear := negActHyps.map fun (nm, _) => mkIdent nm
  -- If `posActHyps` is not empty, then only consider them and throw `Next` and negative actions
  if (!posActHyps.isEmpty) || nextHyp?.isNone then
    -- NOTE: Usually there should be at most one action hypothesis, but here we handle all of them
    let toClear := if let some nextHyp := nextHyp? then toClear.push (mkIdent nextHyp.userName) else toClear
    unless toClear.isEmpty do
      veilEvalTactic (← `(tactic| clear $[$toClear:ident]*))
  unless posActHyps.isEmpty do
    for actName in posActHyps do
      let _ ← applyTransitionAbstract findHypHeadedByConst
        (toTransitionName (toExtName actName)) (toTransitionAbstractName (toExtName actName))
    return
  -- Otherwise, consider negative actions and `Next`
  let some nextHyp := nextHyp? | return
  -- Simplify `Next` first
  veilWithMainContext do
    let simps := #[labelCases, assembledNextTr]
    veilEvalTactic (← `(tactic| simp only [$[$simps:ident],*] at $(mkIdent nextHyp.userName):ident))
  -- Drop the branches in `Next` by `simp` with negative action hypotheses
  if !negActHyps.isEmpty then
    let simps := toClear ++ (#[``_root_.false_or, ``_root_.or_false].map Lean.mkCIdent)
    veilWithMainContext do
      veilEvalTactic (← `(tactic| (simp only [$[$simps:ident],*] at $(mkIdent nextHyp.userName):ident) ; clear $[$toClear:ident]* ))
  -- Keep "active" branches
  let activeIdxs := Array.range actions.size |>.filter fun i => negActHyps.all (fun (_, idx) => idx != i)
  let activeIdxsList := activeIdxs.map Syntax.mkNatLit
  let dsimps := #[``repeatedOrProp, ``List.reverse, ``IteratedPred.exists].map Lean.mkIdent
  -- Sometimes Lean has difficulty finding the theory argument, so need to provide it explicitly here
  -- FIXME: The following just uses the simplest heuristic
  veilWithMainContext do
    veilEvalTactic (← `(tactic|
      apply $(mkIdent <| toTransitionAbstractName assembledNextName)
        ($environmentTheory := $environmentTheory)
        ($environmentState := $environmentState)
        ($(mkVeilImplementationDetailIdent `idxs) := [$activeIdxsList,*])
        ($(mkVeilImplementationDetailIdent `r₀) := $(mkIdent `th))
        at $(mkIdent nextHyp.userName):ident ; dsimp [$[$dsimps:ident],*] at $(mkIdent nextHyp.userName):ident))

/-! ## Common pipeline -/

/-- Unveil a temporal proof obligation by narrowing, concretizing, unfolding,
    neutralizing, and simplifying. Finding-based sub-tactics self-skip when
    their targets are not present. -/
def elabUnveilTemporal : DesugarTacticM Unit := do
  veilEvalTactic <| ← `(tactic| tsimp only [$(mkIdent ``TLA.and_imp):ident] ; tfinite_window )
  elabUnveilTemporalPreparePremises
  -- Narrowing
  -- elabLivenessNarrowNext
  elabLivenessNarrowInit
  elabLivenessNarrowAction
  elabLivenessNarrowEnabled
  elabLivenessNarrowAssumptions
  elabLivenessNarrowInvariants
  elabLivenessNarrowLocalRProp
  -- Generalize
  veilWithMainContext do
    veilEvalTactic (← `(tacticSeq|
      __veil_concretize_state_wp
      __veil_concretize_fields_wp !))
  -- Unfold (finding-based, self-skipping)
  elabLivenessUnfoldAssumptionsCore
  elabLivenessUnfoldInvariantsCore
  veilWithMainContext do
    veilEvalTactic (← `(tacticSeq|
      veil_dsimp only [$(mkIdent `nextSimp):ident, $(fieldLabelToCodomain stateName):ident, $(fieldLabelToDomain stateName):ident] at *
      -- Neutralize
      __veil_neutralize_decidable_inst))
  -- Classical simplification
  veilWithMainContext do
    veilEvalTactic (← elabSimplifyBeforeConcretizeWp (fast := true) (simpHinv := true))

/-- Solve temporal subgoals by unveiling, normalizing first-order structure, and SMT. -/
def elabVeilSolveTemporal : DesugarTacticM Unit := do
  elabUnveilTemporal
  -- FOL + SMT
  veilWithMainContext do
    veilEvalTactic (← `(tacticSeq| veil_fol ! ; veil_solve ))

elab_rules : tactic
  -- | `(tactic| __liveness_drop_init%$tk) => elabLivenessDropInit.runByOption tk
  -- | `(tactic| __liveness_drop_invariants%$tk) => elabLivenessDropInvariants.runByOption tk
  | `(tactic| __liveness_reduce_to_safety%$tk) => elabLivenessReduceToSafety.runByOption tk
  | `(tactic| __liveness_narrow_localrprop%$tk) => elabLivenessNarrowLocalRProp.runByOption tk
  -- | `(tactic| __liveness_narrow_next%$tk) => elabLivenessNarrowNext.runByOption tk
  | `(tactic| __liveness_narrow_enabled%$tk) => elabLivenessNarrowEnabled.runByOption tk
  | `(tactic| __liveness_narrow_invariants%$tk) => elabLivenessNarrowInvariants.runByOption tk
  | `(tactic| __liveness_narrow_assumptions%$tk) => elabLivenessNarrowAssumptions.runByOption tk
  | `(tactic| __liveness_unfold_assumptions_core%$tk) => elabLivenessUnfoldAssumptionsCore.runByOption tk
  | `(tactic| __liveness_unfold_invariants_core%$tk) => elabLivenessUnfoldInvariantsCore.runByOption tk
  | `(tactic| __liveness_narrow_init%$tk) => elabLivenessNarrowInit.runByOption tk
  | `(tactic| __liveness_narrow_action%$tk) => elabLivenessNarrowAction.runByOption tk
  | `(tactic| __unveil_temporal_prepare_premises%$tk) => elabUnveilTemporalPreparePremises.runByOption tk
  | `(tactic| unveil_temporal%$tk) => elabUnveilTemporal.runByOption tk
  | `(tactic| veil_solve_temporal%$tk) => elabVeilSolveTemporal.runByOption tk

syntax (name := tlaGroundBigopTac) "tground_bigop" (Lean.Parser.Tactic.location)? : tactic

elab_rules : tactic
  | `(tactic| tground_bigop%$tk $[$pos:location]? ) => do
    let simps := #[``bigwedge_list_cons, ``bigwedge_list_nil,
      ``bigvee_list_cons, ``bigvee_list_nil].map Lean.mkIdent
    let a := veilEvalTactic <| ← `(tacticSeq| tsimp +$(mkIdent `decide) only [$[$simps:ident],* , ↓ $(mkIdent ``reduceIte):ident] $[$pos:location]? ; tnormalize)
    a.runByOption tk

end Veil.Liveness
