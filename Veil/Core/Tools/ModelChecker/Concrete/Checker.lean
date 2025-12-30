import Veil.Core.Tools.ModelChecker.Concrete.Sequential
import Veil.Core.Tools.ModelChecker.Concrete.Parallel
import Veil.Core.Tools.ModelChecker.Concrete.Progress

namespace Veil.ModelChecker.Concrete

/-! ## Trace Recovery

These functions reconstruct a full trace with concrete states from a SearchContext
that contains fingerprint-based state references. -/

/-- Walk backward through the log to build a fingerprint-based path from a
state to an initial state. Returns `(initialStateFingerprint, steps)` where
each step has the transition label and the fingerprint of the post-state. -/
partial def retraceSteps [BEq σₕ] [Hashable σₕ]
  (log : Std.HashMap σₕ (σₕ × κ)) (cur : σₕ)
  (acc : List (Step σₕ κ) := []) : σₕ × List (Step σₕ κ) :=
  match log.get? cur with
  | none => (cur, acc)
  | some (prev, label) =>
    retraceSteps log prev ({ transitionLabel := label, nextState := cur } :: acc)

/-- Find a full state from a list that matches a given fingerprint. -/
@[inline, specialize]
def findByFingerprint [fp : StateFingerprint σ σₕ]
  (states : List σ) (targetFp : σₕ) (fallback : σ) : σ :=
  states.find? (fun s => fp.view s == targetFp) |>.getD fallback

/-- Reconstruct a full trace with concrete states from a SearchContext.
This re-executes transitions to recover full state objects from fingerprints.
The `targetFingerprint` parameter specifies which violating state's trace to recover. -/
def recoverTrace {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [fp : StateFingerprint σ σₕ]
  [Inhabited κ] [Inhabited σ] [Repr σₕ]
  [BEq σ] [BEq κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  {params : SearchParameters ρ σ}
  (ctx : @BaseSearchContext ρ σ κ σₕ fp th sys params)
  (targetFingerprint : σₕ)
  : m (Trace ρ σ κ) := do
  -- Retrace steps from the target fingerprint back to an initial state
  let (initFp, stepsFp) := retraceSteps ctx.log targetFingerprint
  -- Recover initial state by matching fingerprint
  let initialState := findByFingerprint sys.initStates initFp default
  -- Recover trace steps by re-executing transitions and matching fingerprints
  let mut curSt := initialState
  let mut steps : Steps σ κ := #[]
  for step in stepsFp do
    let successors := sys.tr th curSt
    let (transitionLabel, nextSt) :=
      match successors.find? (fun (_, s) => fp.view s == step.nextState) with
      | some (tr, s) => (tr, s)
      | none => panic! s!"Could not recover transition from fingerprint {repr (fp.view curSt)} to {repr step.nextState}!"
    curSt := nextSt
    steps := steps.push { transitionLabel := transitionLabel, nextState := nextSt }
  return { theory := th, initialState := initialState, steps := steps }

/-! ## Model Checker

This module provides the main entry point for model checking, dispatching to
either the sequential or parallel implementation based on configuration. -/

def findReachable {ρ σ κ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [Inhabited κ] [Inhabited σ] [Repr σ]
  [BEq σ] [BEq κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  [fp : StateFingerprint σ UInt64]
  (params : SearchParameters ρ σ)
  (parallelCfg : Option ParallelConfig)
  : m (ModelCheckingResult ρ σ κ UInt64) := do
  initProgress
  let ctx ← match parallelCfg with
    | some cfg => do pure (← breadthFirstSearchParallel sys params cfg).toBaseSearchContext
    | none     => do pure (← breadthFirstSearchSequential sys params).toBaseSearchContext
  match ctx.finished with
  | some (.earlyTermination (.foundViolatingState fingerprint violations)) => do
    return ModelCheckingResult.foundViolation fingerprint (.safetyFailure violations) (some (← recoverTrace sys ctx fingerprint))
  | some (.earlyTermination (.deadlockOccurred fingerprint)) => do
    return ModelCheckingResult.foundViolation fingerprint .deadlock (some (← recoverTrace sys ctx fingerprint))
  | some (.earlyTermination (.reachedDepthBound _)) =>
    -- No violation found within depth bound; report number of states explored
    return ModelCheckingResult.noViolationFound ctx.seen.size (.earlyTermination (.reachedDepthBound ctx.completedDepth))
  | some (.exploredAllReachableStates) => do
    if !ctx.violatingStates.isEmpty then
      let (fingerprint, violation) := ctx.violatingStates.head!
      return ModelCheckingResult.foundViolation fingerprint violation (some (← recoverTrace sys ctx fingerprint))
    else
      return ModelCheckingResult.noViolationFound ctx.seen.size (.exploredAllReachableStates)
  | none => panic! s!"SearchContext.finished is none! This should never happen."

end Veil.ModelChecker.Concrete
