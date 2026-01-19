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
The `targetFingerprint` parameter specifies which violating state's trace to recover.
If `assertionFailureExId` is provided, this is an assertion failure trace and we'll
find the failing transition to populate the `failingStep` field. -/
def recoverTrace {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [fp : StateFingerprint σ σₕ]
  [Inhabited κ] [Inhabited σ] [Repr σₕ]
  [BEq σ] [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  (ctx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (targetFingerprint : σₕ)
  (assertionFailureExId : Option Int := none)
  : m (Trace ρ σ κ) := do
  -- Retrace steps from the target fingerprint back to an initial state
  let (initFp, stepsFp) := retraceSteps ctx.log targetFingerprint
  -- Recover initial state by matching fingerprint
  let initialState := findByFingerprint sys.initStates initFp default
  -- Recover trace steps by re-executing transitions and matching fingerprints
  let mut curSt := initialState
  let mut steps : Steps σ κ := #[]
  for step in stepsFp do
    let outcomes := sys.tr th curSt
    -- Extract successful transitions for trace recovery
    let successfulTransitions := extractSuccessfulTransitions outcomes
    let (transitionLabel, nextSt) :=
      match successfulTransitions.find? (fun (_, s) => fp.view s == step.nextState) with
      | some (tr, s) => (tr, s)
      | none => panic! s!"Could not recover transition from fingerprint {repr (fp.view curSt)} to {repr step.nextState}!"
    curSt := nextSt
    steps := steps.push { transitionLabel := transitionLabel, nextState := nextSt }
  return { theory := th, initialState := initialState, steps := steps, failingStep := findFailingStep curSt assertionFailureExId }
where
  findFailingStep (st : σ) : Option Int → Option (Step σ κ)
    | some exId =>
      match (sys.tr th st).find? (·.2.exceptionId? == some exId) with
      | some (label, .assertionFailure _ failState) => some { transitionLabel := label, nextState := failState }
      | _ => none
    | none => none

/-! ## Model Checker

This module provides the main entry point for model checking, dispatching to
either the sequential or parallel implementation based on configuration. -/

def findReachable {ρ σ κ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [Inhabited κ] [inhabσ : Inhabited σ] [Repr σ] [Repr κ]
  [BEq σ] [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  [fp : StateFingerprint σ UInt64]
  (params : SearchParameters ρ σ)
  (parallelCfg : Option ParallelConfig)
  (progressInstanceId : Nat)
  (cancelToken : IO.CancelToken)
  : m (ModelCheckingResult ρ σ κ UInt64) := do
  let ctx ← match parallelCfg with
    | some cfg => do pure (← breadthFirstSearchParallel sys params cfg progressInstanceId cancelToken).toBaseSearchContext
    | none     => do pure (← breadthFirstSearchSequential sys params progressInstanceId cancelToken).toBaseSearchContext
  match ctx.finished with
  | some (.earlyTermination (.foundViolatingState fingerprint violations)) => do
    return ModelCheckingResult.foundViolation fingerprint (.safetyFailure violations) (some (← recoverTrace sys ctx fingerprint))
  | some (.earlyTermination (.deadlockOccurred fingerprint)) => do
    return ModelCheckingResult.foundViolation fingerprint .deadlock (some (← recoverTrace sys ctx fingerprint))
  | some (.earlyTermination (.assertionFailed fingerprint exId)) => do
    return ModelCheckingResult.foundViolation fingerprint (.assertionFailure exId) (some (← recoverTrace sys ctx fingerprint (some exId)))
  | some (.earlyTermination (.reachedDepthBound _)) =>
    -- No violation found within depth bound; report number of states explored
    return ModelCheckingResult.noViolationFound ctx.seen.size (.earlyTermination (.reachedDepthBound ctx.completedDepth))
  | some (.earlyTermination .cancelled) =>
    -- Search was cancelled by the user
    return ModelCheckingResult.cancelled
  | some (.exploredAllReachableStates) => do
    if !ctx.violatingStates.isEmpty then
      let (fingerprint, violation) := ctx.violatingStates.head!
      -- For assertion failures, pass the exception ID to recover the failing step
      let assertionExId := match violation with
        | .assertionFailure exId => some exId
        | _ => none
      return ModelCheckingResult.foundViolation fingerprint violation (some (← recoverTrace sys ctx fingerprint assertionExId))
    else
      return ModelCheckingResult.noViolationFound ctx.seen.size (.exploredAllReachableStates)
  | none => panic! s!"SearchContext.finished is none! This should never happen."

end Veil.ModelChecker.Concrete
