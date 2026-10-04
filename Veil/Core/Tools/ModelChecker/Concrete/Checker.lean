module

public import Veil.Core.Tools.ModelChecker.Concrete.Sequential
public import Veil.Core.Tools.ModelChecker.Concrete.MapReduce

public section

namespace Veil.ModelChecker.Concrete

/-! ## Trace Recovery

These functions reconstruct a full trace with concrete states from a SearchContext
that contains fingerprint-based state references. -/

/-- Walk backward through the log to build a fingerprint-based path from a
state to an initial state. Returns `(initialStateFingerprint, steps)` where
each step has the transition label and the fingerprint of the post-state. -/
partial def retraceSteps [BEq σₕ] [Hashable σₕ]
  (log : Std.HashMap σₕ (Option (σₕ × κ))) (cur : σₕ)
  (acc : List (Step σₕ κ) := []) : σₕ × List (Step σₕ κ) :=
  match log[cur]? with
  | some (some (prev, label)) =>
    retraceSteps log prev ({ transitionLabel := label, nextState := cur } :: acc)
  | _ => (cur, acc)

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
def recoverTrace {ρ σ κ σₕ asm : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [fp : StateFingerprint σ σₕ]
  [Inhabited σ] [Repr σₕ]
  [ActionStatUpdate κ asm]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  -- (params : SearchParameters ρ σ)
  (ctx : BaseSearchContext σ κ σₕ asm)
  (targetFingerprint : σₕ)
  (assertionFailureExId : Option Int := none)
  : m (Trace ρ σ κ) := do
  -- Retrace steps from the target fingerprint back to an initial state
  let (initFp, stepsFp) := retraceSteps ctx.log targetFingerprint
  -- Recover initial state by matching fingerprint
  let initialState := findByFingerprint sys.initStates initFp default
  -- Recover trace steps by re-executing transitions and matching fingerprints
  -- FIXME: Ideally, this should never fail, due to the proof we have ...
  let mut curSt := initialState
  let mut steps : Steps σ κ := #[]
  for step in stepsFp do
    let successfulTransitions := (sys.tr th curSt).successes
    let (transitionLabel, nextSt) ←
      match successfulTransitions.find? (fun (_, s) => fp.view s == step.nextState) with
      | some (tr, s) => pure (tr, s)
      | none => IO.ofExcept <| Except.error s!"Could not recover transition from fingerprint {repr (fp.view curSt)} to {repr step.nextState}!"
    curSt := nextSt
    steps := steps.push { transitionLabel := transitionLabel, nextState := nextSt }
  return { theory := th, initialState := initialState, steps := steps, failingStep := findFailingStep curSt assertionFailureExId }
where
  findFailingStep (st : σ) : Option Int → Option (Step σ κ)
    | some exId =>
      match (sys.tr th st).failures.find? (·.error == exId) with
      | some f => some { transitionLabel := f.label, nextState := f.state }
      | none => none
    | none => none

/-! ## Model Checker

This module provides the main entry point for model checking, dispatching to
either the sequential or parallel implementation based on configuration. -/

/-- The result of a finished search, with a trace for a violation. -/
private def searchResult {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [Inhabited σ] [ActionStatUpdate κ asm]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  [fp : StateFingerprint σ σₕ] [Repr σₕ]
  (ctx : BaseSearchContext σ κ σₕ asm) (distinctCount : Nat)
  : m (ModelCheckingResult ρ σ κ σₕ) := do
  match ctx.finished with
  | some (.earlyTermination (.foundViolatingState fingerprint violations)) => do
    return ModelCheckingResult.foundViolation fingerprint (.safetyFailure violations) (some (← recoverTrace sys ctx fingerprint))
  | some (.earlyTermination (.deadlockOccurred fingerprint)) => do
    return ModelCheckingResult.foundViolation fingerprint .deadlock (some (← recoverTrace sys ctx fingerprint))
  | some (.earlyTermination (.assertionFailed fingerprint exId)) => do
    return ModelCheckingResult.foundViolation fingerprint (.assertionFailure exId) (some (← recoverTrace sys ctx fingerprint (some exId)))
  | some (.earlyTermination (.reachedDepthBound _)) =>
    -- No violation found within depth bound; report number of states explored
    return ModelCheckingResult.noViolationFound distinctCount (.earlyTermination (.reachedDepthBound ctx.completedDepth))
  | some (.earlyTermination .cancelled) =>
    -- Search was cancelled by the user
    return ModelCheckingResult.cancelled
  | some (.exploredAllReachableStates) => do
    match ctx.violatingStates with
    | (fingerprint, violation) :: _ =>
      -- For assertion failures, pass the exception ID to recover the failing step
      let assertionExId := match violation with
        | .assertionFailure exId => some exId
        | _ => none
      return ModelCheckingResult.foundViolation fingerprint violation (some (← recoverTrace sys ctx fingerprint assertionExId))
    | [] =>
      return ModelCheckingResult.noViolationFound distinctCount (.exploredAllReachableStates)
  | none => panic! s!"SearchContext.finished is none! This should never happen."

/-- Run `act`, and only then let go of `keep`, which is part of the result. If inlined, the caller
would take the pair apart right away and release `keep` before `act` runs; a function that just
ignored `keep` would not work either, since the compiler drops unused parameters. -/
@[noinline] private def keepingThen {m : Type → Type} [Monad m] {α β : Type} (keep : β) (act : m α) :
    m (α × β) := do
  let a ← act
  pure (a, keep)

section

variable {ρ σ κ σₕ α : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [inhabσ : Inhabited σ] [Repr κ]
  [ActionStatUpdate κ asm]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  [fp : StateFingerprint σ σₕ] [Ord σₕ] [Std.TransOrd σₕ] [Std.LawfulBEqOrd σₕ] [Repr σₕ] [Inhabited σₕ]
  (params : SearchParameters ρ σ)
  (parallelCfg : Option ParallelConfig)
  (progressInstanceId : Nat)
  (cancelToken : IO.CancelToken)

/-- `findReachable`, then `finish` on the result while the search's data structures (the seen
set, the log for recovering traces) are still referenced; they are released only after `finish`
returns. The caller picks the fingerprint type `σₕ` and its `StateFingerprint` instance. -/
def findReachableThen (finish : ModelCheckingResult ρ σ κ σₕ → m α) : m α := do
  let assumptionViolations := params.violatedAssumptions th
  unless assumptionViolations.isEmpty do
    setViolationFound progressInstanceId
    return ← finish (ModelCheckingResult.foundViolation default (.assumptionFailure assumptionViolations) none)
  -- Create a "filtered" version of the system
  let sys := Veil.ModelChecker.restrictSystemByStateConstraints sys params th
  match parallelCfg with
  | some cfg => do
    let mctx ← breadthFirstSearchParallel (σₕ := σₕ) params sys cfg progressInstanceId cancelToken
    let result ← searchResult sys mctx.base mctx.globalSeen.size
    return (← keepingThen mctx (finish result)).1
  | none => do
    let sctx ← breadthFirstSearchSequential (σₕ := σₕ) params sys 60000 progressInstanceId cancelToken
    let result ← searchResult sys sctx.1 sctx.1.log.size
    return (← keepingThen sctx (finish result)).1

def findReachable : m (ModelCheckingResult ρ σ κ σₕ) :=
  findReachableThen (σₕ := σₕ) sys params parallelCfg progressInstanceId cancelToken pure

end

end Veil.ModelChecker.Concrete
