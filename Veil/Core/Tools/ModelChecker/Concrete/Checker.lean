module

public import Veil.Core.Tools.ModelChecker.Concrete.Sequential
public import Veil.Core.Tools.ModelChecker.Concrete.MapReduce
public import Veil.Util.HAMTShard

public section

namespace Veil.ModelChecker.Concrete

/-! ## Model Checker

This module provides the main entry point for model checking, dispatching to
either the sequential or parallel implementation based on configuration. -/

/-- The trace to the state recorded against `fingerprint`, re-executed in `sys`, with the failing
step when the violation is an assertion failure with exception `assertionFailureExId`. -/
private def recoverViolationTrace {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT IO m]
  [StateFingerprint σ σₕ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  (look : LogLookup σₕ κ)
  (fingerprint : σₕ)
  (assertionFailureExId : Option Int := none)
  : m (Trace ρ σ κ) := do
  match recoverTrace? sys look fingerprint with
  | some trace =>
    let failingStep := assertionFailureExId.bind fun exId =>
      (sys.tr th trace.lastState).failures.find? (·.error == exId) |>.map fun f =>
        { transitionLabel := f.label, nextState := f.state }
    return { trace with failingStep := failingStep }
  | none => IO.ofExcept <| Except.error s!"Could not recover a trace for the state {repr fingerprint}!"

/-- The result of a finished search, with a trace for a violation, recovered in `traceSys ()` from
the search's log `look`. `completedDepth` is the depth the search has completed. -/
private def searchResult {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [ActionStatUpdate κ asm]
  {th : ρ}
  (traceSys : Unit → EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  [fp : StateFingerprint σ σₕ] [Repr σₕ]
  (ctx : BaseSearchContext σ κ σₕ asm) (completedDepth : Nat) (look : LogLookup σₕ κ) (distinctCount : Nat)
  : m (ModelCheckingResult ρ σ κ σₕ) := do
  match ctx.finished with
  | some (.earlyTermination (.foundViolatingState fingerprint violations)) => do
    return ModelCheckingResult.foundViolation fingerprint (.safetyFailure violations) (some (← recoverViolationTrace (traceSys ()) look fingerprint))
  | some (.earlyTermination (.deadlockOccurred fingerprint)) => do
    return ModelCheckingResult.foundViolation fingerprint .deadlock (some (← recoverViolationTrace (traceSys ()) look fingerprint))
  | some (.earlyTermination (.assertionFailed fingerprint exId)) => do
    return ModelCheckingResult.foundViolation fingerprint (.assertionFailure exId) (some (← recoverViolationTrace (traceSys ()) look fingerprint (some exId)))
  | some (.earlyTermination (.reachedDepthBound _)) =>
    -- No violation found within depth bound; report number of states explored
    return ModelCheckingResult.noViolationFound distinctCount (.earlyTermination (.reachedDepthBound completedDepth))
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
      return ModelCheckingResult.foundViolation fingerprint violation (some (← recoverViolationTrace (traceSys ()) look fingerprint assertionExId))
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
  [Repr κ]
  [ActionStatUpdate κ asm]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  -- The system to recover counterexample traces in. It must have the transitions of `sys`, in the
  -- same order, since the log records transitions by their position: the frontend passes `sys`
  -- with picks logged (`LogSwitch`), which the search does without. It is a thunk, so that it is
  -- built only when there is a trace to recover.
  (traceSys : Unit → EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  [fp : StateFingerprint σ σₕ] {ShardOf : Type → Type} [Membership σₕ (ShardOf (LogEntry σₕ κ))]
  [MapShard σₕ (LogEntry σₕ κ) (ShardOf (LogEntry σₕ κ))] [Repr σₕ] [Inhabited σₕ]
  (params : SearchParameters ρ σ)
  (parallelCfg : Option ParallelConfig)
  (progressInstanceId : Nat)
  (cancelToken : IO.CancelToken)

/-- `findReachable`, then `finish` on the result while the search's data structures (the seen
set, the log for recovering traces) are still referenced; they are released only after `finish`
returns. The caller picks the fingerprint type `σₕ` and its `StateFingerprint` instance, and the
map type of the shards of the parallel search's seen set, which also holds its log, as a function
`ShardOf` of the type of the values. Traces are recovered in `traceSys ()` rather than `sys`. -/
def findReachableThen (finish : ModelCheckingResult ρ σ κ σₕ → m α) : m α := do
  let assumptionViolations := params.violatedAssumptions th
  unless assumptionViolations.isEmpty do
    setViolationFound progressInstanceId
    return ← finish (ModelCheckingResult.foundViolation default (.assumptionFailure assumptionViolations) none)
  -- Create a "filtered" version of the system
  let sys := Veil.ModelChecker.restrictSystemByStateConstraints sys params th
  let traceSys := fun _ => Veil.ModelChecker.restrictSystemByStateConstraints (traceSys ()) params th
  match parallelCfg with
  | some cfg => do
    let mctx ← breadthFirstSearchParallel (σₕ := σₕ) (Shard := ShardOf (LogEntry σₕ κ)) params sys cfg
      progressInstanceId cancelToken
    let result ← searchResult traceSys mctx.base mctx.completedDepth mctx.globalSeen.get? mctx.globalSeen.size
    return (← keepingThen mctx (finish result)).1
  | none => do
    let sctx ← breadthFirstSearchSequential (σₕ := σₕ) params sys 60000 progressInstanceId cancelToken
    let result ← searchResult traceSys sctx.val.base sctx.val.completedDepth (logLookup sctx.val.log) sctx.val.log.size
    return (← keepingThen sctx (finish result)).1

def findReachable : m (ModelCheckingResult ρ σ κ σₕ) :=
  findReachableThen (σₕ := σₕ) (ShardOf := ShardOf) sys traceSys params parallelCfg progressInstanceId cancelToken pure

end

end Veil.ModelChecker.Concrete
