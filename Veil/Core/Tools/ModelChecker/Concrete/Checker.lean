module

public import Veil.Core.Tools.ModelChecker.Concrete.Sequential
public import Veil.Core.Tools.ModelChecker.Concrete.MapReduce
public import Veil.Util.HAMTShard

public section

namespace Veil.ModelChecker.Concrete

/-! ## Model Checker

This module provides the main entry point for model checking, dispatching to
either the sequential or parallel implementation based on configuration. -/

/-- The result of a finished search, with a trace for a violation, recovered in `sys` from the
search's log `look`: the log is sound for some representatives, which exhibit the violations that
`ctx` records. The picks of the trace come from `pickSource`, which is built only for a trace. -/
def searchResult {ρ σ κ σₕ : Type} [ActionStatUpdate κ asm] {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  (pickSource : Unit → PickSource σ κ)
  (params : SearchParameters ρ σ) [fp : StateFingerprint σ σₕ]
  (ctx : BaseSearchContext σ κ σₕ asm) (look : LogLookup σₕ κ) (distinctCount : Nat)
  (h : ∃ rep dep, LogInvariants sys look rep dep ∧ ctx.ViolationTerminationSound sys params rep) :
  ModelCheckingResult ρ σ κ σₕ :=
  match hf : ctx.finished with
  | some (.earlyTermination (.foundViolatingState x names)) =>
    let r := recoverViolationTrace sys (pickSource ()) params look x (.safetyFailure names) (by
      obtain ⟨rep, dep, hinv, -, hterm⟩ := h ; rw [hf] at hterm ; exact ⟨rep, dep, hinv, hterm⟩)
    .foundViolation x (.safetyFailure names) (some r.1) r.2
  | some (.earlyTermination (.deadlockOccurred x)) =>
    let r := recoverViolationTrace sys (pickSource ()) params look x .deadlock (by
      obtain ⟨rep, dep, hinv, -, hterm⟩ := h ; rw [hf] at hterm ; exact ⟨rep, dep, hinv, hterm⟩)
    .foundViolation x .deadlock (some r.1) r.2
  | some (.earlyTermination (.assertionFailed x exId)) =>
    let r := recoverViolationTrace sys (pickSource ()) params look x (.assertionFailure exId) (by
      obtain ⟨rep, dep, hinv, -, hterm⟩ := h ; rw [hf] at hterm ; exact ⟨rep, dep, hinv, hterm⟩)
    .foundViolation x (.assertionFailure exId) (some r.1) r.2
  | some (.earlyTermination (.reachedDepthBound _)) =>
    -- No violation found within depth bound; report number of states explored
    .noViolationFound distinctCount (.earlyTermination (.reachedDepthBound ctx.completedDepth))
  | some (.earlyTermination .cancelled) =>
    -- Search was cancelled by the user
    .cancelled
  | some .exploredAllReachableStates =>
    match hv : ctx.violatingStates with
    | (x, violation) :: _ =>
      let r := recoverViolationTrace sys (pickSource ()) params look x violation (by
        obtain ⟨rep, dep, hinv, hviol, -⟩ := h
        exact ⟨rep, dep, hinv, hviol _ (by rw [hv] ; exact List.mem_cons_self)⟩)
      .foundViolation x violation (some r.1) r.2
    | [] => .noViolationFound distinctCount .exploredAllReachableStates
  | none => panic! s!"SearchContext.finished is none! This should never happen."

/-- The result of a search is sound: each violation it reports comes with a trace that is valid in
`sys` and ends at a state that exhibits the violation. -/
theorem searchResult_sound {ρ σ κ σₕ : Type} [ActionStatUpdate κ asm] {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  (pickSource : Unit → PickSource σ κ)
  (params : SearchParameters ρ σ) [fp : StateFingerprint σ σₕ]
  (ctx : BaseSearchContext σ κ σₕ asm) (look : LogLookup σₕ κ) (distinctCount : Nat)
  (h : ∃ rep dep, LogInvariants sys look rep dep ∧ ctx.ViolationTerminationSound sys params rep) :
  ResultSound sys params (searchResult sys pickSource params ctx look distinctCount h) := by
  unfold searchResult
  split <;> (try split) <;> first | exact recoverViolationTrace_sound sys _ | trivial

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
  -- The initial states and transitions of `sys` computed with the picks logged (`LogSwitch`), which
  -- the search runs without: the picks of a counterexample trace come from it. It is a thunk, so
  -- that it is built only when there is a trace.
  (pickSource : Unit → PickSource σ κ)
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
`ShardOf` of the type of the values. Traces are recovered in `sys`, from the log of the search,
with the picks of their states from `pickSource`. -/
def findReachableThen (finish : ModelCheckingResult ρ σ κ σₕ → m α) : m α := do
  let assumptionViolations := params.violatedAssumptions th
  unless assumptionViolations.isEmpty do
    setViolationFound progressInstanceId
    return ← finish (ModelCheckingResult.foundViolation default (.assumptionFailure assumptionViolations) none {})
  -- Create a "filtered" version of the system
  let sys := Veil.ModelChecker.restrictSystemByStateConstraints sys params th
  let pickSource := fun _ => (pickSource ()).restrictByStateConstraints params th
  match parallelCfg with
  | some cfg => do
    let mctx ← breadthFirstSearchParallel (σₕ := σₕ) (Shard := ShardOf (LogEntry σₕ κ)) params sys cfg
      progressInstanceId cancelToken
    let result := searchResult sys pickSource params mctx.val.base mctx.val.globalSeen.get? mctx.val.globalSeen.size
      (mctx.property.2.elim fun rep h => h.elim fun dep h => ⟨rep, dep, h.log_invs, h.toViolationTerminationSound⟩)
    return (← keepingThen mctx (finish result)).1
  | none => do
    let sctx ← breadthFirstSearchSequential (σₕ := σₕ) params sys 60000 progressInstanceId cancelToken
    let result := searchResult sys pickSource params sctx.val.base (logLookup sctx.val.log) sctx.val.log.size
      (sctx.property.2.elim fun rep h => h.elim fun dep h => ⟨rep, dep, h.log_invs, h.toViolationTerminationSound⟩)
    return (← keepingThen sctx (finish result)).1

def findReachable : m (ModelCheckingResult ρ σ κ σₕ) :=
  findReachableThen (σₕ := σₕ) (ShardOf := ShardOf) sys pickSource params parallelCfg progressInstanceId cancelToken pure

end

end Veil.ModelChecker.Concrete
