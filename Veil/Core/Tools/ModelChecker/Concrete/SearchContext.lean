module

public import Veil.Core.Tools.ModelChecker.Concrete.Core
public import Veil.Core.Tools.ModelChecker.Concrete.Subtypes
public import Veil.Core.Tools.ModelChecker.Concrete.Containers
public import Veil.Core.Tools.ModelChecker.Concrete.TraceRecovery
public import Veil.Util.ShardedMapUInt

public section

namespace Veil.ModelChecker.Concrete

section Sequential

/-- The state of a sequential search. Its log doubles as its seen set. -/
structure SequentialSearchContext (σ κ σₕ asm : Type) [fp : StateFingerprint σ σₕ] [ActionStatUpdate κ asm] where
  base : BaseSearchContext σ κ σₕ asm
  /-- The seen set, with how each seen state was first reached; `recoverTrace` rebuilds a
  counterexample trace from it. -/
  log : Std.HashMap σₕ (LogEntry σₕ κ)
  queue : fQueue (QueueItem σₕ σ)

variable {ρ σ κ σₕ asm : Type}
  [fp : StateFingerprint σ σₕ]
  [ActionStatUpdate κ asm]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  (params : SearchParameters ρ σ)

/-- A sequential search context is stable closed if for any reachable state `u`
that has been seen and has been fully processed (i.e., not in the queue, not being
processed), then all its successful successors have also been seen. -/
abbrev SequentialSearchContext.isStableClosed (sctx : SequentialSearchContext σ κ σₕ asm)
  -- (Optional) state that is currently being processed
  (stateInTransit : Option σ) : Prop :=
  Function.InjectiveOn fp.view sys.reachable →
    (sctx.base.finished = some (.exploredAllReachableStates) ∨ sctx.base.finished = none) →
      ∀ u, sys.reachable u → u ∉ stateInTransit → (fp.view u) ∈ sctx.log →
        (∀ d : Nat, ⟨fp.view u, u, d⟩ ∉ sctx.queue) →
          ∀ l v, (l, ExecutionOutcome.success v) ∈ sys.tr th u →
            (fp.view v) ∈ sctx.log

-- TODO conjecture: executable things should not become part of this structure
-- (e.g., arguments), otherwise some reference counting will boom?
structure SequentialSearchContextInvariants
  (stateInTransit : Option σ)
  (sctx : SequentialSearchContext σ κ σₕ asm)
extends @SearchContextInvariants ρ σ κ σₕ fp th sys params (fun (x : σₕ) (st : σ) => ∃ d, ⟨x, st, d⟩ ∈ sctx.queue) (· ∈ sctx.log)
where
  -- NOTE: should be strengthened to talk about depth, with this
  -- being a special case
  init_states_included : ∀ s ∈ sys.initStates, (fp.view s) ∈ sctx.log
  terminate_empty_queue : sctx.base.finished = some (.exploredAllReachableStates) → sctx.queue.isEmpty
  stable_closed : sctx.isStableClosed sys stateInTransit

/-- The log of a sequential search describes, through the representatives `rep`, the states
the search has queued and the violations it has recorded. Kept apart from
`SequentialSearchContextInvariants`, since it is preserved for a growing `rep`. -/
structure SequentialSearchContext.LogSound (sctx : SequentialSearchContext σ κ σₕ asm)
    (rep : σₕ → Option σ) (dep : σₕ → Nat) : Prop
    extends BaseSearchContext.ViolationTerminationSound sys params sctx.base rep where
  log_invs : LogInvariants sys (logLookup sctx.log) rep dep
  queue_rep : ∀ item ∈ sctx.queue, rep item.fingerprint = some item.state

abbrev LawfulSequentialSearchContext (stateInTransit : Option σ := .none) : Type :=
  Subtype (α := SequentialSearchContext σ κ σₕ asm) fun sctx =>
    SequentialSearchContextInvariants sys params stateInTransit sctx ∧ ∃ rep dep, sctx.LogSound sys params rep dep

end Sequential

section MapReduce

/-- The seen set of the parallel search, which is also its log: for each fingerprint it has seen,
how the search first reached a state of that fingerprint, in shards of type `Shard`. -/
abbrev MapReduceGlobalSeen (σₕ κ Shard : Type) : Type := ShardedMapUSize σₕ (LogEntry σₕ κ) Shard

structure MapReduceSearchContextMain (σ κ σₕ asm Shard : Type) [fp : StateFingerprint σ σₕ] [ActionStatUpdate κ asm] where
  base : BaseSearchContext σ κ σₕ asm
  tovisitLen : Nat
  tovisit : List (MapReduceQueueItem σₕ σ κ)
  /-- The seen set, which is also the log: how the search first reached each state it has seen,
  by fingerprint; `recoverTrace` rebuilds a counterexample trace from it. -/
  globalSeen : MapReduceGlobalSeen σₕ κ Shard

/-- The state of a worker of the parallel search. -/
structure MapReduceSearchContextLocal (σ κ σₕ asm : Type) [fp : StateFingerprint σ σₕ] [ActionStatUpdate κ asm] where
  base : BaseSearchContext σ κ σₕ asm
  /-- The fingerprints of the states in `queue`, to deduplicate within the worker. -/
  seen : Std.HashSet σₕ
  /-- The states the worker found new, each with its log entry. -/
  queue : List (MapReduceQueueItem σₕ σ κ)

variable {ρ σ κ σₕ asm : Type}
  [fp : StateFingerprint σ σₕ]
  [ActionStatUpdate κ asm]
  {Shard : Type} [Membership σₕ Shard]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  (params : SearchParameters ρ σ)

/-- A map-reduce main context is stable closed if for any reachable state `u`
that has been seen (in globalSeen) and has been fully processed (i.e., not in the
frontier array), then all its successful successors have also been seen. -/
abbrev MapReduceSearchContextMain.isStableClosed (mctx : MapReduceSearchContextMain σ κ σₕ asm Shard) : Prop :=
  Function.InjectiveOn fp.view sys.reachable →
    (mctx.base.finished = some (.exploredAllReachableStates) ∨ mctx.base.finished = none) →
      ∀ u, sys.reachable u → (fp.view u) ∈ mctx.globalSeen →
        (∀ item ∈ mctx.tovisit, item.fingerprint ≠ fp.view u) →
          ∀ l v, (l, ExecutionOutcome.success v) ∈ sys.tr th u →
            (fp.view v) ∈ mctx.globalSeen

structure MapReduceSearchContextMainInvariants
  (mctx : MapReduceSearchContextMain σ κ σₕ asm Shard)
extends @SearchContextInvariants ρ σ κ σₕ fp th sys params (fun x st => ∃ e, ⟨x, st, e⟩ ∈ mctx.tovisit) (· ∈ mctx.globalSeen)
where
  init_states_included : ∀ s ∈ sys.initStates, (fp.view s) ∈ mctx.globalSeen
  terminate_empty_queue : mctx.base.finished = some (.exploredAllReachableStates) → mctx.tovisit.isEmpty
  stable_closed : mctx.isStableClosed sys
  tovisit_len : mctx.tovisitLen = mctx.tovisit.length

abbrev LawfulMapReduceSearchContextMain : Type :=
  Subtype (α := MapReduceSearchContextMain σ κ σₕ asm Shard) (MapReduceSearchContextMainInvariants sys params)

structure MapReduceSearchContextLocalInvariants
  (globalSeen : MapReduceGlobalSeen σₕ κ Shard)
  (visited : MapReduceQueueItem σₕ σ κ → Prop)
  (lctx : MapReduceSearchContextLocal σ κ σₕ asm)
extends @SearchContextInvariants ρ σ κ σₕ fp th sys params (fun x st => ∃ e, ⟨x, st, e⟩ ∈ lctx.queue) (fun h => ∃ s e, ⟨h, s, e⟩ ∈ lctx.queue)
where
  not_explored_all : lctx.base.finished ≠ some (.exploredAllReachableStates)   -- OK, but why?
  tovisit_globalSeen_disjoint : ∀ item ∈ lctx.queue, item.fingerprint ∉ globalSeen
  -- NOTE: This might be eventually removed
  tovisit_seen_same_domain : ∀ fpSt, fpSt ∈ lctx.seen ↔ ∃ item ∈ lctx.queue, item.fingerprint = fpSt
  successor_collected : lctx.base.finished = none → ∀ fingerprint st e, visited ⟨fingerprint, st, e⟩ →
    ∀ (l : κ) (v : σ), (l, .success v) ∈ sys.tr th st →
      ((fp.view v) ∈ globalSeen ∨
        fp.view v ∈ lctx.seen)

/-- What a worker's results say through the representatives `rep`: the entry of each item it has
queued is a transition from the representative of the entry's parent, and each violation it has
recorded is exhibited by the representative of its fingerprint. -/
structure MapReduceSearchContextLocal.LogSound (lctx : MapReduceSearchContextLocal σ κ σₕ asm)
    (rep : σₕ → Option σ) : Prop
    extends BaseSearchContext.ViolationTerminationSound sys params lctx.base rep where
  entries_sound : ∀ item ∈ lctx.queue, ∃ p l i sp, item.entry = .step p l i ∧ rep p = some sp ∧
    (sys.tr th sp).successes[i]? = some (l, item.state)

/-- A worker's context with its invariants, and its `LogSound` for any `rep` that maps the items
it has processed (`visited`) to their states, so that the merge can apply it to the
representatives of the main context. -/
abbrev LawfulMapReduceSearchContextLocal
  (globalSeen : MapReduceGlobalSeen σₕ κ Shard)
  (visited : MapReduceQueueItem σₕ σ κ → Prop) : Type :=
  Subtype (α := MapReduceSearchContextLocal σ κ σₕ asm) fun lctx =>
    MapReduceSearchContextLocalInvariants sys params globalSeen visited lctx ∧
    ∀ rep : σₕ → Option σ, (∀ c, visited c → rep c.fingerprint = some c.state) → lctx.LogSound sys params rep

end MapReduce

end Veil.ModelChecker.Concrete
