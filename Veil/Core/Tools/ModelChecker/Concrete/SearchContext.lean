module

public import Veil.Core.Tools.ModelChecker.Concrete.Core
public import Veil.Core.Tools.ModelChecker.Concrete.Subtypes
public import Veil.Core.Tools.ModelChecker.Concrete.Containers
public import Veil.Core.Tools.ModelChecker.Concrete.TraceRecovery

public section

namespace Veil.ModelChecker.Concrete

section Sequential

abbrev SequentialSearchContext (σ κ σₕ asm : Type) [fp : StateFingerprint σ σₕ] [ActionStatUpdate κ asm] :=
  BaseSearchContext σ κ σₕ asm × fQueue (QueueItem σₕ σ)

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
    (sctx.1.finished = some (.exploredAllReachableStates) ∨ sctx.1.finished = none) →
      ∀ u, sys.reachable u → u ∉ stateInTransit → (fp.view u) ∈ sctx.1.log →
        (∀ d : Nat, ⟨fp.view u, u, d⟩ ∉ sctx.2) →
          ∀ l v, (l, ExecutionOutcome.success v) ∈ sys.tr th u →
            (fp.view v) ∈ sctx.1.log

-- TODO conjecture: executable things should not become part of this structure
-- (e.g., arguments), otherwise some reference counting will boom?
structure SequentialSearchContextInvariants
  (stateInTransit : Option σ)
  (sctx : SequentialSearchContext σ κ σₕ asm)
extends @SearchContextInvariants ρ σ κ σₕ fp th sys params (fun (x : σₕ) (st : σ) => ∃ d, ⟨x, st, d⟩ ∈ sctx.2) (· ∈ sctx.1.log)
where
  -- NOTE: should be strengthened to talk about depth, with this
  -- being a special case
  init_states_included : ∀ s ∈ sys.initStates, (fp.view s) ∈ sctx.1.log
  terminate_empty_queue : sctx.1.finished = some (.exploredAllReachableStates) → sctx.2.isEmpty
  stable_closed : sctx.isStableClosed sys stateInTransit

/-- The log of a sequential search describes, through the representatives `rep`, the states
the search has queued and the violations it has recorded. Kept apart from
`SequentialSearchContextInvariants`, since it is preserved for a growing `rep`. -/
structure SequentialSearchContext.LogSound (sctx : SequentialSearchContext σ κ σₕ asm)
    (rep : σₕ → Option σ) (dep : σₕ → Nat) : Prop where
  log_invs : LogInvariants sys (logLookup sctx.1.log) rep dep
  queue_rep : ∀ item ∈ sctx.2, rep item.fingerprint = some item.state
  violations_sound : ∀ v ∈ sctx.1.violatingStates, ViolationSound sys params rep v
  termination_sound : TerminationSound sys params rep sctx.1.finished

abbrev LawfulSequentialSearchContext (stateInTransit : Option σ := .none) : Type :=
  Subtype (α := SequentialSearchContext σ κ σₕ asm) fun sctx =>
    SequentialSearchContextInvariants sys params stateInTransit sctx ∧ ∃ rep dep, sctx.LogSound sys params rep dep

end Sequential

section MapReduce

structure MapReduceSearchContextMain (σ κ σₕ asm Shard : Type) [fp : StateFingerprint σ σₕ] [ActionStatUpdate κ asm] where
  base : BaseSearchContext σ κ σₕ asm
  tovisitLen : Nat
  tovisit : List (MapReduceQueueItem σₕ σ κ)
  globalSeen : ShardedSetUSize σₕ Shard
  /-- The log entries of the states kept by each BFS layer, *newest layer first*; not yet in
  `base.log`, which holds only the initial states. They are merged into a map only when a trace
  has to be recovered (`fullLog`). -/
  accumulatedLogs : List (List (σₕ × LogEntry σₕ κ)) := []

-- FIXME: It should not be necessary to maintain these kinds of logs ...
-- Probably, just rollback by depth?
/-- The whole log of the search: the entries of the initial states, then those of every round.
Built only when a trace has to be recovered. -/
def MapReduceSearchContextMain.fullLog [fp : StateFingerprint σ σₕ] [ActionStatUpdate κ asm] {Shard : Type}
    (mctx : MapReduceSearchContextMain σ κ σₕ asm Shard) : Std.HashMap σₕ (LogEntry σₕ κ) :=
  mctx.accumulatedLogs.foldr (fun entries acc => entries.foldl (fun acc (x, e) => acc.insert x e) acc) mctx.base.log

abbrev MapReduceSearchContextLocal (σ κ σₕ asm : Type) [fp : StateFingerprint σ σₕ] [ActionStatUpdate κ asm] :=
  BaseSearchContext σ κ σₕ asm × List (MapReduceQueueItem σₕ σ κ)

structure MapReduceSearchContextTemp (σ κ σₕ asm : Type) [fp : StateFingerprint σ σₕ] [ActionStatUpdate κ asm] (n : USize) where
  base : BaseSearchContext σ κ σₕ asm
  tovisit : List (MapReduceQueueItem σₕ σ κ)
  tempSeen : ShardedHashSetUSize σₕ n

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
  (globalSeen : ShardedSetUSize σₕ Shard)
  (visited : MapReduceQueueItem σₕ σ κ → Prop)
  (lctx : MapReduceSearchContextLocal σ κ σₕ asm)
extends @SearchContextInvariants ρ σ κ σₕ fp th sys params (fun x st => ∃ e, ⟨x, st, e⟩ ∈ lctx.2) (fun h => ∃ s e, ⟨h, s, e⟩ ∈ lctx.2)
where
  not_explored_all : lctx.1.finished ≠ some (.exploredAllReachableStates)   -- OK, but why?
  tovisit_globalSeen_disjoint : ∀ item ∈ lctx.2, item.fingerprint ∉ globalSeen
  -- NOTE: This might be eventually removed
  tovisit_log_same_domain : ∀ fpSt, fpSt ∈ lctx.1.log ↔ ∃ item ∈ lctx.2, item.fingerprint = fpSt
  successor_collected : lctx.1.finished = none → ∀ fingerprint st e, visited ⟨fingerprint, st, e⟩ →
    ∀ (l : κ) (v : σ), (l, .success v) ∈ sys.tr th st →
      ((fp.view v) ∈ globalSeen ∨
        fp.view v ∈ lctx.1.log)

abbrev LawfulMapReduceSearchContextLocal
  (globalSeen : ShardedSetUSize σₕ Shard)
  (visited : MapReduceQueueItem σₕ σ κ → Prop) : Type :=
  Subtype (α := MapReduceSearchContextLocal σ κ σₕ asm) (MapReduceSearchContextLocalInvariants sys params globalSeen visited)

end MapReduce

end Veil.ModelChecker.Concrete
