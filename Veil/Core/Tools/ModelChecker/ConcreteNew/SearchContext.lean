import Veil.Core.Tools.ModelChecker.ConcreteNew.Core
import Veil.Core.Tools.ModelChecker.Concrete.Subtypes
import Veil.Core.Tools.ModelChecker.Concrete.Containers

namespace Veil.ModelChecker.Concrete

section Sequential

abbrev SequentialSearchContext (σ κ σₕ : Type) [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ] :=
  BaseSearchContext σ κ σₕ × fQueue (QueueItem σₕ σ)

variable {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)

/-- A sequential search context is stable closed if for any state `u` that
has been seen and has been fully processed (i.e., not in the queue, not being
processed), then all its successfully reachable have also been seen. -/
abbrev SequentialSearchContext.isStableClosed (sctx : SequentialSearchContext σ κ σₕ)
  -- (Optional) state that is currently being processed
  (stateInTransit : Option σ) : Prop :=
  Function.Injective fp.view →
    (sctx.1.finished = some (.exploredAllReachableStates) ∨ sctx.1.finished = none) →
      ∀ u ∉ stateInTransit, (fp.view u) ∈ sctx.1.log →
        (∀ d : Nat, ⟨fp.view u, u, d⟩ ∉ sctx.2) →
          ∀ l v, (l, ExecutionOutcome.success v) ∈ sys.tr th u →
            (fp.view v) ∈ sctx.1.log

-- TODO conjecture: executable things should not become part of this structure
-- (e.g., arguments), otherwise some reference counting will boom?
structure SequentialSearchContextInvariants
  (stateInTransit : Option σ)
  (sctx : SequentialSearchContext σ κ σₕ)
extends @SearchContextInvariants ρ σ κ σₕ fp th sys params (fun (x : σₕ) (st : σ) => ∃ d, ⟨x, st, d⟩ ∈ sctx.2) (· ∈ sctx.1.log)
where
  -- NOTE: should be strengthened to talk about depth, with this
  -- being a special case
  init_states_included : ∀ s ∈ sys.initStates, (fp.view s) ∈ sctx.1.log
  terminate_empty_queue : sctx.1.finished = some (.exploredAllReachableStates) → sctx.2.isEmpty
  stable_closed : sctx.isStableClosed sys stateInTransit

abbrev LawfulSequentialSearchContext (stateInTransit : Option σ := .none) : Type :=
  Subtype (α := SequentialSearchContext σ κ σₕ) (SequentialSearchContextInvariants sys params stateInTransit)

end Sequential

section MapReduce

structure MapReduceSearchContextMain (σ κ σₕ : Type) [fp : StateFingerprint σ σₕ] [Ord σₕ] [BEq κ] [Hashable κ] where
  base : BaseSearchContext σ κ σₕ
  tovisitLen : Nat
  tovisit : List (MapReduceQueueItem σₕ σ)
  globalSeen : Std.TreeSet σₕ

abbrev MapReduceSearchContextLocal (σ κ σₕ : Type) [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ] :=
  BaseSearchContext σ κ σₕ × List (MapReduceQueueItem σₕ σ)

structure MapReduceSearchContextTemp (σ κ σₕ : Type) [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ] where
  base : BaseSearchContext σ κ σₕ
  tovisit : List (MapReduceQueueItem σₕ σ)
  tempSeen : Std.HashSet σₕ

variable {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ]
  [Ord σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)

/-- A map-reduce main context is stable closed if for any state `u` that
has been seen (in globalSeen) and has been fully processed (i.e., not in the
frontier array), then all its successfully reachable states have also been seen. -/
abbrev MapReduceSearchContextMain.isStableClosed (mctx : MapReduceSearchContextMain σ κ σₕ) : Prop :=
  Function.Injective fp.view →
    (mctx.base.finished = some (.exploredAllReachableStates) ∨ mctx.base.finished = none) →
      ∀ u, (fp.view u) ∈ mctx.globalSeen →
        (∀ item ∈ mctx.tovisit, item.fingerprint ≠ fp.view u) →
          ∀ l v, (l, ExecutionOutcome.success v) ∈ sys.tr th u →
            (fp.view v) ∈ mctx.globalSeen

structure MapReduceSearchContextMainInvariants
  (mctx : MapReduceSearchContextMain σ κ σₕ)
extends @SearchContextInvariants ρ σ κ σₕ fp th sys params (fun x st => ⟨x, st⟩ ∈ mctx.tovisit) (· ∈ mctx.globalSeen)
where
  init_states_included : ∀ s ∈ sys.initStates, (fp.view s) ∈ mctx.globalSeen
  terminate_empty_queue : mctx.base.finished = some (.exploredAllReachableStates) → mctx.tovisit.isEmpty
  stable_closed : mctx.isStableClosed sys
  tovisit_len : mctx.tovisitLen = mctx.tovisit.length

abbrev LawfulMapReduceSearchContextMain : Type :=
  Subtype (α := MapReduceSearchContextMain σ κ σₕ) (MapReduceSearchContextMainInvariants sys params)

structure MapReduceSearchContextLocalInvariants
  (globalSeen : Std.TreeSet σₕ)
  (visited : MapReduceQueueItem σₕ σ → Prop)
  (lctx : MapReduceSearchContextLocal σ κ σₕ)
extends @SearchContextInvariants ρ σ κ σₕ fp th sys params (fun x st => ⟨x, st⟩ ∈ lctx.2) (fun h => ∃ s, ⟨h, s⟩ ∈ lctx.2)
where
  not_explored_all : lctx.1.finished ≠ some (.exploredAllReachableStates)   -- OK, but why?
  tovisit_globalSeen_disjoint : ∀ item ∈ lctx.2, item.fingerprint ∉ globalSeen
  -- NOTE: This might be eventually removed
  tovisit_log_same_domain : ∀ fpSt, fpSt ∈ lctx.1.log ↔ ∃ item ∈ lctx.2, item.fingerprint = fpSt
  successor_collected : lctx.1.finished = none → ∀ fingerprint st, visited ⟨fingerprint, st⟩ →
    ∀ (l : κ) (v : σ), (l, .success v) ∈ sys.tr th st →
      ((fp.view v) ∈ globalSeen ∨
        fp.view v ∈ lctx.1.log)

abbrev LawfulMapReduceSearchContextLocal
  (globalSeen : Std.TreeSet σₕ)
  (visited : MapReduceQueueItem σₕ σ → Prop) : Type :=
  Subtype (α := MapReduceSearchContextLocal σ κ σₕ) (MapReduceSearchContextLocalInvariants sys params globalSeen visited)

end MapReduce

end Veil.ModelChecker.Concrete
