import Veil.Core.Tools.ModelChecker.ConcreteNew.Core
import Veil.Core.Tools.ModelChecker.Concrete.Subtypes
import Veil.Core.Tools.ModelChecker.Concrete.Containers

namespace Veil.ModelChecker.Concrete

/-- The frontier-closed property: all states that are discovered (in `seen`) and not in the frontier
    (not in `tovisit`) have all their successors discovered. This is the key invariant for BFS correctness.
    This version uses HashSet for O(1) membership checking. -/
abbrev FrontierClosed {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (seen : Std.HashSet σₕ)
  (tovisitSet : Std.HashSet σₕ)
  (finished : Option (TerminationReason σₕ)) : Prop :=
  Function.Injective fp.view →
    (finished = some (.exploredAllReachableStates) ∨ finished = none) →
    ∀ (s : σ), fp.view s ∈ seen →
      (fp.view s ∉ tovisitSet) →
      ∀ l next_s, (l, .success next_s) ∈ sys.tr th s →
      fp.view next_s ∈ seen


/-- The property that all successors of items in `items` satisfy the `inSeen` predicate.
    Used as a key invariant in parallel BFS to express that successors have been collected. -/
abbrev SuccessorsCollected {ρ σ κ σₕ : Type _}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (inQueue : QueueItem σₕ σ → Prop)
  (hasFinished : Bool)
  (seen : σₕ → Prop) : Prop :=
  !hasFinished → ∀ fingerprint st d, inQueue ⟨fingerprint, st, d⟩ →
    ∀ (l : κ) (v : σ), (l, .success v) ∈ sys.tr th st →
    seen (fp.view v)


structure SequentialSearchContext {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
extends @BaseSearchContext ρ σ κ σₕ fp instBEq instHash th sys params
where
  sq    : fQueue (QueueItem σₕ σ)
  invs  : @SearchContextInvariants ρ σ κ σₕ fp th sys params (Membership.mem sq) (Membership.mem seen)
  terminate_empty_queue : finished = some (.exploredAllReachableStates) → sq.isEmpty
  stable_closed :  Function.Injective fp.view →
    (finished = some (.exploredAllReachableStates) ∨ finished = none)
      → ∀ u : σ, (fp.view u) ∈ seen → (∀ d : Nat, ⟨fp.view u, u, d⟩ ∉ sq) →
      ∀l v, (l, ExecutionOutcome.success v) ∈ sys.tr th u → (fp.view v) ∈ seen


structure ParallelSearchContext {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
extends @BaseSearchContext ρ σ κ σₕ fp instBEq instHash th sys params
where
  /-- Recording the nodes to visit in the next depth as an Array for efficient iteration/splitting. -/
  tovisitQueue : Array (QueueItem σₕ σ)
  /-- HashSet for O(1) membership checking of fingerprints in the queue. -/
  tovisitSet : Std.HashSet σₕ
  /-- Consistency between queue and set: a fingerprint is in the set iff some item with that fingerprint is in the queue. -/
  tovisitConsistent : ∀ h, h ∈ tovisitSet ↔ ∃ item ∈ tovisitQueue, item.fingerprint = h
  invs  : @SearchContextInvariants ρ σ κ σₕ fp th sys params (Membership.mem tovisitQueue) (Membership.mem seen)
  frontier_closed : FrontierClosed sys seen tovisitSet finished
  starts_in_seen : ∀s₀, s₀ ∈ sys.initStates → fp.view s₀ ∈ seen
  terminate_empty_tovisit :
    finished = some (.exploredAllReachableStates) → tovisitQueue.isEmpty


structure LocalSearchContext {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
extends @BaseSearchContext ρ σ κ σₕ fp instBEq instHash th sys params
where
  /-- Recording the nodes to visit as an Array for efficient iteration. -/
  tovisitQueue : Array (QueueItem σₕ σ)
  /-- HashSet for O(1) membership checking of fingerprints in the queue. -/
  tovisitSet : Std.HashSet σₕ
  /-- Consistency between queue and set: a fingerprint is in the set iff some item with that fingerprint is in the queue. -/
  tovisitConsistent : ∀ h, h ∈ tovisitSet ↔ ∃ item ∈ tovisitQueue, item.fingerprint = h
  localLog : Std.HashMap σₕ (σₕ × κ)
  seenUnaltered : ∀s, s ∈ baseCtx.seen ↔ s ∈ seen
  invs : @SearchContextInvariants ρ σ κ σₕ fp th sys params (Membership.mem tovisitQueue) (fun h => h ∈ seen ∨ h ∈ tovisitSet)
  /-- Local count of post-states generated (before deduplication) -/
  localStatesFound : Nat := 0
  /-- Local per-action statistics: label → stats -/
  localActionStatsMap : Std.HashMap κ ActionStat := {}
  excludeAllStatesFinish : finished ≠ some (.exploredAllReachableStates)


/-- Merge action stats maps by summing counts for each action. -/
private def mergeActionStatsMaps [BEq κ] [Hashable κ] (m1 m2 : Std.HashMap κ ActionStat) : Std.HashMap κ ActionStat :=
  m2.fold (init := m1) fun acc label stat2 =>
    match acc[label]? with
    | some stat1 => acc.insert label { statesGenerated := stat1.statesGenerated + stat2.statesGenerated, distinctStates := stat1.distinctStates + stat2.distinctStates }
    | none => acc.insert label stat2

end Veil.ModelChecker.Concrete
