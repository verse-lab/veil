import Veil.Core.Tools.ModelChecker.Concrete.Core
import Veil.Core.Tools.ModelChecker.Concrete.Subtypes
import Veil.Core.Tools.ModelChecker.Concrete.DataLemmas

namespace Veil.ModelChecker.Concrete

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
  /-- Recording the nodes to visit in the next depth. Due to the way
  parallel BFS works, it could be any data structure that supports `O(1)`
  element insertion (e.g., `Array`); but to support efficient merging,
  it's made to be an `HashMap`. -/
  tovisit : Std.HashMap σₕ (σ × Nat)
  invs  : @SearchContextInvariants ρ σ κ σₕ fp th sys params (fun ⟨h, x, d⟩ => tovisit[h]? = some (x, d)) (Membership.mem seen)
  frontier_closed : Function.Injective fp.view →
    (finished = some (.exploredAllReachableStates) ∨ finished = none) →
    ∀ (s : σ), fp.view s ∈ seen →           -- s is discovered
      (tovisit[(fp.view s)]? = none) →      -- s is not in the frontier
      ∀ l next_s, (l, .success next_s) ∈ sys.tr th s →   -- for all successors
      fp.view next_s ∈ seen                 -- successor must be discovered
  terminate_empty_tovisit :
    finished = some (.exploredAllReachableStates) → tovisit.isEmpty


structure LocalSearchContext {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
extends @BaseSearchContext ρ σ κ σₕ fp instBEq instHash th sys params
where
  tovisit : Std.HashMap σₕ (σ × Nat)
  localSeen : Std.HashSet σₕ
  localLog : Std.HashMap σₕ (σₕ × κ)
  seenUnaltered : ∀s, s ∈ baseCtx.seen ↔ s ∈ seen
  invs : @SearchContextInvariants ρ σ κ σₕ fp th sys params (fun ⟨h, x, d⟩ => tovisit[h]? = some (x, d))  (fun h => h ∈ seen ∨ h ∈ localSeen)
  /-- Local count of post-states generated (before deduplication) -/
  localStatesFound : Nat := 0
  /-- Local per-action statistics: label → stats -/
  localActionStatsMap : Std.HashMap κ ActionStat := {}
  excludeAllStatesFinish : finished ≠ some (.exploredAllReachableStates)
  deltaConsistent : (Function.Injective fp.view → ∀x, (fp.view x) ∈ localSeen → ∃d, tovisit[fp.view x]? = some (x, d))


/-- Merge action stats maps by summing counts for each action. -/
private def mergeActionStatsMaps [BEq κ] [Hashable κ] (m1 m2 : Std.HashMap κ ActionStat) : Std.HashMap κ ActionStat :=
  m2.fold (init := m1) fun acc label stat2 =>
    match acc[label]? with
    | some stat1 => acc.insert label { statesGenerated := stat1.statesGenerated + stat2.statesGenerated, distinctStates := stat1.distinctStates + stat2.distinctStates }
    | none => acc.insert label stat2

end Veil.ModelChecker.Concrete
