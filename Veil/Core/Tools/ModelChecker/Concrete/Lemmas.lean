import Veil.Core.Tools.ModelChecker.Concrete.Core
import Veil.Core.Tools.ModelChecker.Concrete.Subtypes

namespace Veil.ModelChecker.Concrete
open Std


structure SequentialSearchContext {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
extends @BaseSearchContext ρ σ κ σₕ fp instBEq instHash th sys params
where
  /- Queue storing (fingerprint, state, depth) tuples for BFS traversal -/
  sq    : fQueue (QueueItem σₕ σ)
  /- Inner invariants that hold at all times -/
  invs  : @SearchContextInvariants ρ σ κ σₕ fp th sys params (Membership.mem sq) (Membership.mem seen)
  /-- Outer invariant relating finished and pcState - only holds at bfsStep boundaries -/
  terminate_empty_queue : finished = some (.exploredAllReachableStates) → sq.isEmpty
  stable_closed :  Function.Injective fp.view →
    (finished = some (.exploredAllReachableStates) ∨ finished = none)
      → ∀ u : σ, (fp.view u) ∈ seen → (∀ d : Nat, ⟨fp.view u, u, d⟩ ∉ sq) →
      ∀l v, (l, ExecutionOutcome.success v) ∈ sys.tr th u → (fp.view v) ∈ seen


theorem SequentialSearchContext.bfs_completeness {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (ctx : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (h_starts : ∀ s, s ∈ sys.initStates → (fp.view s) ∈ ctx.seen)
  (h_explore_all : ctx.finished = some (.exploredAllReachableStates))
  (h_view_inj : Function.Injective fp.view) :
  ∀ s : σ, sys.reachable s → (fp.view s) ∈ ctx.seen := by
  intro s h_reachable
  induction h_reachable with
  | init s h_s_in_initStates =>
    exact h_starts s h_s_in_initStates
  | step u v h_u_reach h_transition ih =>
    obtain ⟨l, h_tr⟩ := h_transition
    have h_u_in_seen : fp.view u ∈ ctx.seen := ih
    have h_queue_empty : ctx.sq.isEmpty := ctx.terminate_empty_queue h_explore_all
    have h_u_not_in_queue : ∀ d : Nat, ⟨fp.view u, u, d⟩ ∉ ctx.sq := by
      intro d h_in
      have h_dequeue_none := fQueue.dequeue?_none_of_isEmpty ctx.sq h_queue_empty
      have h_spec := fQueue.dequeue?_spec ctx.sq
      rw [h_dequeue_none] at h_spec
      unfold Membership.mem fQueue.instMembership at h_in
      simp only [fQueue.toList] at h_in h_spec
      grind
    have h_finished_cond : ctx.finished = some (.exploredAllReachableStates) ∨ ctx.finished = none := by
      left; exact h_explore_all
    exact ctx.stable_closed h_view_inj h_finished_cond u h_u_in_seen h_u_not_in_queue l v h_tr


def SequentialSearchContext.initial {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ) :
  @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params := {
    BaseSearchContext.initial sys params with
    sq := fQueue.ofList (sys.initStates |> Functor.map (fun s => ⟨fp.view s, s, 0⟩)),
    invs := by
      constructor
      · -- queue_sound: all states in queue are reachable
        dsimp only [Functor.map]
        intro x d h_in_queue
        unfold Membership.mem at h_in_queue
        -- Convert queue membership to list membership
        have h_in_toList : (⟨fp.view x, x, d⟩ : QueueItem σₕ σ) ∈
            fQueue.toList (List.foldl fQueue.enqueue fQueue.empty
              (List.map (fun s => (⟨fp.view s, s, 0⟩ : QueueItem σₕ σ)) sys.initStates)) := by
          simp only [fQueue.toList, List.mem_append, List.mem_reverse]
          -- unfold fQueue.ofList at h_in_queue
          exact h_in_queue
        rw [fQueue.foldl_enqueue_toList] at h_in_toList
        simp only [fQueue.toList_empty, List.nil_append] at h_in_toList
        simp only [List.mem_map] at h_in_toList
        obtain ⟨s, h_s_in_init, h_eq⟩ := h_in_toList
        have h_state_eq : s = x := by
          have : (⟨fp.view s, s, 0⟩ : QueueItem σₕ σ).state =
                 (⟨fp.view x, x, d⟩ : QueueItem σₕ σ).state := by
            rw [h_eq]
          exact this
        rw [← h_state_eq]
        exact EnumerableTransitionSystem.reachable.init s h_s_in_init
      · -- visited_sound: all seen states are reachable
        intro h_view_inj x h_in_seen
        simp only [BaseSearchContext.initial] at h_in_seen
        have h_in_list : fp.view x ∈ sys.initStates.map fp.view := by
          exact Std.HashSet.mem_list_of_mem_insertMany h_in_seen
        simp only [List.mem_map] at h_in_list
        obtain ⟨s, h_s_in, h_eq_view⟩ := h_in_list
        have h_eq_st : s = x := h_view_inj h_eq_view
        rw [← h_eq_st]
        exact EnumerableTransitionSystem.reachable.init s h_s_in
      · -- queue_sub_visited: queue elements are in seen set
        intro x d h_in_queue
        dsimp only [Functor.map]
        simp only [BaseSearchContext.initial]
        unfold Membership.mem fQueue.instMembership at h_in_queue
        have h_in_toList : (⟨fp.view x, x, d⟩ : QueueItem σₕ σ) ∈
            fQueue.toList (List.foldl fQueue.enqueue fQueue.empty
              (List.map (fun s => (⟨fp.view s, s, 0⟩ : QueueItem σₕ σ)) sys.initStates)) := by
          simp only [fQueue.toList, List.mem_append, List.mem_reverse]
          exact h_in_queue
        rw [fQueue.foldl_enqueue_toList] at h_in_toList
        simp only [fQueue.toList_empty, List.nil_append] at h_in_toList
        simp only [List.mem_map] at h_in_toList
        obtain ⟨s, h_s_in_init, h_eq⟩ := h_in_toList
        have h_fp_eq : fp.view s = fp.view x := by
          have : (⟨fp.view s, s, 0⟩ : QueueItem σₕ σ).fingerprint =
                 (⟨fp.view x, x, d⟩ : QueueItem σₕ σ).fingerprint := by
            rw [h_eq]
          exact this
        rw [← h_fp_eq]
        apply Std.HashSet.mem_insertMany_of_mem_list
        show fp.view s ∈ List.map fp.view sys.initStates
        simp only [List.mem_map]
        exact ⟨s, h_s_in_init, rfl⟩
      · -- queue_wellformed: fingerprints match states
        dsimp only [Functor.map]
        intro fp' st d h_in_queue
        unfold Membership.mem fQueue.instMembership at h_in_queue
        have h_in_toList : (⟨fp', st, d⟩ : QueueItem σₕ σ) ∈
            fQueue.toList (List.foldl fQueue.enqueue fQueue.empty
              (List.map (fun s => (⟨fp.view s, s, 0⟩ : QueueItem σₕ σ)) sys.initStates)) := by
          simp only [fQueue.toList, List.mem_append, List.mem_reverse]
          exact h_in_queue
        rw [fQueue.foldl_enqueue_toList] at h_in_toList
        simp only [fQueue.toList_empty, List.nil_append] at h_in_toList
        simp only [List.mem_map] at h_in_toList
        obtain ⟨s, h_s_in_init, h_eq⟩ := h_in_toList
        have h_fp_eq : fp.view s = fp' := by
          have : (⟨fp.view s, s, 0⟩ : QueueItem σₕ σ).fingerprint =
                 (⟨fp', st, d⟩ : QueueItem σₕ σ).fingerprint := by
            rw [h_eq]
          exact this
        have h_st_eq : s = st := by
          have : (⟨fp.view s, s, 0⟩ : QueueItem σₕ σ).state =
                 (⟨fp', st, d⟩ : QueueItem σₕ σ).state := by
            rw [h_eq]
          exact this
        rw [← h_st_eq, ← h_fp_eq]
    terminate_empty_queue := by
      intro h_finished;
      contradiction
    stable_closed := by
      intro h_view_inj h_finished u h_in_seen h_not_in_queue l v h_tr
      unfold BaseSearchContext.initial at h_in_seen
      have h_in_list := Std.HashSet.mem_list_of_mem_insertMany h_in_seen
      simp only [Functor.map, List.mem_map] at h_in_list
      obtain ⟨s, h_s_in_init, h_view_eq⟩ := h_in_list
      have h_eq : s = u := h_view_inj h_view_eq
      subst h_eq
      exfalso
      apply h_not_in_queue 0
      apply fQueue.mem_ofList
      simp only [Functor.map, List.mem_map]
      exact ⟨s, h_s_in_init, rfl⟩
  }


-- High-level theorem: enqueue operation preserves invariants when fingerprint is in seen
theorem SequentialSearchContext.enqueue_preserves_invs {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [instBEq: BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (ctx : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (fingerprint : σₕ)
  (succ : σ)
  (depth : Nat)
  (h_neighbor : sys.reachable succ)
  (h_fp : fingerprint = fp.view succ)
  (h_seen : ctx.seen.contains fingerprint) :
  @SearchContextInvariants ρ σ κ σₕ fp th sys params
    (Membership.mem (ctx.sq.enqueue ⟨fingerprint, succ, depth + 1⟩))
    (Membership.mem ctx.seen) := by
  constructor
  · -- queue_sound: states in the enqueued queue are reachable
    intro x d h_in_queue
    unfold Membership.mem fQueue.instMembership fQueue.enqueue at h_in_queue
    -- h_in_queue: x in new queue's front or back
    rcases h_in_queue with h_in_front | h_in_back
    · -- x is in front (unchanged from original queue)
      have h_in_old : ⟨fp.view x, x, d⟩ ∈ ctx.sq := by
        unfold Membership.mem fQueue.instMembership
        left
        exact h_in_front
      exact ctx.invs.queue_sound x d h_in_old
    · -- x is in back (which now includes the new element)
      -- back is (succ :: ctx.sq.back), so x is either succ or in old back
      simp only [List.mem_cons] at h_in_back
      rcases h_in_back with h_is_new | h_in_old_back
      · -- x is the newly enqueued element (succ)
        have h_eq : (⟨fp.view x, x, d⟩ : QueueItem σₕ σ) = ⟨fingerprint, succ, depth + 1⟩ := h_is_new
        have h_x_eq : x = succ := by
          have : (⟨fp.view x, x, d⟩ : QueueItem σₕ σ).state =
                 (⟨fingerprint, succ, depth + 1⟩ : QueueItem σₕ σ).state := by rw [h_eq]
          simp only at this
          exact this
        rw [h_x_eq]
        exact h_neighbor
      · -- x is in the old back
        have h_in_old : ⟨fp.view x, x, d⟩ ∈ ctx.sq := by
          unfold Membership.mem fQueue.instMembership
          right
          exact h_in_old_back
        exact ctx.invs.queue_sound x d h_in_old
  · -- visited_sound: seen set unchanged
    intro h_view_inj x h_in_seen_mem
    exact ctx.invs.visited_sound h_view_inj x h_in_seen_mem
  · -- queue_sub_visited: elements in enqueued queue have fingerprints in seen
    intro x d h_in_queue
    unfold Membership.mem fQueue.instMembership fQueue.enqueue at h_in_queue
    rcases h_in_queue with h_in_front | h_in_back
    · -- x is in front
      have h_in_old : ⟨fp.view x, x, d⟩ ∈ ctx.sq := by
        unfold Membership.mem fQueue.instMembership
        left;exact h_in_front
      exact ctx.invs.queue_sub_visited x d h_in_old
    · -- x is in back
      simp only [List.mem_cons] at h_in_back
      rcases h_in_back with h_is_new | h_in_old_back
      · -- x is the newly enqueued element
        have h_eq : (⟨fp.view x, x, d⟩ : QueueItem σₕ σ) = ⟨fingerprint, succ, depth + 1⟩ := h_is_new
        have h_fp_eq : fp.view x = fingerprint := by
          have : (⟨fp.view x, x, d⟩ : QueueItem σₕ σ).fingerprint =
                 (⟨fingerprint, succ, depth + 1⟩ : QueueItem σₕ σ).fingerprint := by rw [h_eq]
          simpa using this
        rw [h_fp_eq]
        exact h_seen
      · -- x is in old back
        have h_in_old : ⟨fp.view x, x, d⟩ ∈ ctx.sq := by
          unfold Membership.mem fQueue.instMembership
          right; exact h_in_old_back
        exact ctx.invs.queue_sub_visited x d h_in_old
  · -- queue_wellformed: fingerprints match states in enqueued queue
    intro fp' st d h_in_queue
    unfold Membership.mem fQueue.instMembership fQueue.enqueue at h_in_queue
    rcases h_in_queue with h_in_front | h_in_back
    · -- in front
      have h_in_old : ⟨fp', st, d⟩ ∈ ctx.sq := by
        unfold Membership.mem fQueue.instMembership
        left; exact h_in_front
      exact ctx.invs.queue_wellformed fp' st d h_in_old
    · -- in back
      simp only [List.mem_cons] at h_in_back
      rcases h_in_back with h_is_new | h_in_old_back
      · have h_eq : (⟨fp', st, d⟩ : QueueItem σₕ σ) = ⟨fingerprint, succ, depth + 1⟩ := h_is_new
        have h_fp_eq : fp' = fingerprint := by
          have : (⟨fp', st, d⟩ : QueueItem σₕ σ).fingerprint =
                 (⟨fingerprint, succ, depth + 1⟩ : QueueItem σₕ σ).fingerprint := by rw [h_eq]
          simp only at this
          exact this
        have h_st_eq : st = succ := by
          have : (⟨fp', st, d⟩ : QueueItem σₕ σ).state =
                 (⟨fingerprint, succ, depth + 1⟩ : QueueItem σₕ σ).state := by rw [h_eq]
          simp only at this
          exact this
        rw [h_st_eq, h_fp_eq, h_fp]
      · have h_in_old : ⟨fp', st, d⟩ ∈ ctx.sq := by
          unfold Membership.mem fQueue.instMembership
          right
          exact h_in_old_back
        exact ctx.invs.queue_wellformed fp' st d h_in_old



-- High-level theorem: inserting a new state into seen preserves invariants (queue unchanged)
theorem SequentialSearchContext.insert_seen_preserves_invs {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [instBEq: BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (ctx : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (fingerprint : σₕ)
  (succ : σ)
  (h_neighbor : sys.reachable succ)
  (h_fp : fingerprint = fp.view succ) :
  @SearchContextInvariants ρ σ κ σₕ fp th sys params
    (Membership.mem ctx.sq)
    (Membership.mem (ctx.seen.insert fingerprint)) := by
  constructor
  · -- queue_sound: queue unchanged, so invariant preserved
    intro x d h_in_queue
    exact ctx.invs.queue_sound x d h_in_queue
  · -- visited_sound: new seen element is the reachable neighbor
    intro h_view_inj x h_in_seen
    rw [Membership.mem] at h_in_seen
    by_cases h : fp.view x = fingerprint
    · -- x's fingerprint equals the new fingerprint, so x = succ
      have h_x_eq_succ : x = succ := by
        rw [h_fp] at h
        exact h_view_inj h
      rw [h_x_eq_succ]; exact h_neighbor
    · -- x's fingerprint is different, so it must have been in the old seen set
      have h_in_old : ctx.seen.contains (fp.view x) := by grind
      exact ctx.invs.visited_sound h_view_inj x h_in_old
  · -- queue_sub_visited: queue unchanged, but seen expanded
    intro x d h_in_queue
    have h_old := ctx.invs.queue_sub_visited x d h_in_queue
    rw [Membership.mem]
    grind
  · -- queue_wellformed: queue unchanged
    intro fp' st d h_in_queue
    exact ctx.invs.queue_wellformed fp' st d h_in_queue



-- High-level theorem: dequeue operation preserves invariants
theorem SequentialSearchContext.dequeue_preserves_invs {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [instBEq: BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (ctx : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (item : QueueItem σₕ σ)
  (q_tail : fQueue (QueueItem σₕ σ))
  (h_dequeue : ctx.sq.dequeue? = some (item, q_tail)) :
  @SearchContextInvariants ρ σ κ σₕ fp th sys params
    (Membership.mem q_tail)
    (Membership.mem ctx.seen) := by
  have spec := fQueue.dequeue?_spec ctx.sq
  rw [h_dequeue] at spec
  simp only at spec
  -- spec: ctx.sq.toList = item :: q_tail.toList
  constructor
  · -- queue_sound: All states in the tail are still reachable
    intro x d h_in_tail
    have h_in_original : ⟨fp.view x, x, d⟩ ∈ ctx.sq := by
      -- Convert tail membership to list membership
      unfold Membership.mem fQueue.instMembership at h_in_tail
      have h_in_tail_list : ⟨fp.view x, x, d⟩ ∈ fQueue.toList q_tail := by
        simp only [fQueue.toList, List.mem_append, List.mem_reverse]
        exact h_in_tail
      -- Use spec to show it's in original queue
      have h_in_ctx_list : ⟨fp.view x, x, d⟩ ∈ fQueue.toList ctx.sq := by
        rw [spec]
        simp only [List.mem_cons]
        right
        exact h_in_tail_list
      -- Convert back to queue membership
      unfold Membership.mem fQueue.instMembership
      simp only [fQueue.toList, List.mem_append, List.mem_reverse] at h_in_ctx_list
      exact h_in_ctx_list
    exact ctx.invs.queue_sound x d h_in_original
  · -- visited_sound: seen set unchanged
    intro h_view_inj x h_in_seen
    exact ctx.invs.visited_sound h_view_inj x h_in_seen
  · -- queue_sub_visited: Elements in tail were already in seen
    intro x d h_in_tail
    have h_in_original : ⟨fp.view x, x, d⟩ ∈ ctx.sq := by
      unfold Membership.mem fQueue.instMembership at h_in_tail
      have h_in_tail_list : ⟨fp.view x, x, d⟩ ∈ fQueue.toList q_tail := by
        simp only [fQueue.toList, List.mem_append, List.mem_reverse]
        exact h_in_tail
      have h_in_ctx_list : ⟨fp.view x, x, d⟩ ∈ fQueue.toList ctx.sq := by
        rw [spec]
        simp only [List.mem_cons]
        right
        exact h_in_tail_list
      unfold Membership.mem fQueue.instMembership
      simp only [fQueue.toList, List.mem_append, List.mem_reverse] at h_in_ctx_list
      exact h_in_ctx_list
    exact ctx.invs.queue_sub_visited x d h_in_original
  · -- queue_wellformed: Fingerprints still match states in tail
    intro fp' st d h_in_tail
    have h_in_original : ⟨fp', st, d⟩ ∈ ctx.sq := by
      unfold Membership.mem fQueue.instMembership at h_in_tail
      have h_in_tail_list : ⟨fp', st, d⟩ ∈ fQueue.toList q_tail := by
        simp only [fQueue.toList, List.mem_append, List.mem_reverse]
        exact h_in_tail
      have h_in_ctx_list : ⟨fp', st, d⟩ ∈ fQueue.toList ctx.sq := by
        rw [spec]
        simp only [List.mem_cons]
        right
        exact h_in_tail_list
      unfold Membership.mem fQueue.instMembership
      simp only [fQueue.toList, List.mem_append, List.mem_reverse] at h_in_ctx_list
      exact h_in_ctx_list
    exact ctx.invs.queue_wellformed fp' st d h_in_original



/-- Theorem: Inserting a new fingerprint into seen and enqueuing the corresponding state preserves invariants.
    This theorem is used in tryExploreNeighbor when adding a newly discovered neighbor. -/
theorem SequentialSearchContext.insert_and_enqueue_preserves_invs {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [instBEq: BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (ctx : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (fingerprint : σₕ)
  (succ : σ)
  (depth : Nat)
  (h_neighbor : sys.reachable succ)
  (h_fp : fingerprint = fp.view succ) :
  @SearchContextInvariants ρ σ κ σₕ fp th sys params
    (Membership.mem (ctx.sq.enqueue ⟨fingerprint, succ, depth + 1⟩))
    (Membership.mem (ctx.seen.insert fingerprint)) := by
  constructor
  · -- queue_sound: states in the enqueued queue are reachable
    intro x d h_in_queue
    unfold Membership.mem fQueue.instMembership fQueue.enqueue at h_in_queue
    rcases h_in_queue with h_in_front | h_in_back
    · -- x is in front (unchanged from original queue)
      have h_in_old : ⟨fp.view x, x, d⟩ ∈ ctx.sq := by
        unfold Membership.mem fQueue.instMembership
        left
        exact h_in_front
      exact ctx.invs.queue_sound x d h_in_old
    · -- x is in back
      simp only [List.mem_cons] at h_in_back
      rcases h_in_back with h_is_new | h_in_old_back
      · -- x is the newly enqueued element (succ)
        have h_eq : (⟨fp.view x, x, d⟩ : QueueItem σₕ σ) = ⟨fingerprint, succ, depth + 1⟩ := h_is_new
        have h_x_eq : x = succ := by
          have : (⟨fp.view x, x, d⟩ : QueueItem σₕ σ).state =
                 (⟨fingerprint, succ, depth + 1⟩ : QueueItem σₕ σ).state := by rw [h_eq]
          simp only at this
          exact this
        rw [h_x_eq]
        exact h_neighbor
      · -- x is in the old back
        have h_in_old : ⟨fp.view x, x, d⟩ ∈ ctx.sq := by
          unfold Membership.mem fQueue.instMembership
          right
          exact h_in_old_back
        exact ctx.invs.queue_sound x d h_in_old
  · -- visited_sound: elements in new seen are reachable
    intro h_view_inj x h_in_new_seen
    rw [Membership.mem] at h_in_new_seen
    by_cases h : fp.view x = fingerprint
    · -- x's fingerprint equals the new fingerprint, so x = succ
      have h_x_eq_succ : x = succ := by
        rw [h_fp] at h
        exact h_view_inj h
      rw [h_x_eq_succ]; exact h_neighbor
    · -- x's fingerprint is different, so it must have been in the old seen set
      have h_in_old : ctx.seen.contains (fp.view x) := by grind
      exact ctx.invs.visited_sound h_view_inj x h_in_old
  · -- queue_sub_visited: elements in enqueued queue have fingerprints in new seen
    intro x d h_in_queue
    unfold Membership.mem fQueue.instMembership fQueue.enqueue at h_in_queue
    rcases h_in_queue with h_in_front | h_in_back
    · -- x is in front
      have h_in_old : ⟨fp.view x, x, d⟩ ∈ ctx.sq := by
        unfold Membership.mem fQueue.instMembership
        left
        exact h_in_front
      have h_in_old_seen := ctx.invs.queue_sub_visited x d h_in_old
      rw [Membership.mem]
      grind
    · -- x is in back
      simp only [List.mem_cons] at h_in_back
      rcases h_in_back with h_is_new | h_in_old_back
      · -- x is the newly enqueued element
        have h_eq : (⟨fp.view x, x, d⟩ : QueueItem σₕ σ) = ⟨fingerprint, succ, depth + 1⟩ := h_is_new
        have h_fp_eq : fp.view x = fingerprint := by
          have : (⟨fp.view x, x, d⟩ : QueueItem σₕ σ).fingerprint =
                 (⟨fingerprint, succ, depth + 1⟩ : QueueItem σₕ σ).fingerprint := by rw [h_eq]
          simp only at this
          exact this
        rw [Membership.mem, h_fp_eq]
        grind
      · -- x is in old back
        have h_in_old : ⟨fp.view x, x, d⟩ ∈ ctx.sq := by
          unfold Membership.mem fQueue.instMembership
          right
          exact h_in_old_back
        have h_in_old_seen := ctx.invs.queue_sub_visited x d h_in_old
        rw [Membership.mem]
        grind
  · -- queue_wellformed: fingerprints match states in enqueued queue
    intro fp' st d h_in_queue
    unfold Membership.mem fQueue.instMembership fQueue.enqueue at h_in_queue
    rcases h_in_queue with h_in_front | h_in_back
    · -- in front
      have h_in_old : ⟨fp', st, d⟩ ∈ ctx.sq := by
        unfold Membership.mem fQueue.instMembership
        left
        exact h_in_front
      exact ctx.invs.queue_wellformed fp' st d h_in_old
    · -- in back
      simp only [List.mem_cons] at h_in_back
      rcases h_in_back with h_is_new | h_in_old_back
      · -- newly enqueued element
        have h_eq : (⟨fp', st, d⟩ : QueueItem σₕ σ) = ⟨fingerprint, succ, depth + 1⟩ := h_is_new
        have h_fp_eq : fp' = fingerprint := by
          have : (⟨fp', st, d⟩ : QueueItem σₕ σ).fingerprint =
                 (⟨fingerprint, succ, depth + 1⟩ : QueueItem σₕ σ).fingerprint := by rw [h_eq]
          simp only at this
          exact this
        have h_st_eq : st = succ := by
          have : (⟨fp', st, d⟩ : QueueItem σₕ σ).state =
                 (⟨fingerprint, succ, depth + 1⟩ : QueueItem σₕ σ).state := by rw [h_eq]
          simp only at this
          exact this
        rw [h_st_eq, h_fp_eq, h_fp]
      · -- in old back
        have h_in_old : ⟨fp', st, d⟩ ∈ ctx.sq := by
          unfold Membership.mem fQueue.instMembership
          right
          exact h_in_old_back
        exact ctx.invs.queue_wellformed fp' st d h_in_old



/-- Theorem: Adding a reachable neighbor (not in seen) to both seen and queue preserves stable_closed.
    This combines insert_seen and enqueue operations.
    Key insight: The new element is added to the queue, so it doesn't violate stable_closed
    (which only applies to states not in queue). -/
theorem SequentialSearchContext.insert_and_enqueue_preserves_stable_closed {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [instBEq: BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (ctx : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (fingerprint : σₕ)
  (succ : σ)
  (depth : Nat)
  (h_neighbor : sys.reachable succ)
  (h_fp : fingerprint = fp.view succ):
  Function.Injective fp.view →
  (ctx.finished = some (.exploredAllReachableStates) ∨ ctx.finished = none) →
  ∀ u : σ, (fp.view u) ∈ (ctx.seen.insert fingerprint) → (∀ d : Nat, ⟨fp.view u, u, d⟩ ∉ (ctx.sq.enqueue ⟨fingerprint, succ, depth + 1⟩)) →
  ∀ l v, (l, ExecutionOutcome.success v) ∈ sys.tr th u → (fp.view v) ∈ (ctx.seen.insert fingerprint) := by
  intro h_view_inj h_finished u h_in_seen h_not_in_queue l v h_tr
  -- Case split: is u the newly added element (succ)?
  by_cases h_u_is_new : fp.view u = fingerprint
  · -- Case 1: u is the newly added element
    -- We need to show that v (successor of u=succ) is in the new seen set
    have h_u_eq_succ : u = succ := by
      rw [h_fp] at h_u_is_new
      exact h_view_inj h_u_is_new
    -- Since u = succ is reachable and (l, v) is a successor of u,
    -- v is also reachable
    rw [h_u_eq_succ] at h_tr
    have h_v_reachable : sys.reachable v :=
      EnumerableTransitionSystem.reachable.step succ v h_neighbor ⟨l, h_tr⟩
    exfalso
    -- u = succ and succ is in the new queue at depth+1
    have h_succ_in_new_queue : ⟨fp.view succ, succ, depth + 1⟩ ∈ ctx.sq.enqueue ⟨fp.view succ, succ, depth + 1⟩ := by
      unfold Membership.mem fQueue.instMembership fQueue.enqueue
      right
      simp
    have h_u_in_new_queue_fp : ⟨fp.view u, u, depth + 1⟩ ∈ ctx.sq.enqueue ⟨fingerprint, succ, depth + 1⟩ := by
      rw [h_u_eq_succ, h_fp]
      exact h_succ_in_new_queue
    grind
  · -- Case 2: u is not the newly added element, so u was in the old seen set
    have h_u_in_old_seen : (fp.view u) ∈ ctx.seen := by
      grind
    -- Since u is in old seen and not in new queue, u is also not in old queue
    have h_not_in_old_queue : ∀ d : Nat, ⟨fp.view u, u, d⟩ ∉ ctx.sq := by
      intro d h_in_old
      apply h_not_in_queue d
      -- If u is in old queue, it's also in new queue (we only added one element)
      unfold Membership.mem fQueue.instMembership at h_in_old ⊢
      unfold fQueue.enqueue
      rcases h_in_old with h_front | h_back
      · left; exact h_front
      · right; simp; right; exact h_back
    -- Apply stable_closed from the original context
    have h_v_in_old_seen : (fp.view v) ∈ ctx.seen :=
      ctx.stable_closed h_view_inj h_finished u h_u_in_old_seen h_not_in_old_queue l v h_tr
    -- v is in old seen, so it's also in new seen
    grind


-- High-level theorem: updating toBaseSearchContext after processState preserves invariants
-- This theorem says: when we extract ctx.toBaseSearchContext, apply processState to get baseCtx',
-- and put baseCtx' back into SequentialSearchContext, the invariants still hold
theorem SequentialSearchContext.update_base_after_processState_preserves_invs {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ] [BEq σ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  (ctx : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (fpSt : σₕ)
  (curr : σ)
  (baseCtx' : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (h_process : (ctx.toBaseSearchContext.processState sys fpSt curr).1 = baseCtx') :
  @SearchContextInvariants ρ σ κ σₕ fp th sys params
    (Membership.mem ctx.sq)
    (Membership.mem baseCtx'.seen) := by
  -- Note: ctx.seen and ctx.toBaseSearchContext.seen are definitionally equal
  -- because SequentialSearchContext extends BaseSearchContext
  -- Derive h_seen_unchanged from h_process
  have h_seen_unchanged : baseCtx'.seen = ctx.seen := by
    have h_preserves := BaseSearchContext.processState_preserves_seen sys params fpSt curr ctx.toBaseSearchContext
    rw [h_process] at h_preserves
    exact h_preserves
  constructor
  · intro x d h_in_queue; exact ctx.invs.queue_sound x d h_in_queue
  · intro h_view_inj x h_in_seen; rw [h_seen_unchanged] at h_in_seen
    exact ctx.invs.visited_sound h_view_inj x h_in_seen
  · intro x d h_in_queue; rw [h_seen_unchanged]; exact ctx.invs.queue_sub_visited x d h_in_queue
  · intro fp' st d h_in_queue; exact ctx.invs.queue_wellformed fp' st d h_in_queue



/-- Theorem: When context is not finished and finished status is unchanged after operations,
    dequeuing preserves terminate_empty_queue.
    Key insight: If finished was none and remains unchanged, it cannot become exploredAllReachableStates.
    Since the premise is impossible, the conclusion (queue isEmpty) is vacuously true. -/
theorem SequentialSearchContext.dequeue_preserves_terminate_empty_queue {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  (ctx : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (new_sq : fQueue (QueueItem σₕ σ))
  (h_non_finished : !ctx.hasFinished)
  (new_finished : Option (TerminationReason σₕ))
  (h_finished_unchanged : new_finished = ctx.finished) :
  new_finished = some (TerminationReason.exploredAllReachableStates) → new_sq.isEmpty := by
  intro h_finished'
  have h_ctx_not_finished : ctx.finished = none := by
    unfold BaseSearchContext.hasFinished at h_non_finished
    simp at h_non_finished
    exact h_non_finished
  rw [h_finished_unchanged] at h_finished'
  rw [h_ctx_not_finished] at h_finished'
  simp at h_finished'


-- High-level theorem: dequeue with all successors in seen preserves stable_closed
-- Key insight: When we dequeue curr, it becomes a state "not in queue".
-- If all successors of curr are already in seen, then stable_closed remains satisfied.
theorem SequentialSearchContext.dequeue_with_successors_in_seen_preserves_stable_closed {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ] [BEq σ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  (ctx : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (curr : σ)
  (fpCurr : σₕ)
  (depth : Nat)
  (new_sq : fQueue (QueueItem σₕ σ))
  (h_dequeue : ctx.sq.dequeue? = some (⟨fpCurr, curr, depth⟩, new_sq))
  (h_all_successors_in_seen : ∀ l v, (l, ExecutionOutcome.success v) ∈ sys.tr th curr → (fp.view v) ∈ ctx.seen):
  Function.Injective fp.view →
  (ctx.finished = some (.exploredAllReachableStates) ∨ ctx.finished = none) →
  ∀ u : σ, (fp.view u) ∈ ctx.seen → (∀ d : Nat, ⟨fp.view u, u, d⟩ ∉ new_sq) →
  ∀ l v, (l, ExecutionOutcome.success v) ∈ sys.tr th u → (fp.view v) ∈ ctx.seen := by
  intro h_view_inj h_finished u h_in_seen h_not_in_new_queue l v h_tr
  -- Case split: is u the dequeued element curr?
  by_cases h_u_is_curr : fp.view u = fpCurr
  · -- Case 1: u is curr (the dequeued element)
    -- We need to prove curr = u first
    have h_curr_wellformed : fpCurr = fp.view curr := by
      have h_in_old_queue : ⟨fpCurr, curr, depth⟩ ∈ ctx.sq := by
        unfold Membership.mem fQueue.instMembership
        have spec := fQueue.dequeue?_spec ctx.sq
        rw [h_dequeue] at spec
        simp only [fQueue.toList] at spec; simp
        -- Convert from disjunction to append membership
        cases h_front : ctx.sq.front with
        | nil =>
          rw [h_front] at spec
          simp only [List.nil_append] at spec
          simp_all
        | cons hd tl =>
          rw [h_front] at spec
          simp only [List.cons_append, List.cons.injEq] at spec
          obtain ⟨rfl, _⟩ := spec
          grind
      exact ctx.invs.queue_wellformed fpCurr curr depth h_in_old_queue
    have h_u_eq_curr : u = curr := by
      have : fp.view u = fp.view curr := by rw [h_u_is_curr, h_curr_wellformed]
      exact h_view_inj this
    rw [h_u_eq_curr] at h_tr
    exact h_all_successors_in_seen l v h_tr
  · -- Case 2: u is not curr, so u is still not in queue (or wasn't in the old queue either)
    have h_not_in_old_queue : ∀ d : Nat, ⟨fp.view u, u, d⟩ ∉ ctx.sq := by
      intro d h_in_old
      unfold Membership.mem fQueue.instMembership at h_in_old
      have spec := fQueue.dequeue?_spec ctx.sq
      rw [h_dequeue] at spec
      simp only [fQueue.toList] at spec
      simp at h_in_old
      rcases h_in_old with h_front | h_back
      · -- u is in front of old queue
        apply h_not_in_new_queue d
        -- Convert from old queue membership to toList
        have h_in_toList : (⟨fp.view u, u, d⟩ : QueueItem σₕ σ) ∈ fQueue.toList ctx.sq := by
          simp only [fQueue.toList, List.mem_append, List.mem_reverse]
          left
          exact h_front
        -- Expand toList and use spec
        simp only [fQueue.toList] at h_in_toList
        rw [spec] at h_in_toList
        simp only [List.mem_cons] at h_in_toList
        rcases h_in_toList with h_eq | h_in_tail
        · -- u is the dequeued element, but we know fp.view u ≠ fpCurr
          have h_fp_u_eq : fp.view u = fpCurr := by
            have : (⟨fp.view u, u, d⟩ : QueueItem σₕ σ).fingerprint =
                   (⟨fpCurr, curr, depth⟩ : QueueItem σₕ σ).fingerprint := by rw [h_eq]
            simp only at this
            exact this
          contradiction
        · -- u is in the tail (new_sq)
          unfold Membership.mem fQueue.instMembership
          simp only [List.mem_append, List.mem_reverse] at h_in_tail
          exact h_in_tail
      · -- u is in back of old queue
        apply h_not_in_new_queue d
        have h_in_toList : (⟨fp.view u, u, d⟩ : QueueItem σₕ σ) ∈ fQueue.toList ctx.sq := by
          simp only [fQueue.toList, List.mem_append, List.mem_reverse]
          right
          exact h_back
        simp only [fQueue.toList] at h_in_toList
        rw [spec] at h_in_toList
        simp only [List.mem_cons] at h_in_toList
        rcases h_in_toList with h_eq | h_in_tail
        · -- u is the dequeued element, contradiction
          have h_fp_u_eq : fp.view u = fpCurr := by
            have : (⟨fp.view u, u, d⟩ : QueueItem σₕ σ).fingerprint =
                   (⟨fpCurr, curr, depth⟩ : QueueItem σₕ σ).fingerprint := by rw [h_eq]
            simp only at this
            exact this
          contradiction
        · -- u is in the tail (new_sq)
          unfold Membership.mem fQueue.instMembership
          simp only [List.mem_append, List.mem_reverse] at h_in_tail
          exact h_in_tail
    exact ctx.stable_closed h_view_inj h_finished u h_in_seen h_not_in_old_queue l v h_tr
