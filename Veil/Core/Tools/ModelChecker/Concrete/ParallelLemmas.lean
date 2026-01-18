import Veil.Core.Tools.ModelChecker.Concrete.Core
import Veil.Core.Tools.ModelChecker.Concrete.Subtypes
import Std.Data.HashMap.Lemmas


namespace Veil.ModelChecker.Concrete
open Std

structure ParallelSearchContextMain {ρ σ κ σₕ : Type}
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


structure ParallelSearchContextSub {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
extends @BaseSearchContext ρ σ κ σₕ fp instBEq instHash th sys params
where
  tovisit : Array (QueueItem σₕ σ)
  localSeen : Std.HashSet σₕ
  localLog : Std.HashMap σₕ (σₕ × κ)
  invs  : @SearchContextInvariants ρ σ κ σₕ fp th sys params (Membership.mem tovisit) (fun h => h ∈ seen ∨ h ∈ localSeen)
  /-- Local count of post-states generated (before deduplication) -/
  localStatesFound : Nat := 0
  /-- Local per-action statistics: label → stats -/
  localActionStatsMap : Std.HashMap κ ActionStat := {}
  /-- The seen set and localSeen are disjoint: newly discovered states go to localSeen -/
  seenDisjoint : ∀ h, h ∈ seen → ¬(h ∈ localSeen)
  initSubSeen : ∀s₀, s₀ ∈ sys.initStates → (fp.view s₀) ∈ seen
  deltaConsistent : (Function.Injective fp.view → ∀x, (fp.view x) ∈ localSeen → ∃d, ⟨(fp.view x), x, d⟩ ∈ tovisit)


/- `Pure data object`, used for batch-merge operation.
We can make it to carry properties ...  -/
structure ParallelSearchContextMerge {ρ σ κ σₕ : Type}
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
  -- invs  : @SearchContextInvariants ρ σ κ σₕ fp th sys params (Membership.mem tovisit) (fun h => h ∈ seen ∨ h ∈ localSeen)
  invs : @SearchContextInvariants ρ σ κ σₕ fp th sys params (fun ⟨h, x, d⟩ => tovisit[h]? = some (x, d))  (fun h => h ∈ seen ∨ h ∈ localSeen)
  -- /-- Local count of post-states generated (before deduplication) -/
  localStatesFound : Nat := 0
  -- /-- Local per-action statistics: label → stats -/
  localActionStatsMap : Std.HashMap κ ActionStat := {}
  -- /-- The seen set and localSeen are disjoint: newly discovered states go to localSeen -/
  -- seenDisjoint : ∀ h, h ∈ seen → ¬(h ∈ localSeen)
  -- initSubSeen : ∀s₀, s₀ ∈ sys.initStates → (fp.view s₀) ∈ seen
  excludeAllStatesFinish : finished ≠ some (.exploredAllReachableStates)
  deltaConsistent : (Function.Injective fp.view → ∀x, (fp.view x) ∈ localSeen → ∃d, tovisit[fp.view x]? = some (x, d))


theorem concurrent_bfs_completeness {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (ctx : @ParallelSearchContextMain ρ σ κ σₕ fp _ _ th sys params)
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
    have h_tovisit_empty : ctx.tovisit.isEmpty := ctx.terminate_empty_tovisit h_explore_all
    have h_u_not_in_tovisit : ctx.tovisit[(fp.view u)]? = none := by
      cases h_get : ctx.tovisit[(fp.view u)]? with
      | none => rfl
      | some val =>
        have h_not_empty : ¬ctx.tovisit.isEmpty := by
          intro h_empty
          simp only [Std.HashMap.isEmpty_iff_forall_not_mem] at h_empty
          have h_mem : (fp.view u) ∈ ctx.tovisit := by grind
          exact h_empty (fp.view u) h_mem
        exact absurd h_tovisit_empty h_not_empty
    have h_finished_cond : ctx.finished = some (.exploredAllReachableStates) ∨ ctx.finished = none := by
      left; exact h_explore_all
    exact ctx.frontier_closed h_view_inj h_finished_cond u h_u_in_seen h_u_not_in_tovisit l v h_tr



/-- Helper lemma: single insertIfNew step preserves reachability -/
@[grind .]
theorem insertIfNew_preserves_reachability
  {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (acc : Std.HashMap σₕ (σ × Nat))
  (h_acc : ∀ x d, acc[fp.view x]? = some (x, d) → sys.reachable x)
  (item : QueueItem σₕ σ)
  (h_item : sys.reachable item.state)
  : ∀ x d, (acc.insertIfNew item.fingerprint (item.state, item.depth))[fp.view x]? = some (x, d) → sys.reachable x := by
  intro x d h_lookup
  by_cases h_contains : acc.contains item.fingerprint
  · have h_lookup_eq : (acc.insertIfNew item.fingerprint (item.state, item.depth))[fp.view x]? = acc[fp.view x]? := by
      rw [Std.HashMap.getElem?_insertIfNew]
      simp only [Std.HashMap.contains] at h_contains
      split
      · next h_cond =>
        have ⟨_, h_not_mem⟩ := h_cond
        have : item.fingerprint ∈ acc := by simp only [Membership.mem]; exact h_contains
        contradiction
      · rfl
    rw [h_lookup_eq] at h_lookup
    exact h_acc x d h_lookup
  · rw [Std.HashMap.getElem?_insertIfNew] at h_lookup
    simp only [Std.HashMap.contains] at h_contains
    have h_not_mem : ¬item.fingerprint ∈ acc := by simp only [Membership.mem]; exact h_contains
    split at h_lookup
    · next h_cond =>
      have ⟨h_eq, _⟩ := h_cond
      cases h_lookup
      exact h_item
    · exact h_acc x d h_lookup



/- Helper lemma: if a key maps to a value in the result of foldl insertIfNew,
    then either it was in init or it came from the array.
    This requires induction on the array structure.
    We require that the array is wellformed (fingerprints match states). -/
theorem getElem?_foldl_insertIfNew {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  (arr : Array (QueueItem σₕ σ))
  (init : Std.HashMap σₕ (σ × Nat))
  (k : σₕ)
  (v : σ × Nat)
  (h_arr_wellformed : ∀ fingerprint st d, ⟨fingerprint, st, d⟩ ∈ arr → fingerprint = fp.view st) :
  (arr.foldl (init := init) fun acc ⟨h, x, d⟩ => acc.insertIfNew h (x, d))[k]? = some v →
  init[k]? = some v ∨ ∃ x d, ⟨k, x, d⟩ ∈ arr ∧ k = fp.view x ∧ v = (x, d) := by
  intro h_lookup
  -- Convert Array.foldl to List.foldl and prove by induction on the list
  have h_lookup' : (arr.toList.foldl (fun acc ⟨h, x, d⟩ => acc.insertIfNew h (x, d)) init)[k]? = some v := by grind
  -- Prove by induction on the list representation
  suffices ∀ (l : List (QueueItem σₕ σ)) (acc : Std.HashMap σₕ (σ × Nat)),
    (∀ fingerprint st d, ⟨fingerprint, st, d⟩ ∈ l → fingerprint = fp.view st) →
    (l.foldl (fun acc ⟨h, x, d⟩ => acc.insertIfNew h (x, d)) acc)[k]? = some v →
    acc[k]? = some v ∨ ∃ x d, ⟨k, x, d⟩ ∈ l ∧ k = fp.view x ∧ v = (x, d) by
    have h_list_wellformed : ∀ fingerprint st d, ⟨fingerprint, st, d⟩ ∈ arr.toList → fingerprint = fp.view st := by
      intro fingerprint st d h_mem
      exact h_arr_wellformed fingerprint st d (Array.mem_toList_iff.mp h_mem)
    cases this arr.toList init h_list_wellformed h_lookup' with
    | inl h => left; exact h
    | inr h => obtain ⟨x, d, h_mem, h_fp, h_val⟩ := h; right; refine ⟨x, d, ?_, h_fp, h_val⟩; grind
  intro l
  induction l with
  | nil =>
    intro acc h_wellformed h_lookup
    simp at h_lookup
    left
    exact h_lookup
  | cons head tail ih =>
    intro acc h_wellformed h_lookup
    simp only [List.foldl] at h_lookup
    -- After processing head, we continue with tail
    have h_tail_wellformed : ∀ fingerprint st d, ⟨fingerprint, st, d⟩ ∈ tail → fingerprint = fp.view st := by
      intro fingerprint st d h_mem
      exact h_wellformed fingerprint st d (List.Mem.tail head h_mem)
    have h_tail := ih (acc.insertIfNew head.fingerprint (head.state, head.depth)) h_tail_wellformed h_lookup
    cases h_tail with
    | inl h_in_modified =>
      -- k → v is in (acc.insertIfNew head.fingerprint (head.state, head.depth))
      -- Check if it came from the insertion or was already in acc
      rw [Std.HashMap.getElem?_insertIfNew] at h_in_modified
      split at h_in_modified
      · -- Case: (head.fingerprint == k) = true and head.fingerprint not in acc
        -- This means the key was just inserted
        next h_cond =>
          obtain ⟨h_beq, h_not_mem⟩ := h_cond
          right
          -- Provide witnesses: head.state and head.depth
          -- From BEq equality to propositional equality
          have h_eq : head.fingerprint = k := by
            have : LawfulBEq σₕ := inferInstanceAs (LawfulBEq σₕ)
            exact LawfulBEq.eq_of_beq h_beq
          refine ⟨head.state, head.depth, ?_, ?_, ?_⟩
          · have : ⟨k, head.state, head.depth⟩ = head := by rw [← h_eq]
            rw [this]
            exact List.Mem.head tail
          · have h_head_wellformed : head.fingerprint = fp.view head.state := by
              exact h_wellformed head.fingerprint head.state head.depth (List.Mem.head tail)
            rw [← h_eq]
            exact h_head_wellformed
          · -- Show v = (head.state, head.depth)
            cases h_in_modified
            rfl
      · -- Case: either k ≠ head.fingerprint or head.fingerprint was already in acc
        -- In both cases, the lookup goes to acc
        next =>
          left
          exact h_in_modified
    | inr h_in_tail =>
      obtain ⟨x, d, h_mem, h_fp_eq, h_val_eq⟩ := h_in_tail
      right
      refine ⟨x, d, ?_, h_fp_eq, h_val_eq⟩
      right
      exact h_mem


/-- Auxiliary lemma: foldl with insertIfNew preserves the property that all states in the HashMap are reachable -/
@[grind .]
theorem foldl_insertIfNew_preserves_reachability
  {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (arr : Array (QueueItem σₕ σ))
  (init : Std.HashMap σₕ (σ × Nat))
  (h_init : ∀ x d, init[fp.view x]? = some (x, d) → sys.reachable x)
  (h_arr : ∀ x d, ⟨fp.view x, x, d⟩ ∈ arr → sys.reachable x)
  (h_arr_wellformed : ∀ fingerprint st d, ⟨fingerprint, st, d⟩ ∈ arr → fingerprint = fp.view st) :
  ∀ x d, (arr.foldl (init := init) fun acc ⟨h, x, d⟩ => acc.insertIfNew h (x, d))[fp.view x]? = some (x, d) →
    sys.reachable x := by
  intro x d h_in_result
  simp at h_in_result
  have h_cases : init[fp.view x]? = some (x, d) ∨
                 ∃ x' d', ⟨fp.view x, x', d'⟩ ∈ arr ∧ fp.view x = fp.view x' ∧ (x, d) = (x', d') :=
    @getElem?_foldl_insertIfNew ρ σ κ σₕ fp _ _ arr init (fp.view x) (x, d) h_arr_wellformed h_in_result
  cases h_cases with
  | inl h_in_init => exact h_init x d h_in_init
  | inr h_in_arr =>
    have ⟨x', d', h_mem, h_fp_eq, h_val_eq⟩ := h_in_arr
    have h_x_eq : x = x' := by injection h_val_eq with h1 h2;
    have h_d_eq : d = d' := by injection h_val_eq with h1 h2;
    rw [h_x_eq]
    have h_mem' : ⟨fp.view x', x', d'⟩ ∈ arr := by
      rw [← h_fp_eq]
      exact h_mem
    exact h_arr x' d' h_mem'



/- If `m[k]? = some v` after `foldl insert` on a list, then either `m` originally had `k -> v`,
    or `(k, v)` was inserted from the list. -/
theorem HashMap.getElem?_foldl_insert {α β σₕ : Type} [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (l : List α) (acc : Std.HashMap σₕ β) (k : σₕ) (v : β)
  (f_key : α → σₕ) (f_val : α → β)
  (h_lookup : (l.foldl (fun acc a => acc.insert (f_key a) (f_val a)) acc)[k]? = some v) :
  acc[k]? = some v ∨ (k, v) ∈ l.map (fun a => (f_key a, f_val a)) := by
  induction l generalizing acc with
  | nil =>
    simp at h_lookup
    left; exact h_lookup
  | cons head tail ih =>
    simp only [List.foldl] at h_lookup
    have h_tail := ih (acc.insert (f_key head) (f_val head)) h_lookup
    cases h_tail with
    | inl h_in_modified =>
      by_cases h_eq : k = f_key head
      · have h_get : (acc.insert (f_key head) (f_val head))[k]? = some (f_val head) := by rw [h_eq]; exact Std.HashMap.getElem?_insert_self
        rw [h_get] at h_in_modified
        cases h_in_modified
        right
        simp only [List.map_cons, List.mem_cons]
        left
        rw [h_eq]
      · have h_get : (acc.insert (f_key head) (f_val head))[k]? = acc[k]? := by
          rw [Std.HashMap.getElem?_insert];grind
        rw [h_get] at h_in_modified
        left; exact h_in_modified
    | inr h_in_tail =>
      right
      simp only [List.map_cons, List.mem_cons]
      right
      exact h_in_tail

/- Insert operation preserves existing keys: if a key has a value before insert, it still has some value after insert. -/
@[grind .]
theorem HashMap.getElem?_isSome_of_insert {β σₕ : Type} [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (m : Std.HashMap σₕ β) (k k' : σₕ) (v' : β)
  (h : m[k]?.isSome) :
  (m.insert k' v')[k]?.isSome := by
  by_cases h_eq : k = k'
  · rw [h_eq, Std.HashMap.getElem?_insert_self]; simp
  · rw [Std.HashMap.getElem?_insert]; split
    · rename_i h_beq
      have : k' = k := LawfulBEq.eq_of_beq h_beq
      have : k = k' := this.symm
      contradiction
    · exact h

/-- Helper: if a key has some value in a map, then after foldl insert, it still has some value. -/
theorem HashMap.isSome_preserved_by_foldl_insert {α β σₕ : Type} [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (l : List α) (acc : Std.HashMap σₕ β) (k : σₕ)
  (f_key : α → σₕ) (f_val : α → β)
  (h : acc[k]?.isSome) :
  (l.foldl (fun acc a => acc.insert (f_key a) (f_val a)) acc)[k]?.isSome := by
  induction l generalizing acc with
  | nil => simp;grind
  | cons head tail ih =>
    simp only [List.foldl]
    apply ih
    exact HashMap.getElem?_isSome_of_insert acc k (f_key head) (f_val head) h

/- If an element `a` is in the list, then after `foldl insert`, the key `f_key a` is in the resulting HashMap. -/
theorem HashMap.mem_of_foldl_insert {α β σₕ : Type} [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (l : List α) (acc : Std.HashMap σₕ β) (a : α)
  (f_key : α → σₕ) (f_val : α → β)
  (h_mem : a ∈ l) :
  ∃ v, (l.foldl (fun acc a => acc.insert (f_key a) (f_val a)) acc)[f_key a]? = some v := by
  induction l generalizing acc with
  | nil => simp at h_mem
  | cons head tail ih =>
    simp only [List.mem_cons] at h_mem
    cases h_mem with
    | inl h_eq =>
      -- a = head
      rw [h_eq]; clear h_eq
      simp only [List.foldl]
      -- After inserting (f_key head, f_val head), the key f_key head is in the map
      have h_inserted : (acc.insert (f_key head) (f_val head))[f_key head]? = some (f_val head) :=
        Std.HashMap.getElem?_insert_self
      -- Show that this key persists through the tail processing
      have h_isSome : (acc.insert (f_key head) (f_val head))[f_key head]?.isSome := by
        rw [h_inserted]; simp
      -- Use the helper lemma
      have h_persists := HashMap.isSome_preserved_by_foldl_insert tail (acc.insert (f_key head) (f_val head)) (f_key head) f_key f_val h_isSome
      simp only [Option.isSome_iff_exists] at h_persists
      exact h_persists
    | inr h_in_tail =>
      -- a ∈ tail
      simp only [List.foldl]
      exact ih (acc.insert (f_key head) (f_val head)) h_in_tail




/-- Theorem: Inserting a new fingerprint into seen and enqueuing the corresponding state preserves invariants.
    This theorem is used in tryExploreNeighbor when adding a newly discovered neighbor. -/
theorem ParallelSearchContextSub.insert_and_enqueue_preserves_invs {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [instBEq: BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (ctx : @ParallelSearchContextSub ρ σ κ σₕ fp _ _ th sys params)
  (fingerprint : σₕ)
  (succ : σ)
  (depth : Nat)
  (h_neighbor : sys.reachable succ)
  (h_fp : fingerprint = fp.view succ) :
  @SearchContextInvariants ρ σ κ σₕ fp th sys params
    (Membership.mem (ctx.tovisit.push ⟨fingerprint, succ, depth + 1⟩))
    (fun h => h ∈ ctx.seen ∨ h ∈ ctx.localSeen.insert fingerprint) := by
  constructor
  · -- queue_sound: states in the enqueued queue are reachable
    intro x d h_in_tovisit
    -- For Array.push, membership means either in original or is the new element
    have h_mem_push : (⟨fp.view x, x, d⟩ : QueueItem σₕ σ) ∈ ctx.tovisit ∨
                      (⟨fp.view x, x, d⟩ : QueueItem σₕ σ) = (⟨fingerprint, succ, depth + 1⟩ : QueueItem σₕ σ) := by
      grind
    rcases h_mem_push with h_in_old | h_is_new
    · -- x is in the original array
      exact ctx.invs.queue_sound x d h_in_old
    · -- x is the newly pushed element (succ)
      have h_x_eq : x = succ := by grind
      rw [h_x_eq]
      exact h_neighbor
  · -- visited_sound: elements in new seen are reachable
    intro h_view_inj x h_in_new_seen
    -- For HashSet.insert, element is in the new set if it equals fingerprint or was in the old sets
    simp only [Membership.mem] at h_in_new_seen
    by_cases h : fp.view x = fingerprint
    · -- x's fingerprint equals the new fingerprint, so x = succ
      have h_x_eq_succ : x = succ := by
        rw [h_fp] at h
        exact h_view_inj h
      rw [h_x_eq_succ]
      exact h_neighbor
    · -- x's fingerprint is different, so it must have been in the old seen sets
      have h_in_old : fp.view x ∈ ctx.seen ∨ fp.view x ∈ ctx.localSeen := by
        -- h_in_new_seen: fp.view x ∈ ctx.seen ∨ fp.view x ∈ ctx.localSeen.insert fingerprint
        cases h_in_new_seen with
        | inl h_seen => left; exact h_seen
        | inr h_in_insert =>
          -- fp.view x ∈ ctx.localSeen.insert fingerprint and fp.view x ≠ fingerprint
          right
          simp only [Membership.mem]
          have : (ctx.localSeen.insert fingerprint).contains (fp.view x) →
                 fp.view x ≠ fingerprint → ctx.localSeen.contains (fp.view x) := by
            intro h_contains h_neq
            grind
          exact this h_in_insert h
      exact ctx.invs.visited_sound h_view_inj x h_in_old
  · -- queue_sub_visited: elements in enqueued queue have fingerprints in new seen
    intro x d h_in_queue
    have h_mem_push : (⟨fp.view x, x, d⟩ : QueueItem σₕ σ) ∈ ctx.tovisit ∨
                      (⟨fp.view x, x, d⟩ : QueueItem σₕ σ) = (⟨fingerprint, succ, depth + 1⟩ : QueueItem σₕ σ) := by
      grind
    rcases h_mem_push with h_in_old | h_is_new
    · -- x is in the original array
      have h_in_old_seen := ctx.invs.queue_sub_visited x d h_in_old
      -- h_in_old_seen: fp.view x ∈ ctx.seen ∨ fp.view x ∈ ctx.localSeen
      simp only [Membership.mem]
      cases h_in_old_seen with
      | inl h_seen => left; exact h_seen
      | inr h_localSeen => right; exact Std.HashSet.mem_of_mem_insert'' ctx.localSeen (fp.view x) fingerprint h_localSeen
    · -- x is the newly pushed element
      have h_fp_eq : fp.view x = fingerprint := by grind
      simp only [Membership.mem]
      right
      rw [h_fp_eq]
      exact Std.HashSet.mem_insert_self' ctx.localSeen fingerprint
  · -- queue_wellformed: fingerprints match states in enqueued queue
    intro fp' st d h_in_queue
    have h_mem_push : (⟨fp', st, d⟩ : QueueItem σₕ σ) ∈ ctx.tovisit ∨
                      (⟨fp', st, d⟩ : QueueItem σₕ σ) = (⟨fingerprint, succ, depth + 1⟩ : QueueItem σₕ σ) := by
      grind
    rcases h_mem_push with h_in_old | h_is_new
    · -- in original array
      exact ctx.invs.queue_wellformed fp' st d h_in_old
    · -- newly pushed element
      have h_fp_eq : fp' = fingerprint := by grind
      have h_st_eq : st = succ := by grind
      rw [h_st_eq, h_fp_eq, h_fp]


/-- Theorem: Inserting a new fingerprint into seen and enqueuing the corresponding state preserves invariants.
    This theorem is used in tryExploreNeighbor when adding a newly discovered neighbor. -/
theorem ParallelSearchContextMerge.insert_and_enqueue_preserves_invs {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [instBEq: BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (ctx : @ParallelSearchContextMerge ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (fingerprint : σₕ)
  (succ : σ)
  (depth : Nat)
  (h_neighbor : sys.reachable succ)
  (h_fp : fingerprint = fp.view succ) :
  @SearchContextInvariants ρ σ κ σₕ fp th sys params
    ((fun ⟨h, x, d⟩ => (ctx.tovisit.insert fingerprint ⟨succ, depth + 1⟩)[h]? = some (x, d)))
    (fun h => h ∈ ctx.seen ∨ h ∈ ctx.localSeen.insert fingerprint) := by
  constructor
  · -- queue_sound: states in the new tovisit are reachable
    intro x d h_in_tovisit
    -- Simplify the match expression in h_in_tovisit
    simp only at h_in_tovisit
    -- For HashMap.insert, we case split on whether we hit the new key or an existing one
    rw [Std.HashMap.getElem?_insert] at h_in_tovisit
    split at h_in_tovisit
    · -- Case: fingerprint == fp.view x
      -- The lookup returns the newly inserted value (succ, depth + 1)
      next h_beq =>
        cases h_in_tovisit
        exact h_neighbor
    · -- Case: fingerprint ≠ fp.view x
      -- The lookup returns the original value from ctx.tovisit
      exact ctx.invs.queue_sound x d h_in_tovisit
  · -- visited_sound: elements in new seen are reachable
    intro h_view_inj x h_in_new_seen
    -- For HashSet.insert, element is in the new set if it equals fingerprint or was in the old sets
    simp only [Membership.mem] at h_in_new_seen
    by_cases h : fp.view x = fingerprint
    · -- x's fingerprint equals the new fingerprint, so x = succ
      have h_x_eq_succ : x = succ := by
        rw [h_fp] at h
        exact h_view_inj h
      rw [h_x_eq_succ]
      exact h_neighbor
    · -- x's fingerprint is different, so it must have been in the old seen sets
      have h_in_old : fp.view x ∈ ctx.seen ∨ fp.view x ∈ ctx.localSeen := by
        -- h_in_new_seen: fp.view x ∈ ctx.seen ∨ fp.view x ∈ ctx.localSeen.insert fingerprint
        cases h_in_new_seen with
        | inl h_seen => left; exact h_seen
        | inr h_in_insert =>
          -- fp.view x ∈ ctx.localSeen.insert fingerprint and fp.view x ≠ fingerprint
          right
          simp only [Membership.mem]
          have : (ctx.localSeen.insert fingerprint).contains (fp.view x) →
                 fp.view x ≠ fingerprint → ctx.localSeen.contains (fp.view x) := by
            intro h_contains h_neq
            grind
          exact this h_in_insert h
      exact ctx.invs.visited_sound h_view_inj x h_in_old
  · -- queue_sub_visited: elements in new tovisit have fingerprints in new seen
    intro x d h_in_queue
    -- Simplify the match expression
    simp only at h_in_queue
    -- Case split on insert
    rw [Std.HashMap.getElem?_insert] at h_in_queue
    split at h_in_queue
    · -- Case: fingerprint == fp.view x
      -- This is the newly inserted element
      next h_beq =>
        have h_fp_eq : fingerprint = fp.view x := LawfulBEq.eq_of_beq h_beq
        simp only [Membership.mem]
        right
        rw [← h_fp_eq]
        exact Std.HashSet.mem_insert_self' ctx.localSeen fingerprint
    · -- Case: lookup goes to original ctx.tovisit
      have h_in_old_seen := ctx.invs.queue_sub_visited x d h_in_queue
      simp only [Membership.mem]
      cases h_in_old_seen with
      | inl h_seen => left; exact h_seen
      | inr h_localSeen => right; exact Std.HashSet.mem_of_mem_insert'' ctx.localSeen (fp.view x) fingerprint h_localSeen
  · -- queue_wellformed: fingerprints match states in new tovisit
    intro fp' st d h_in_queue
    -- Simplify the match expression
    simp only at h_in_queue
    -- Case split on insert
    rw [Std.HashMap.getElem?_insert] at h_in_queue
    split at h_in_queue
    · -- Case: fingerprint == fp'
      -- This is the newly inserted element (succ, depth + 1)
      next h_beq =>
        have h_fp'_eq : fingerprint = fp' := LawfulBEq.eq_of_beq h_beq
        cases h_in_queue
        rw [← h_fp'_eq, h_fp]
    · -- Case: lookup goes to original ctx.tovisit
      exact ctx.invs.queue_wellformed fp' st d h_in_queue



-- High-level theorem: updating toBaseSearchContext after processState preserves invariants
-- This theorem says: when we extract ctx.toBaseSearchContext, apply processState to get baseCtx',
-- and put baseCtx' back into SequentialSearchContext, the invariants still hold
theorem ParallelSearchContextSub.update_base_after_processState_preserves_invs {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ] [BEq σ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  (ctx : @ParallelSearchContextSub ρ σ κ σₕ fp _ _ th sys params)
  (fpSt : σₕ)
  (curr : σ)
  (baseCtx' : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (h_process : (ctx.toBaseSearchContext.processState sys fpSt curr).1 = baseCtx') :
  @SearchContextInvariants ρ σ κ σₕ fp th sys params
    (Membership.mem ctx.tovisit)
    (fun h => h ∈ baseCtx'.seen ∨ h ∈ ctx.localSeen) := by
  have h_seen_unchanged : baseCtx'.seen = ctx.seen := by
    have h_preserves := BaseSearchContext.processState_preserves_seen sys params fpSt curr ctx.toBaseSearchContext
    rw [h_process] at h_preserves
    exact h_preserves
  constructor
  · intro x d h_in_queue; exact ctx.invs.queue_sound x d h_in_queue
  · intro h_view_inj x h_in_seen;
    rw [h_seen_unchanged] at h_in_seen
    have htmp := ctx.invs.visited_sound h_view_inj x
    grind
  · intro x d h_in_queue;
    have htmp := ctx.invs.queue_sub_visited x d h_in_queue
    grind
  · intro fp' st d h_in_queue; exact ctx.invs.queue_wellformed fp' st d h_in_queue


-- High-level theorem: updating toBaseSearchContext after processState preserves invariants
-- This is the version for ParallelSearchContextMerge (uses HashMap for tovisit)
theorem ParallelSearchContextMerge.update_base_after_processState_preserves_invs {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ] [BEq σ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (ctx : @ParallelSearchContextMerge ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (fpSt : σₕ)
  (curr : σ)
  (baseCtx' : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (h_process : (ctx.toBaseSearchContext.processState sys fpSt curr).1 = baseCtx') :
  @SearchContextInvariants ρ σ κ σₕ fp th sys params
    (fun ⟨h, x, d⟩ => ctx.tovisit[h]? = some (x, d))
    (fun h => h ∈ baseCtx'.seen ∨ h ∈ ctx.localSeen) := by
  have h_seen_unchanged : baseCtx'.seen = ctx.seen := by
    have h_preserves := BaseSearchContext.processState_preserves_seen sys params fpSt curr ctx.toBaseSearchContext
    rw [h_process] at h_preserves
    exact h_preserves
  constructor
  · -- queue_sound: states in tovisit are reachable
    intro x d h_in_queue
    exact ctx.invs.queue_sound x d h_in_queue
  · -- visited_sound: elements in seen ∪ localSeen are reachable
    intro h_view_inj x h_in_seen
    rw [h_seen_unchanged] at h_in_seen
    have htmp := ctx.invs.visited_sound h_view_inj x
    -- h_in_seen : fp.view x ∈ ctx.seen ∨ fp.view x ∈ ctx.localSeen
    -- ctx.invs.visited_sound needs: fp.view x ∈ ctx.seen ∨ fp.view x ∈ ctx.localSeen
    exact htmp h_in_seen
  · -- queue_sub_visited: elements in tovisit have fingerprints in seen ∪ localSeen
    intro x d h_in_queue
    have htmp := ctx.invs.queue_sub_visited x d h_in_queue
    -- htmp : fp.view x ∈ ctx.seen ∨ fp.view x ∈ ctx.localSeen
    -- goal : fp.view x ∈ baseCtx'.seen ∨ fp.view x ∈ ctx.localSeen
    rw [h_seen_unchanged]
    exact htmp
  · -- queue_wellformed: fingerprints match states
    intro fp' st d h_in_queue
    exact ctx.invs.queue_wellformed fp' st d h_in_queue


structure ParallelSearchContextMain' {ρ σ κ σₕ : Type}
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




theorem ParallelSearchContextMain.merge_preserves_frontier_closed {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (ctx : @ParallelSearchContextMain ρ σ κ σₕ fp _ _ th sys params)
  (unionSeen : Std.HashSet σₕ)
  -- (h_disjoint : ∀ h, h ∈ unionSeen → ¬(h ∈ ctx.seen))
  (currTovisit : Std.HashMap σₕ (σ × Nat))
  (h_not_finished : ctx.finished = none)
  (h_view_inj : Function.Injective fp.view)
  -----------------------------------------------------------------------------
  (h_delta_consistent : Function.Injective fp.view →
    ∀ x, (fp.view x) ∈ unionSeen → ∃d, currTovisit[(fp.view x)]? = some (x, d))
  -----------------------------------------------------------------------------
  (h_collect_all : ∀ (s : σ) (d : Nat),
    ctx.tovisit[fp.view s]? = some (s, d) →
      (∀l v, (l, .success v) ∈ (sys.tr th s)
        → ((fp.view v) ∈ ctx.seen ∨ (fp.view v) ∈ unionSeen)))
  -----------------------------------------------------------------------------
  : ∀ (s : σ), fp.view s ∈ (ctx.seen.union unionSeen) →      -- s is discovered
      (currTovisit[(fp.view s)]? = none) →          -- s is not in the frontier
      ∀ l next_s, (l, .success next_s) ∈ sys.tr th s →    -- for all successors
        fp.view next_s ∈ ctx.seen.union unionSeen
  -----------------------------------------------------------------------------
  := by
  intro s h_in_new_seen h_not_in_new_tovisit l next_s h_tr
  rw [Std.HashSet.mem_union] at h_in_new_seen
  rcases h_in_new_seen with h_in_old_seen | h_in_new_added
  · -- Check if s is in the old tovisit queue
    cases h_in_old_queue : ctx.tovisit[(fp.view s)]? with
    | none =>
      -- Subcase B.2 (Case 1): (`s ∉ Q_old`)
      have h_old_invariant := ctx.frontier_closed h_view_inj (by
        right; exact h_not_finished
      ) s h_in_old_seen h_in_old_queue l next_s h_tr
      rw [Std.HashSet.mem_union]
      left; exact h_old_invariant
    | some val =>
      -- Subcase B.1 (Case 2): (`s ∈ Q_old`) h_collect_all
      obtain ⟨s', d⟩ := val
      have h_s'_eq_s : s' = s := by
        have h_in_queue : (fun ⟨h, x, d⟩ => ctx.tovisit[h]? = some (x, d)) (QueueItem.mk (fp.view s) s' d) := by simp only; exact h_in_old_queue
        have h_fp_eq : fp.view s = fp.view s' := ctx.invs.queue_wellformed (fp.view s) s' d h_in_queue
        exact h_view_inj h_fp_eq.symm
      have h_in_queue : ctx.tovisit[fp.view s]? = some (s, d) := by
        have : (s', d) = (s, d) := by rw [h_s'_eq_s]
        rw [← this]; exact h_in_old_queue
      have h_all_succ := h_collect_all s d h_in_queue
      have h_is_successful : (l, next_s) ∈ extractSuccessfulTransitions (sys.tr th s) := by unfold extractSuccessfulTransitions; grind
      have h_succ_in_union : fp.view next_s ∈ ctx.seen ∨ fp.view next_s ∈ unionSeen :=
        h_all_succ l next_s (by simp [h_tr])
      rw [Std.HashSet.mem_union]
      exact h_succ_in_union
  -- Case A (Case 3): (`s ∈ unionSeen`) --h_delta_consistent
  · have h_must_be_in_queue := h_delta_consistent h_view_inj s h_in_new_added
    obtain ⟨d, h_in_q⟩ := h_must_be_in_queue
    rw [h_in_q] at h_not_in_new_tovisit
    contradiction

/-- Helper: insertIfNew preserves existing key's value -/
theorem HashMap.getElem?_insertIfNew_of_contains {σₕ β : Type}
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (m : Std.HashMap σₕ β) (k k' : σₕ) (v v' : β)
  (h_in : m[k]? = some v) :
  (m.insertIfNew k' v')[k]? = some v := by
  rw [Std.HashMap.getElem?_insertIfNew]
  split
  · next h_cond =>
    -- k' == k and k' ∉ m, but k ∈ m since m[k]? = some v
    have ⟨h_eq, h_not_in⟩ := h_cond
    have h_k'_eq_k : k' = k := LawfulBEq.eq_of_beq h_eq
    subst h_k'_eq_k
    -- Now h_not_in : k ∉ m, but we have m[k]? = some v
    simp only [Std.HashMap.mem_iff_contains] at h_not_in
    grind
  · exact h_in

/-- Helper: insertIfNew adds new key's value when key not present -/
theorem HashMap.getElem?_insertIfNew_of_not_contains_same_key {σₕ β : Type}
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (m : Std.HashMap σₕ β) (k : σₕ) (v : β)
  (h_not_in : k ∉ m) :
  (m.insertIfNew k v)[k]? = some v := by
  rw [Std.HashMap.getElem?_insertIfNew]
  split
  · next h_cond => rfl
  · next h_cond =>
    push_neg at h_cond
    have h_beq_refl : (k == k) = true := by simp
    have h := h_cond h_beq_refl
    simp only [Std.HashMap.mem_iff_contains] at h_not_in
    contradiction

/-- Helper: insertIfNew preserves key's value when inserting different key -/
theorem HashMap.getElem?_insertIfNew_of_ne {σₕ β : Type}
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (m : Std.HashMap σₕ β) (k k' : σₕ) (v' : β)
  (h_ne : k ≠ k') :
  (m.insertIfNew k' v')[k]? = m[k]? := by
  rw [Std.HashMap.getElem?_insertIfNew]
  split
  · next h_cond =>
    have ⟨h_eq, _⟩ := h_cond
    have h_k'_eq_k : k' = k := LawfulBEq.eq_of_beq h_eq
    exact absurd h_k'_eq_k.symm h_ne
  · rfl

/-- For insertIfNew: if key is already in m2, it preserves m2's value (won't be overwritten).
    This uses HashMap.fold which iterates over toList. -/
theorem HashMap.getElem?_fold_insertIfNew_preserves_m2 {σₕ β : Type}
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (m1 m2 : Std.HashMap σₕ β) (k : σₕ) (v : β)
  (h_in_m2 : m2[k]? = some v) :
  (m1.fold (init := m2) fun acc k' v' => acc.insertIfNew k' v')[k]? = some v := by
  rw [Std.HashMap.fold_eq_foldl_toList]
  generalize h_l : m1.toList = l
  clear h_l
  induction l generalizing m2 with
  | nil =>
    simp only [List.foldl]
    exact h_in_m2
  | cons hd tl ih =>
    -- Step case
    simp only [List.foldl]
    apply ih
    apply HashMap.getElem?_insertIfNew_of_contains
    exact h_in_m2


/-- Helper: List.foldl with insertIfNew preserves existing key's value -/
theorem List.foldl_insertIfNew_preserves {σₕ β : Type}
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (l : List (σₕ × β)) (acc : Std.HashMap σₕ β) (k : σₕ) (v : β)
  (h_in_acc : acc[k]? = some v) :
  (l.foldl (fun acc (kv : σₕ × β) => acc.insertIfNew kv.1 kv.2) acc)[k]? = some v := by
  induction l generalizing acc with
  | nil => simp only [List.foldl]; exact h_in_acc
  | cons hd tl ih =>
    simp only [List.foldl]
    apply ih
    apply HashMap.getElem?_insertIfNew_of_contains
    exact h_in_acc

/-- 主定理：如果 key 在 m1 中但不在 m2 中，fold insertIfNew 后它会被正确插入 -/
theorem HashMap.getElem?_fold_insertIfNew_from_m1 {σₕ β : Type}
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (m1 m2 : Std.HashMap σₕ β) (k : σₕ) (v : β)
  (h_in_m1 : m1[k]? = some v)
  (h_not_in_m2 : k ∉ m2) :
  (m1.fold (init := m2) fun acc k' v' => acc.insertIfNew k' v')[k]? = some v := by
  -- 1. 转换 fold 为 List foldl
  rw [Std.HashMap.fold_eq_foldl_toList] -- [cite: 266]
  -- 2. 证明 (k, v) 存在于 m1.toList 中
  have h_mem : (k, v) ∈ m1.toList := by
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] -- [cite: 252]
    exact h_in_m1
  -- 3. 证明 m1.toList 的 Key 是唯一的 (Nodup)
  have h_nodup : m1.toList.map Prod.fst |> List.Nodup := by
    rw [Std.HashMap.map_fst_toList_eq_keys] --
    exact Std.HashMap.nodup_keys --
  generalize h_l : m1.toList = l
  rw [h_l] at h_mem h_nodup
  clear h_l
  induction l generalizing m2 with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.foldl, List.mem_cons, List.map_cons, List.nodup_cons] at h_mem h_nodup ⊢
    obtain ⟨h_key_not_in_tail, h_tail_unique⟩ := h_nodup
    by_cases h_eq : hd.1 = k
    · -- Case A: 当前处理的元素就是 k
      -- 因为 Key 唯一且 (k, v) 在列表中，所以 hd 必须是 (k, v)
      have h_val : hd.2 = v := by
        cases h_mem with
        | inl h_head => grind
        | inr h_tail => grind
      subst h_eq
      subst h_val
      -- 这一步将 (k, v) 插入 m2
      -- 下一步的目标是证明：剩下的 foldl (tl) 会保留这个值
      apply List.foldl_insertIfNew_preserves
      -- 证明当前插入成功：因为 k ∉ m2，所以 insertIfNew 会写入 (k, v)
      apply HashMap.getElem?_insertIfNew_of_not_contains_same_key
      exact h_not_in_m2
    · -- Case B: 当前处理的不是 k
      apply ih
      · -- 证明 (k, v) 在 tail 中
        cases h_mem
        · rename_i h_head
          grind
        · grind
      · exact h_tail_unique
      · -- 证明 k 依然不在新的 accumulator (m2.insertIfNew hd.1 hd.2) 中
        -- 因为 k ∉ m2 且 k ≠ hd.1
        grind

/- Combined lemma for deltaConsistent: when key is in localSeen (from either ctx),
    and both tovisit maps satisfy queue_wellformed, the result tovisit has (x, d) for some d.
    Uses insertIfNew semantics: m2 values take precedence over m1. -/
theorem HashMap.getElem?_fold_insertIfNew_deltaConsistent {σₕ σ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (m1 m2 : Std.HashMap σₕ (σ × Nat)) (x : σ)
  -- (h_m1_wellformed : ∀ k x' d, m1[k]? = some (x', d) → k = fp.view x')
  (h_m2_wellformed : ∀ k x' d, m2[k]? = some (x', d) → k = fp.view x')
  (h_inj : Function.Injective fp.view)
  -- Either m1 or m2 has the entry for x
  (h_exists : (∃ d, m1[fp.view x]? = some (x, d)) ∨ (∃ d, m2[fp.view x]? = some (x, d))) :
  ∃ d', (m1.fold (init := m2) fun acc k' v' => acc.insertIfNew k' v')[fp.view x]? = some (x, d') := by
  rcases h_exists with ⟨d1, h_in_m1⟩ | ⟨d2, h_in_m2⟩
  · -- Case: entry is in m1
    by_cases h_key_in_m2 : (fp.view x) ∈ m2
    · -- Subcase: key also in m2, insertIfNew preserves m2's value
      -- By queue_wellformed + injectivity, m2's value is also (x, _)
      have h_m2_some : (m2[fp.view x]?).isSome := by grind
      obtain ⟨⟨x', d'⟩, h_m2_lookup⟩ := Option.isSome_iff_exists.mp h_m2_some
      have h_wf := h_m2_wellformed (fp.view x) x' d' h_m2_lookup
      -- h_wf : fp.view x = fp.view x', so by injectivity x = x'
      have h_eq : x = x' := h_inj h_wf
      subst h_eq
      use d'
      exact HashMap.getElem?_fold_insertIfNew_preserves_m2 m1 m2 (fp.view x) (x, d') h_m2_lookup
    · -- Subcase: key not in m2, insertIfNew inserts m1's value
      use d1
      exact HashMap.getElem?_fold_insertIfNew_from_m1 m1 m2 (fp.view x) (x, d1) h_in_m1 h_key_in_m2
  · -- Case: entry is in m2, insertIfNew preserves it
    use d2
    exact HashMap.getElem?_fold_insertIfNew_preserves_m2 m1 m2 (fp.view x) (x, d2) h_in_m2


/-- Helper: trace back the source of a lookup result from List.foldl insertIfNew.
    If we get a result, it came from either acc (preserved) or the list (inserted). -/
theorem List.foldl_insertIfNew_source {σₕ β : Type}
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (l : List (σₕ × β)) (acc : Std.HashMap σₕ β) (k : σₕ) (v : β)
  (h_lookup : (l.foldl (fun acc (kv : σₕ × β) => acc.insertIfNew kv.1 kv.2) acc)[k]? = some v) :
  acc[k]? = some v ∨ ((k, v) ∈ l ∧ k ∉ acc) := by
  induction l generalizing acc with
  | nil =>
    simp only [List.foldl] at h_lookup
    left; exact h_lookup
  | cons hd tl ih =>
    simp only [List.foldl] at h_lookup
    have h_step := ih (acc.insertIfNew hd.1 hd.2) h_lookup
    cases h_step with
    | inl h_in_step =>
      -- v is in (acc.insertIfNew hd.1 hd.2)
      rw [Std.HashMap.getElem?_insertIfNew] at h_in_step
      split at h_in_step
      · -- hd.1 == k and hd.1 ∉ acc, so hd was inserted
        next h_cond =>
          have ⟨h_beq, h_not_in⟩ := h_cond
          have h_hd1_eq_k : hd.1 = k := LawfulBEq.eq_of_beq h_beq
          right
          constructor
          · simp only [List.mem_cons]
            left; rw [← h_hd1_eq_k]
            cases h_in_step
            rfl
          · grind
      · -- k ≠ hd.1 or hd.1 was already in acc
        left; exact h_in_step
    | inr h_from_tl =>
      -- v came from tl and k ∉ (acc.insertIfNew hd.1 hd.2)
      have ⟨h_in_tl, h_not_in_step⟩ := h_from_tl
      right
      constructor
      · simp only [List.mem_cons]
        right; exact h_in_tl
      · -- k ∉ acc: since k ∉ (acc.insertIfNew hd.1 hd.2)
        simp only [Std.HashMap.mem_iff_contains] at h_not_in_step ⊢
        simp only [Std.HashMap.contains_insertIfNew] at h_not_in_step
        push_neg at h_not_in_step
        grind

/-- Helper: trace back the source of a lookup result from HashMap.fold insertIfNew.
    If we get a result, it came from either m2 (preserved) or m1 (inserted when key not in m2). -/
theorem HashMap.getElem?_fold_insertIfNew_source {σₕ β : Type}
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (m1 m2 : Std.HashMap σₕ β) (k : σₕ) (v : β)
  (h_lookup : (m1.fold (init := m2) fun acc k' v' => acc.insertIfNew k' v')[k]? = some v) :
  m2[k]? = some v ∨ (m1[k]? = some v ∧ k ∉ m2) := by
  rw [Std.HashMap.fold_eq_foldl_toList] at h_lookup
  have h_source := List.foldl_insertIfNew_source m1.toList m2 k v h_lookup
  cases h_source with
  | inl h_from_m2 => left; exact h_from_m2
  | inr h_from_list =>
    right
    have ⟨h_in_list, h_not_in_m2⟩ := h_from_list
    constructor
    · rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at h_in_list
      exact h_in_list
    · exact h_not_in_m2

/-- Reachability is preserved through HashMap.fold with insertIfNew.
    If both m1 and m2 contain only reachable states, so does the result. -/
theorem HashMap.fold_insertIfNew_preserves_reachability {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (m1 m2 : Std.HashMap σₕ (σ × Nat))
  (h_m1_sound : ∀ x d, m1[fp.view x]? = some (x, d) → sys.reachable x)
  (h_m2_sound : ∀ x d, m2[fp.view x]? = some (x, d) → sys.reachable x) :
  ∀ x d, (m1.fold (init := m2) fun acc k v => acc.insertIfNew k v)[fp.view x]? = some (x, d) →
    sys.reachable x := by
  intro x d h_lookup
  have h_source := HashMap.getElem?_fold_insertIfNew_source m1 m2 (fp.view x) (x, d) h_lookup
  cases h_source with
  | inl h_from_m2 => exact h_m2_sound x d h_from_m2
  | inr h_from_m1 => exact h_m1_sound x d h_from_m1.1


/-- If a key-value pair is in a HashMap, it's in the toArray representation. -/
theorem HashMap.mem_toArray_of_getElem? {α β : Type} [BEq α] [Hashable α]
  [LawfulBEq α]
  (m : Std.HashMap α β) (k : α) (v : β)
  (h : m[k]? = some v) :
  (k, v) ∈ m.toArray := by
  simp [Array.mem_def] at *
  grind

/-- If a key-value pair is in the toArray representation, it's in the HashMap. -/
theorem HashMap.getElem?_of_mem_toArray {α β : Type} [BEq α] [Hashable α]
  [LawfulBEq α]
  (m : Std.HashMap α β) (k : α) (v : β)
  (h : (k, v) ∈ m.toArray) :
  m[k]? = some v := by
  simp [Array.mem_def] at *
  grind

/-- Elements in Array.extract are from the original array. -/
theorem Array.mem_of_mem_extract {α : Type} (arr : Array α) (i j : Nat) (x : α)
  (h : x ∈ arr.extract i j) : x ∈ arr := by
  rw [Array.mem_def] at h ⊢
  rw [Array.toList_extract] at h
  exact List.mem_of_mem_drop (List.mem_of_mem_take h)

/-- ParallelConfig.chunkRanges produces valid ranges (within bounds). -/
theorem ParallelConfig.chunkRanges_valid (cfg : ParallelConfig) (n : Nat) :
  ∀ lr ∈ cfg.chunkRanges n, lr.1 ≤ lr.2 ∧ lr.2 ≤ n := by
  intro lr h_lr_in
  unfold ParallelConfig.chunkRanges at h_lr_in
  split at h_lr_in
  · -- Case: n < cfg.thresholdToParallel, ranges = [(0, n)]
    simp at h_lr_in
    grind
  · -- Case: n ≥ cfg.thresholdToParallel
    rename_i h_not_small
    simp at h_not_small
    -- ranges = List.range numSubTasks |>.map (fun i => ...)
    simp [List.mem_map] at h_lr_in
    obtain ⟨i, h_i_in, h_lr_eq⟩ := h_lr_in
    split
    . simp
    . simp
      rename_i h_lr_eq
      apply Nat.div_le_self
    constructor
    .
      rename_i h_lr_eq
      obtain ⟨a, h_a_lt, h_eq⟩ := h_lr_eq
      rw [← h_eq]
      dsimp
      split_ifs
      · apply Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.lt_of_lt_of_le h_a_lt (le_max_right _ _))))
        rw [Nat.mul_comm]
        apply Nat.div_mul_le_self
      · apply Nat.mul_le_mul_right
        apply Nat.le_succ
    .
      rename_i h_lr_eq
      obtain ⟨a, h_a_lt, h_eq⟩ := h_lr_eq
      rw [← h_eq]; dsimp
      split_ifs <;> try apply Nat.le_refl
      trans (max 1 cfg.numSubTasks) * (n / max 1 cfg.numSubTasks)
      · apply Nat.mul_le_mul_right; omega
      · rw [Nat.mul_comm]; apply Nat.div_mul_le_self


/-- ParallelConfig.chunkRanges covers all indices. -/
theorem ParallelConfig.chunkRanges_cover (cfg : ParallelConfig) (n : Nat) :
  ∀ i, i < n → ∃ lr ∈ cfg.chunkRanges n, lr.1 ≤ i ∧ i < lr.2 := by
  intro i h_i_lt
  unfold ParallelConfig.chunkRanges
  split
  · -- Case: n < cfg.thresholdToParallel, ranges = [(0, n)]
    exists (0, n)
    simp
    omega
  · -- Case: n ≥ cfg.thresholdToParallel
    rename_i h_not_small
    let k := max 1 cfg.numSubTasks
    let s := n / k
    have hk_pos : 0 < k := Nat.le_max_left 1 _
    let idx := if i < (k - 1) * s then i / s else k - 1
    let l := idx * s
    let r := if idx == k - 1 then n else (idx + 1) * s
    exists (l, r)
    constructor
    · apply List.mem_map_of_mem
      rw [List.mem_range]
      dsimp [idx]
      split_ifs with h_cond
      · have hs_pos : 0 < s := Nat.pos_of_ne_zero (fun h => by simp [h] at h_cond)
        calc
          i / s < k - 1 := Nat.div_lt_of_lt_mul (by grind)
          _     < k     := Nat.pred_lt (by grind)
      · apply Nat.pred_lt (by grind)
    . simp
      constructor
      . -- sub-goal: l ≤ i
        dsimp [l, idx]
        split_ifs with h_cond
        . exact Nat.div_mul_le_self i s
        . omega
      . dsimp [r]
        split_ifs with h_is_last
        . exact h_i_lt
        . simp [idx] at h_is_last
          have h_idx_val : idx = i / s := by
            dsimp [idx]; split_ifs; rfl; grind
          rw [h_idx_val]
          rw [Nat.add_mul]
          rw [Nat.one_mul]
          apply Nat.lt_div_mul_add
          refine Nat.pos_of_ne_zero (fun h_s_zero => ?_)
          have h_lt := h_is_last.1
          rw [h_s_zero, Nat.mul_zero] at h_lt
          exact Nat.not_lt_zero i h_lt


theorem Array.mem_flatten_of_partition {α : Type}
  (arr : Array α)
  (ranges : List (Nat × Nat))
  (x : α) (h_mem : x ∈ arr)
  (h_cover : ∀ i, i < arr.size → ∃ lr ∈ ranges, lr.1 ≤ i ∧ i < lr.2)
  (h_valid : ∀ lr ∈ ranges, lr.1 ≤ lr.2 ∧ lr.2 ≤ arr.size) :
  x ∈ (ranges.map fun lr => (arr.extract lr.1 lr.2)).toArray.flatten := by
  rcases Array.mem_iff_getElem.mp h_mem with ⟨i, h_i_lt, rfl⟩
  rcases h_cover i h_i_lt with ⟨lr, h_lr_in, h_l_le, h_i_lt_r⟩
  rw [Array.mem_flatten]
  let subArr := (arr.extract lr.1 lr.2)
  exists subArr
  constructor
  . rw [List.mem_toArray, List.mem_map]; exists lr
  . dsimp [subArr]
    rw [Array.mem_iff_getElem]
    have h_idx_valid : i - lr.1 < (arr.extract lr.1 lr.2).size := by
      rw [Array.size_extract]
      have h_le_size : lr.2 ≤ arr.size := (h_valid lr h_lr_in).2
      rw [Nat.min_eq_left h_le_size]
      apply Nat.sub_lt_sub_right h_l_le h_i_lt_r
    grind





end Veil.ModelChecker.Concrete
