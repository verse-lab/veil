import Veil.Core.Tools.ModelChecker.Concrete.SearchContext

namespace Veil.ModelChecker.Concrete

theorem concurrent_bfs_completeness {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (ctx : @ParallelSearchContext ρ σ κ σₕ fp _ _ th sys params)
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
    have h_tovisit_empty : ctx.tovisitQueue.isEmpty := ctx.terminate_empty_tovisit h_explore_all
    have h_u_not_in_tovisit : fp.view u ∉ ctx.tovisitSet := by
      intro h_in_set
      have ⟨item, h_item_in_queue, _⟩ := ctx.tovisitConsistent (fp.view u) |>.mp h_in_set
      have h_not_empty : ¬ctx.tovisitQueue.isEmpty := by
        simp only [Array.isEmpty_iff]
        intro h_eq_empty
        rw [h_eq_empty] at h_item_in_queue
        exact (Array.not_mem_empty item) h_item_in_queue
      exact h_not_empty h_tovisit_empty
    have h_finished_cond : ctx.finished = some (.exploredAllReachableStates) ∨ ctx.finished = none := by
      left; exact h_explore_all
    exact ctx.frontier_closed h_view_inj h_finished_cond u h_u_in_seen h_u_not_in_tovisit l v h_tr


/-- Pushing an item to the queue and inserting its fingerprint to the set preserves tovisitConsistent. -/
theorem LocalSearchContext.push_insert_preserves_tovisitConsistent {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th}
  {params : SearchParameters ρ σ}
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (ctx : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (fingerprint : σₕ)
  (succ : σ)
  (depth : Nat) :
  ∀ h, h ∈ ctx.tovisitSet.insert fingerprint ↔
    ∃ item ∈ ctx.tovisitQueue.push ⟨fingerprint, succ, depth + 1⟩, item.fingerprint = h := by
  intro h
  rw [Std.HashSet.mem_insert]
  constructor
  · intro h_in_set
    cases h_in_set with
    | inl h_eq =>
      refine ⟨⟨fingerprint, succ, depth + 1⟩, ?_, ?_⟩
      · rw [Array.mem_push]; exact Or.inr rfl
      · simp only; exact LawfulBEq.eq_of_beq h_eq
    | inr h_in_old =>
      have ⟨item, h_item_in, h_item_fp⟩ := ctx.tovisitConsistent h |>.mp h_in_old
      refine ⟨item, ?_, h_item_fp⟩
      rw [Array.mem_push]
      exact Or.inl h_item_in
  · intro ⟨item, h_item_in, h_item_fp⟩
    rw [Array.mem_push] at h_item_in
    cases h_item_in with
    | inl h_in_old =>
      right
      exact ctx.tovisitConsistent h |>.mpr ⟨item, h_in_old, h_item_fp⟩
    | inr h_eq =>
      left
      have h_fp_eq : fingerprint = item.fingerprint := by simp [h_eq]
      rw [h_fp_eq, h_item_fp]
      exact BEq.refl _


/-- Merging two LocalSearchContext instances preserves tovisitConsistent. -/
theorem merge_local_local_preserves_tovisitConsistent {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (ctx1 ctx2 : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx) :
  let filteredQueue := ctx2.tovisitQueue.filter fun item => !ctx1.tovisitSet.contains item.fingerprint
  ∀ h, h ∈ ctx1.tovisitSet.union ctx2.tovisitSet ↔
    ∃ item ∈ (ctx1.tovisitQueue ++ filteredQueue), item.fingerprint = h := by
  intro filteredQueue h
  constructor
  · intro h_in_union
    simp only [Std.HashSet.mem_union] at h_in_union
    cases h_in_union with
    | inl h_in_ctx1 =>
      have ⟨item, h_item_in, h_item_fp⟩ := ctx1.tovisitConsistent h |>.mp h_in_ctx1
      refine ⟨item, ?_, h_item_fp⟩
      simp only [Array.mem_append]
      exact Or.inl h_item_in
    | inr h_in_ctx2 =>
      have ⟨item, h_item_in, h_item_fp⟩ := ctx2.tovisitConsistent h |>.mp h_in_ctx2
      by_cases h_in_ctx1_set : ctx1.tovisitSet.contains item.fingerprint
      · -- Item is already in ctx1's set, so some item with same fingerprint is in ctx1's queue
        have ⟨item1, h_item1_in, h_item1_fp⟩ := ctx1.tovisitConsistent item.fingerprint |>.mp h_in_ctx1_set
        refine ⟨item1, ?_, ?_⟩
        · simp only [Array.mem_append]; exact Or.inl h_item1_in
        · rw [h_item1_fp, h_item_fp]
      · -- Item passes filter
        refine ⟨item, ?_, h_item_fp⟩
        simp only [Array.mem_append]
        right
        rw [Array.mem_filter]
        exact ⟨h_item_in, by simp [h_in_ctx1_set]⟩
  · intro ⟨item, h_item_in, h_item_fp⟩
    simp only [Array.mem_append] at h_item_in
    simp only [Std.HashSet.mem_union]
    cases h_item_in with
    | inl h_in_ctx1 =>
      left
      exact ctx1.tovisitConsistent h |>.mpr ⟨item, h_in_ctx1, h_item_fp⟩
    | inr h_in_filtered =>
      have h_in_ctx2 : item ∈ ctx2.tovisitQueue := (Array.mem_filter.mp h_in_filtered).1
      right
      exact ctx2.tovisitConsistent h |>.mpr ⟨item, h_in_ctx2, h_item_fp⟩


/-- Helper lemma: membership in foldl-built HashSet (general version with arbitrary init) -/
private theorem mem_foldl_insert_iff_aux {σₕ : Type} [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ]
  (fps : List σₕ) (init : Std.HashSet σₕ) (h : σₕ) :
  h ∈ fps.foldl (fun acc fp => acc.insert fp) init ↔ h ∈ init ∨ h ∈ fps := by
  induction fps generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih]
    rw [Std.HashSet.mem_insert]
    constructor
    · intro h_in
      cases h_in with
      | inl h_in_init =>
        cases h_in_init with
        | inl h_beq => right; left; exact (LawfulBEq.eq_of_beq h_beq).symm
        | inr h_in_init' => left; exact h_in_init'
      | inr h_in_tl => right; right; exact h_in_tl
    · intro h_in
      cases h_in with
      | inl h_in_init => left; right; exact h_in_init
      | inr h_in_list =>
        cases h_in_list with
        | inl h_eq => left; left; rw [h_eq]; exact BEq.refl _
        | inr h_in_tl => right; exact h_in_tl

/-- Helper lemma: membership in foldl-built HashSet starting from empty -/
private theorem mem_foldl_insert_iff {σₕ : Type} [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ]
  (fps : List σₕ) (h : σₕ) :
  h ∈ fps.foldl (fun acc fp => acc.insert fp) Std.HashSet.emptyWithCapacity ↔ h ∈ fps := by
  rw [mem_foldl_insert_iff_aux]
  simp [Std.HashSet.not_mem_emptyWithCapacity]

/-- Helper lemma: foldl over QueueItems equals foldl over mapped fingerprints (general version) -/
private theorem foldl_queueitem_eq_foldl_map_aux {σₕ σ : Type} [BEq σₕ] [Hashable σₕ]
  (items : List (QueueItem σₕ σ)) (init : Std.HashSet σₕ) :
  items.foldl (fun acc item => acc.insert item.fingerprint) init =
  (items.map (·.fingerprint)).foldl (fun acc fp => acc.insert fp) init := by
  induction items generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons]
    exact ih (init.insert hd.fingerprint)

/-- The reduce operation preserves tovisitConsistent for the new tovisitSet built from the queue. -/
theorem reduce_preserves_tovisitConsistent {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th}
  {params : SearchParameters ρ σ}
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (aggregatedCtx : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx) :
  let newTovisitSet := aggregatedCtx.tovisitQueue.foldl (fun acc item => acc.insert item.fingerprint) Std.HashSet.emptyWithCapacity
  ∀ h, h ∈ newTovisitSet ↔ ∃ item ∈ aggregatedCtx.tovisitQueue, item.fingerprint = h := by
  intro newTovisitSet h
  -- Convert to List.foldl
  have h_to_list_foldl : newTovisitSet =
    aggregatedCtx.tovisitQueue.toList.foldl (fun acc item => acc.insert item.fingerprint) Std.HashSet.emptyWithCapacity := by
    simp only [newTovisitSet, Array.foldl_toList]
  -- Then convert to foldl over mapped fingerprints
  have h_to_map_foldl : aggregatedCtx.tovisitQueue.toList.foldl (fun acc item => acc.insert item.fingerprint) Std.HashSet.emptyWithCapacity =
    (aggregatedCtx.tovisitQueue.toList.map (·.fingerprint)).foldl (fun acc fp => acc.insert fp) Std.HashSet.emptyWithCapacity :=
    foldl_queueitem_eq_foldl_map_aux aggregatedCtx.tovisitQueue.toList Std.HashSet.emptyWithCapacity
  have h_array_to_list : newTovisitSet =
    (aggregatedCtx.tovisitQueue.toList.map (·.fingerprint)).foldl (fun acc fp => acc.insert fp) Std.HashSet.emptyWithCapacity := by
    rw [h_to_list_foldl, h_to_map_foldl]
  constructor
  · intro h_in_set
    rw [h_array_to_list] at h_in_set
    have h_in_list := (mem_foldl_insert_iff _ h).mp h_in_set
    simp only [List.mem_map] at h_in_list
    obtain ⟨item, h_item_in_list, h_fp_eq⟩ := h_in_list
    use item
    exact ⟨Array.mem_toList_iff.mp h_item_in_list, h_fp_eq⟩
  · intro ⟨item, h_item_in, h_item_fp⟩
    rw [h_array_to_list]
    apply (mem_foldl_insert_iff _ h).mpr
    simp only [List.mem_map]
    use item
    exact ⟨Array.mem_toList_iff.mpr h_item_in, h_item_fp⟩


/-- Theorem: Inserting a new fingerprint into seen and enqueuing the corresponding state preserves invariants.
    This theorem is used in tryExploreNeighbor when adding a newly discovered neighbor. -/
theorem LocalSearchContext.insert_and_enqueue_preserves_invs {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [instBEq: BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (ctx : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (fingerprint : σₕ)
  (succ : σ)
  (depth : Nat)
  (h_neighbor : sys.reachable succ)
  (h_fp : fingerprint = fp.view succ) :
  @SearchContextInvariants ρ σ κ σₕ fp th sys params
    (Membership.mem (ctx.tovisitQueue.push ⟨fingerprint, succ, depth + 1⟩))
    (fun h => h ∈ ctx.seen ∨ h ∈ ctx.tovisitSet.insert fingerprint) := by
  constructor
  · -- queue_sound: states in queue are reachable
    intro x d h_in_tovisit
    simp only [Array.mem_push] at h_in_tovisit
    cases h_in_tovisit with
    | inl h_old => exact ctx.invs.queue_sound x d h_old
    | inr h_new =>
      simp only [QueueItem.mk.injEq] at h_new
      obtain ⟨_, h_x_eq, _⟩ := h_new
      rw [h_x_eq]
      exact h_neighbor
  · -- visited_sound: states in seen/tovisitSet are reachable
    intro h_view_inj x h_in_new_seen
    simp only [Membership.mem] at h_in_new_seen
    by_cases h : fp.view x = fingerprint
    · have h_x_eq_succ : x = succ := by
        rw [h_fp] at h
        exact h_view_inj h
      rw [h_x_eq_succ]
      exact h_neighbor
    · have h_in_old : fp.view x ∈ ctx.seen ∨ fp.view x ∈ ctx.tovisitSet := by
        cases h_in_new_seen with
        | inl h_seen => left; exact h_seen
        | inr h_in_insert =>
          right
          simp only [Membership.mem]
          have : (ctx.tovisitSet.insert fingerprint).contains (fp.view x) →
                 fp.view x ≠ fingerprint → ctx.tovisitSet.contains (fp.view x) := by
            intro h_contains h_neq
            grind
          exact this h_in_insert h
      exact ctx.invs.visited_sound h_view_inj x h_in_old
  · -- queue_sub_visited: states in queue have fingerprints in seen/tovisitSet
    intro x d h_in_queue
    simp only [Array.mem_push] at h_in_queue
    simp only [Membership.mem]
    cases h_in_queue with
    | inl h_old =>
      have h_sub := ctx.invs.queue_sub_visited x d h_old
      cases h_sub with
      | inl h_seen => left; exact h_seen
      | inr h_tovisitSet => right; exact Std.HashSet.mem_of_mem_insert'' ctx.tovisitSet (fp.view x) fingerprint h_tovisitSet
    | inr h_new =>
      simp only [QueueItem.mk.injEq] at h_new
      obtain ⟨h_fp_eq, _, _⟩ := h_new
      right; rw [h_fp_eq]
      exact Std.HashSet.mem_insert_self' ctx.tovisitSet fingerprint
  · -- queue_wellformed: fingerprints match fp.view
    intro fp' st d h_in_queue
    simp only [Array.mem_push] at h_in_queue
    cases h_in_queue with
    | inl h_old => exact ctx.invs.queue_wellformed fp' st d h_old
    | inr h_new =>
      simp only [QueueItem.mk.injEq] at h_new
      obtain ⟨h_fp'_eq, h_st_eq, _⟩ := h_new
      rw [h_fp'_eq, h_st_eq, h_fp]



-- High-level theorem: updating toBaseSearchContext after processState preserves invariants
-- This is the version for LocalSearchContext (uses Array for tovisitQueue)
theorem LocalSearchContext.update_base_after_processState_preserves_invs {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ] [BEq σ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (ctx : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (fpSt : σₕ)
  (curr : σ)
  (baseCtx' : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (h_process : (ctx.toBaseSearchContext.processState sys fpSt curr).1 = baseCtx') :
  @SearchContextInvariants ρ σ κ σₕ fp th sys params
    (Membership.mem ctx.tovisitQueue)
    (fun h => h ∈ baseCtx'.seen ∨ h ∈ ctx.tovisitSet) := by
  have h_seen_unchanged : baseCtx'.seen = ctx.seen := by
    have h_preserves := BaseSearchContext.processState_preserves_seen sys params fpSt curr ctx.toBaseSearchContext
    rw [h_process] at h_preserves
    exact h_preserves
  constructor
  · intro x d h_in_queue           -- queue_sound: states
    exact ctx.invs.queue_sound x d h_in_queue
  · intro h_view_inj x h_in_seen   -- visited_sound
    rw [h_seen_unchanged] at h_in_seen
    have htmp := ctx.invs.visited_sound h_view_inj x
    exact htmp h_in_seen
  · intro x d h_in_queue          -- queue_sub_visited
    have htmp := ctx.invs.queue_sub_visited x d h_in_queue
    rw [h_seen_unchanged]
    exact htmp
  · intro fp' st d h_in_queue     -- queue_wellformed
    exact ctx.invs.queue_wellformed fp' st d h_in_queue


/-- Reachability is preserved through HashMap.fold with insertIfNew.
    If both m1 and m2 contain only reachable states, so does the result. -/
theorem fold_insertIfNew_preserves_reachability {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (m1 m2 : Std.HashMap σₕ (σ × Nat))
  (h_m1_sound : ∀ x d, m1[fp.view x]? = some (x, d) → sys.reachable x)
  (h_m2_sound : ∀ x d, m2[fp.view x]? = some (x, d) → sys.reachable x) :
  ∀ x d, (m1.fold (init := m2) fun acc k v => acc.insertIfNew k v)[fp.view x]? = some (x, d) →
    sys.reachable x := by
  intro x d h_lookup
  have h_source := Std.HashMap.getElem?_fold_insertIfNew_source m1 m2 (fp.view x) (x, d) h_lookup
  cases h_source with
  | inl h_from_m2 => exact h_m2_sound x d h_from_m2
  | inr h_from_m1 => exact h_m1_sound x d h_from_m1.1


/-- Theorem for processSuccessors recursive step: combines neighbor and rest results -/
theorem processSuccessors_cons_step {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (ctx neighbor_ctx rest_ctx : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (label : κ) (state : σ) (rest : List (κ × σ))
  -- Properties from neighbor result (tryExploreNeighbor)
  (h_neighbor_tovisitSet_mono : ∀ fp_elem, fp_elem ∈ ctx.tovisitSet → fp_elem ∈ neighbor_ctx.tovisitSet)
  (h_current_in_seen : neighbor_ctx.seen.contains (fp.view state) ∨ neighbor_ctx.tovisitSet.contains (fp.view state))
  -- Properties from rest result (recursive processSuccessors)
  (h_rest_complete : ∀ (l : κ) (v : σ), (l, v) ∈ rest → (fp.view v) ∈ rest_ctx.seen ∨ (fp.view v) ∈ rest_ctx.tovisitSet)
  (h_rest_tovisitSet_mono : ∀ fp_elem, fp_elem ∈ neighbor_ctx.tovisitSet → fp_elem ∈ rest_ctx.tovisitSet) :
  -- Result: combined properties for (label, state) :: rest
  (∀ (l : κ) (v : σ), (l, v) ∈ (label, state) :: rest → (fp.view v) ∈ rest_ctx.seen ∨ (fp.view v) ∈ rest_ctx.tovisitSet) ∧
  (∀ fp_elem, fp_elem ∈ ctx.tovisitSet → fp_elem ∈ rest_ctx.tovisitSet) := by
  constructor
  · intro l v h_in_cons
    cases h_in_cons with
    | head =>
      simp at *
      cases h_current_in_seen with
      | inl h_in_seen =>
        -- seen is stable via seenUnaltered
        left
        have h1 : fp.view state ∈ baseCtx.seen := (neighbor_ctx.seenUnaltered (fp.view state)).mpr h_in_seen
        exact (rest_ctx.seenUnaltered (fp.view state)).mp h1
      | inr h_in_tovisitSet => right; exact h_rest_tovisitSet_mono (fp.view state) h_in_tovisitSet
    | tail _ h_in_rest => exact h_rest_complete l v h_in_rest
  · intro fp_elem h_in_ctx
    have h1 : fp_elem ∈ neighbor_ctx.tovisitSet := h_neighbor_tovisitSet_mono fp_elem h_in_ctx
    exact h_rest_tovisitSet_mono fp_elem h1


/-- Theorem for processState: combines processSuccessors result with ctx_updated -/
theorem processState_some_step {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (ctx res_ctx : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (curr : σ)
  -- ctx_updated has same tovisitSet as ctx
  (h_tovisitSet_eq : res_ctx.tovisitSet = ctx.tovisitSet ∨
                    ∃ ctx_updated : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx,
                      ctx_updated.tovisitSet = ctx.tovisitSet ∧
                      (∀ fp_elem, fp_elem ∈ ctx_updated.tovisitSet → fp_elem ∈ res_ctx.tovisitSet))
  -- Completeness from processSuccessors
  (h_res_complete : ∀ (l : κ) (v : σ), (l, v) ∈ extractSuccessfulTransitions (sys.tr th curr) →
                    (fp.view v) ∈ res_ctx.seen ∨ (fp.view v) ∈ res_ctx.tovisitSet) :
  -- Result: properties for processState
  (∀ x, x ∈ ctx.tovisitSet → x ∈ res_ctx.tovisitSet) ∧
  (!res_ctx.hasFinished → ∀ l v, (l, v) ∈ extractSuccessfulTransitions (sys.tr th curr) →
    (fp.view v) ∈ res_ctx.seen ∨ (fp.view v) ∈ res_ctx.tovisitSet) := by
  constructor
  · intro x h_in_ctx
    cases h_tovisitSet_eq with
    | inl h_eq => rw [h_eq]; exact h_in_ctx
    | inr h_exists =>
      obtain ⟨ctx_updated, h_updated_eq, h_mono⟩ := h_exists
      rw [← h_updated_eq] at h_in_ctx
      exact h_mono x h_in_ctx
  · intro _ l v h_in_extracted
    exact h_res_complete l v h_in_extracted


/-- Theorem for processWorkQueue recursive step: combines processState and recursive results -/
theorem processWorkQueue_cons_step {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (ctx next_ctx rest_ctx : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (fpSt : σₕ) (curr : σ) (depth : Nat) (rest : List (σₕ × σ × Nat))
  (h_next_not_finished : !next_ctx.hasFinished)
  -- Properties from processState
  (h_next_mono : ∀ x, x ∈ ctx.tovisitSet → x ∈ next_ctx.tovisitSet)
  (h_next_complete : !next_ctx.hasFinished → ∀ l v, (l, v) ∈ extractSuccessfulTransitions (sys.tr th curr) →
                     (fp.view v) ∈ next_ctx.seen ∨ (fp.view v) ∈ next_ctx.tovisitSet)
  -- Properties from recursive processWorkQueue (using SuccessorsCollected)
  (h_rest_complete : SuccessorsCollected sys (fun ⟨h, st, d⟩ => (h, st, d) ∈ rest) rest_ctx.hasFinished (fun h => h ∈ rest_ctx.seen ∨ h ∈ rest_ctx.tovisitSet))
  (h_rest_mono : ∀ fp_elem, fp_elem ∈ next_ctx.tovisitSet → fp_elem ∈ rest_ctx.tovisitSet) :
  -- Result: combined properties for (fpSt, curr, depth) :: rest using SuccessorsCollected
  SuccessorsCollected sys (fun ⟨h, st, d⟩ => (h, st, d) ∈ (fpSt, curr, depth) :: rest) rest_ctx.hasFinished (fun h => h ∈ rest_ctx.seen ∨ h ∈ rest_ctx.tovisitSet) ∧
  (∀ fp_elem, fp_elem ∈ ctx.tovisitSet → fp_elem ∈ rest_ctx.tovisitSet)
   := by
  constructor
  · -- Prove SuccessorsCollected for the cons case
    intro h_final_nf fingerprint st d h_in_cons l v h_tr
    -- Simplify the match expression in h_in_cons
    simp only at h_in_cons
    -- Now h_in_cons should be: (fingerprint, st, d) ∈ (fpSt, curr, depth) :: rest
    -- Case analysis on whether the item is the head or in the tail
    by_cases h_eq : (fingerprint, st, d) = (fpSt, curr, depth)
    · -- Case: (fingerprint, st, d) = (fpSt, curr, depth)
      cases h_eq
      -- Now st = curr, so we need to show successors of curr are in seen
      have h_in_extracted : (l, v) ∈ extractSuccessfulTransitions (sys.tr th curr) := by
        unfold extractSuccessfulTransitions
        simp only [List.mem_filterMap]
        exact ⟨(l, .success v), h_tr, rfl⟩
      have h_head_processed := h_next_complete h_next_not_finished l v h_in_extracted
      cases h_head_processed with
      | inl h_seen =>
        left
        have h1 : fp.view v ∈ baseCtx.seen := (next_ctx.seenUnaltered (fp.view v)).mpr h_seen
        exact (rest_ctx.seenUnaltered (fp.view v)).mp h1
      | inr h_local => right; exact h_rest_mono _ h_local
    · -- Case: (fingerprint, st, d) ≠ (fpSt, curr, depth), so it must be in rest
      have h_in_rest : (fingerprint, st, d) ∈ rest := by
        rw [List.mem_cons] at h_in_cons
        cases h_in_cons with
        | inl h_head => exact absurd h_head h_eq
        | inr h_tail => exact h_tail
      exact h_rest_complete h_final_nf fingerprint st d h_in_rest l v h_tr
  · intro x hx
    apply h_rest_mono
    apply h_next_mono
    exact hx

/-- Theorem for preserving SearchContextInvariants when seen is unchanged.
    Used in processState none branch where tovisit and tovisitSet stay the same. -/
theorem SearchContextInvariants.preserved_when_seen_unchanged {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (tovisitQueue : Array (QueueItem σₕ σ))
  (old_seen new_seen : Std.HashSet σₕ)
  (tovisitSet : Std.HashSet σₕ)
  (h_seen_unchanged : new_seen = old_seen)
  (h_old_invs : @SearchContextInvariants ρ σ κ σₕ fp th sys params
    (Membership.mem tovisitQueue)
    (fun h => h ∈ old_seen ∨ h ∈ tovisitSet)) :
  @SearchContextInvariants ρ σ κ σₕ fp th sys params
    (Membership.mem tovisitQueue)
    (fun h => h ∈ new_seen ∨ h ∈ tovisitSet) := by
  constructor
  · exact h_old_invs.queue_sound
  · intro h_view_inj x h_in_seen
    rw [h_seen_unchanged] at h_in_seen
    exact h_old_invs.visited_sound h_view_inj x h_in_seen
  · intro x d h_in_queue
    have h_old := h_old_invs.queue_sub_visited x d h_in_queue
    rw [h_seen_unchanged]
    exact h_old
  · exact h_old_invs.queue_wellformed

/-- Theorem for processState none branch: when early termination occurs (hasFinished = true),
    the subtype properties are trivially satisfied -/
theorem processState_none_subtype {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (ctx ctx' : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (curr : σ)
  (h_tovisitSet_eq : ctx'.tovisitSet = ctx.tovisitSet)
  (h_finished : ctx'.hasFinished) :
  (∀ x, x ∈ ctx.tovisitSet → x ∈ ctx'.tovisitSet) ∧
  (!ctx'.hasFinished → ∀ l v, (l, v) ∈ extractSuccessfulTransitions (sys.tr th curr) →
    (fp.view v) ∈ ctx'.seen ∨ (fp.view v) ∈ ctx'.tovisitSet) :=
  ⟨fun x h => h_tovisitSet_eq ▸ h, fun h_nf => by simp_all⟩



theorem ParallelSearchContext.merge_preserves_frontier_closed {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ]
  {th : ρ} (sys : _) (params : SearchParameters ρ σ)
  (ctx : @ParallelSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (unionSeen : Std.HashSet σₕ)
  (currTovisitSet : Std.HashSet σₕ)
  (h_not_finished : ctx.finished = none)
  (h_view_inj : Function.Injective fp.view)
  -----------------------------------------------------------------------------
  (h_delta_consistent : Function.Injective fp.view →
    ∀ x, (fp.view x) ∈ unionSeen → fp.view x ∈ currTovisitSet)
  -----------------------------------------------------------------------------
  (h_collect_all : ∀ (s : σ),
    fp.view s ∈ ctx.tovisitSet →
      (∀l v, (l, .success v) ∈ (sys.tr th s)
        → ((fp.view v) ∈ ctx.seen ∨ (fp.view v) ∈ unionSeen)))
  -----------------------------------------------------------------------------
  : ∀ (s : σ), fp.view s ∈ (ctx.seen.union unionSeen) →      -- s is discovered
      (fp.view s ∉ currTovisitSet) →          -- s is not in the frontier
      ∀ l next_s, (l, .success next_s) ∈ sys.tr th s →    -- for all successors
        fp.view next_s ∈ ctx.seen.union unionSeen
  -----------------------------------------------------------------------------
  := by
  intro s h_in_new_seen h_not_in_new_tovisit l next_s h_tr
  rw [Std.HashSet.mem_union] at h_in_new_seen
  rcases h_in_new_seen with h_in_old_seen | h_in_new_added
  · -- Check if s is in the old tovisit set
    by_cases h_in_old_queue : fp.view s ∈ ctx.tovisitSet
    · -- Subcase B.1 (Case 2): (`s ∈ Q_old`) h_collect_all
      have h_all_succ := h_collect_all s h_in_old_queue
      have h_succ_in_union : fp.view next_s ∈ ctx.seen ∨ fp.view next_s ∈ unionSeen :=
        h_all_succ l next_s h_tr
      rw [Std.HashSet.mem_union]
      exact h_succ_in_union
    · -- Subcase B.2 (Case 1): (`s ∉ Q_old`)
      have h_old_invariant := ctx.frontier_closed h_view_inj (by
        right; exact h_not_finished
      ) s h_in_old_seen h_in_old_queue l next_s h_tr
      rw [Std.HashSet.mem_union]
      left; exact h_old_invariant
  -- Case A (Case 3): (`s ∈ unionSeen`) --h_delta_consistent
  · have h_must_be_in_queue := h_delta_consistent h_view_inj s h_in_new_added
    exact absurd h_must_be_in_queue h_not_in_new_tovisit

/-- Items in an extracted subarray are reachable if items in the original array are reachable -/
theorem Array_extract_items_reachable {σₕ σ : Type}
  [_fp : StateFingerprint σ σₕ]
  {ρ κ : Type}
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (tovisitArr : Array (σₕ × σ × Nat))
  (h_arr_reachable : ∀ item ∈ tovisitArr.toList, sys.reachable item.2.1) :
  ∀ (lr : Nat × Nat), ∀ item ∈ (tovisitArr.extract lr.1 lr.2).toList,
    sys.reachable item.2.1 := by
  intro lr item h_mem
  have h_in_original : item ∈ tovisitArr.toList := by
    rw [Array.mem_toList_iff] at h_mem ⊢
    exact Array.mem_of_mem_extract tovisitArr lr.1 lr.2 item (by grind)
  exact h_arr_reachable item h_in_original

/-- All items in split arrays (obtained by mapping extract over ranges) are reachable -/
theorem splitArrays_items_reachable {σₕ σ : Type}
  [_fp : StateFingerprint σ σₕ]
  {ρ κ : Type}
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (tovisitArr : Array (σₕ × σ × Nat))
  (ranges : List (Nat × Nat))
  (splitArrays : List (Array (σₕ × σ × Nat)))
  (h_split_def : splitArrays = ranges.map (fun lr => tovisitArr.extract lr.1 lr.2))
  (h_extract_reachable : ∀ (lr : Nat × Nat), ∀ item ∈ (tovisitArr.extract lr.1 lr.2).toList,
    sys.reachable item.2.1) :
  ∀ subArr ∈ splitArrays, ∀ item ∈ subArr.toList, sys.reachable item.2.1 := by
  intro subArr h_subArr_in item h_item_in
  rw [h_split_def] at h_subArr_in
  obtain ⟨lr, _, h_subArr_eq⟩ := List.mem_map.mp h_subArr_in
  rw [← h_subArr_eq] at h_item_in
  exact h_extract_reachable lr item h_item_in

/-- All items in tovisitQueue are reachable if the queue satisfies queue_sound (QueueItem version) -/
theorem tovisitQueue_items_reachable {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (ctx : @ParallelSearchContext ρ σ κ σₕ fp _ _ th sys params) :
  ∀ item ∈ ctx.tovisitQueue.toList, sys.reachable item.state := by
  intro ⟨h, x, d⟩ h_mem
  have h_in_queue : (⟨h, x, d⟩ : QueueItem σₕ σ) ∈ ctx.tovisitQueue := Array.mem_toList_iff.mp h_mem
  have h_wf : h = fp.view x := ctx.invs.queue_wellformed h x d h_in_queue
  rw [h_wf] at h_in_queue
  exact ctx.invs.queue_sound x d h_in_queue

/-- Items in an extracted subarray are reachable if items in the original array are reachable (QueueItem version) -/
theorem Array_extract_items_reachable_QueueItem {σₕ σ : Type}
  [_fp : StateFingerprint σ σₕ]
  {ρ κ : Type}
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (tovisitArr : Array (QueueItem σₕ σ))
  (h_arr_reachable : ∀ item ∈ tovisitArr.toList, sys.reachable item.state) :
  ∀ (lr : Nat × Nat), ∀ item ∈ ((tovisitArr.extract lr.1 lr.2).map (fun item => (item.fingerprint, item.state, item.depth))).toList,
    sys.reachable item.2.1 := by
  intro lr ⟨h, x, d⟩ h_mem
  rw [Array.mem_toList_iff] at h_mem
  simp only [Array.mem_map] at h_mem
  obtain ⟨item, h_item_in_extract, h_item_eq⟩ := h_mem
  have h_in_original : item ∈ tovisitArr.toList := by
    rw [Array.mem_toList_iff]
    exact Array.mem_of_mem_extract tovisitArr lr.1 lr.2 item h_item_in_extract
  have h_reachable := h_arr_reachable item h_in_original
  simp only [Prod.mk.injEq] at h_item_eq
  rw [← h_item_eq.2.1]
  exact h_reachable

/-- All items in split arrays (obtained by mapping extract and converting to tuples) are reachable (QueueItem version) -/
theorem splitArrays_items_reachable_QueueItem {σₕ σ : Type}
  [_fp : StateFingerprint σ σₕ]
  {ρ κ : Type}
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (tovisitArr : Array (QueueItem σₕ σ))
  (ranges : List (Nat × Nat))
  (splitArrays : List (Array (σₕ × σ × Nat)))
  (h_split_def : splitArrays = ranges.map (fun lr => (tovisitArr.extract lr.1 lr.2).map (fun item => (item.fingerprint, item.state, item.depth))))
  (h_extract_reachable : ∀ (lr : Nat × Nat), ∀ item ∈ ((tovisitArr.extract lr.1 lr.2).map (fun item => (item.fingerprint, item.state, item.depth))).toList,
    sys.reachable item.2.1) :
  ∀ subArr ∈ splitArrays, ∀ item ∈ subArr.toList, sys.reachable item.2.1 := by
  intro subArr h_subArr_in item h_item_in
  rw [h_split_def] at h_subArr_in
  obtain ⟨lr, _, h_subArr_eq⟩ := List.mem_map.mp h_subArr_in
  rw [← h_subArr_eq] at h_item_in
  exact h_extract_reachable lr item h_item_in

/-- Invariants are preserved when merging two LocalSearchContext instances.
    The merged context uses filtered Array concatenation for tovisitQueue and unions for seen/tovisitSet. -/
theorem merge_local_local_preserves_invs {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (ctx1 ctx2 : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx) :
  let filteredQueue := ctx2.tovisitQueue.filter fun item => !ctx1.tovisitSet.contains item.fingerprint
  @SearchContextInvariants ρ σ κ σₕ fp th sys params
    (Membership.mem (ctx1.tovisitQueue ++ filteredQueue))
    (fun h => h ∈ ctx1.seen.union ctx2.seen ∨ h ∈ ctx1.tovisitSet.union ctx2.tovisitSet) := by
  intro filteredQueue
  constructor
  · -- queue_sound: states in merged tovisit are reachable
    intro x d h_in_merged
    rw [Array.mem_append] at h_in_merged
    cases h_in_merged with
    | inl h_in_ctx1 => exact ctx1.invs.queue_sound x d h_in_ctx1
    | inr h_in_filtered =>
      have h_in_ctx2 : ⟨fp.view x, x, d⟩ ∈ ctx2.tovisitQueue := by
        have := Array.mem_filter.mp h_in_filtered
        exact this.1
      exact ctx2.invs.queue_sound x d h_in_ctx2
  · -- visited_sound: elements in merged seen/tovisitSet are reachable
    intro h_inj x h_in_union
    simp only [Std.HashSet.mem_union] at h_in_union
    rcases h_in_union with (h1 | h2) | (h3 | h4)
    · exact ctx1.invs.visited_sound h_inj x (Or.inl h1)
    · exact ctx2.invs.visited_sound h_inj x (Or.inl h2)
    · exact ctx1.invs.visited_sound h_inj x (Or.inr h3)
    · exact ctx2.invs.visited_sound h_inj x (Or.inr h4)
  · -- queue_sub_visited: elements in merged tovisit have fingerprints in merged seen/tovisitSet
    intro x d h_in_merged
    rw [Array.mem_append] at h_in_merged
    simp only [Std.HashSet.mem_union]
    cases h_in_merged with
    | inl h_in_ctx1 =>
      rcases ctx1.invs.queue_sub_visited x d h_in_ctx1 with h_seen | h_tovisitSet
      · exact Or.inl (Or.inl h_seen)
      · exact Or.inr (Or.inl h_tovisitSet)
    | inr h_in_filtered =>
      have h_in_ctx2 : ⟨fp.view x, x, d⟩ ∈ ctx2.tovisitQueue := by
        have := Array.mem_filter.mp h_in_filtered
        exact this.1
      rcases ctx2.invs.queue_sub_visited x d h_in_ctx2 with h_seen | h_tovisitSet
      · exact Or.inl (Or.inr h_seen)
      · exact Or.inr (Or.inr h_tovisitSet)
  · -- queue_wellformed: fingerprints match states in merged tovisit
    intro k x d h_in_merged
    rw [Array.mem_append] at h_in_merged
    cases h_in_merged with
    | inl h_in_ctx1 => exact ctx1.invs.queue_wellformed k x d h_in_ctx1
    | inr h_in_filtered =>
      have h_in_ctx2 : ⟨k, x, d⟩ ∈ ctx2.tovisitQueue := by
        have := Array.mem_filter.mp h_in_filtered
        exact this.1
      exact ctx2.invs.queue_wellformed k x d h_in_ctx2

/-- When merging two LocalSearchContext instances with Option.or,
    if the result is exploredAllReachableStates, one of the contexts must have had it. -/
theorem merge_local_local_excludes_exploredAll {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (ctx1 ctx2 : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (h_eq : Option.or ctx1.finished ctx2.finished = some .exploredAllReachableStates) :
  False := by
  unfold Option.or at h_eq
  cases h_ctx1 : ctx1.finished with
  | none     => simp [h_ctx1] at h_eq; exact ctx2.excludeAllStatesFinish h_eq
  | some val => simp [h_ctx1] at h_eq; subst h_eq; exact ctx1.excludeAllStatesFinish h_ctx1

/-- The seen set of merged LocalSearchContext is the union of both seen sets,
    which equals the union of both baseCtx.seen (via seenUnaltered). -/
theorem merge_local_local_preserves_seenUnaltered {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (ctx1 ctx2 : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (s : σₕ) :
  s ∈ baseCtx.seen ↔ s ∈ ctx1.seen.union ctx2.seen := by
  rw [Std.HashSet.mem_union, ←ctx1.seenUnaltered s, ←ctx2.seenUnaltered s]
  simp

/-- Invariants are preserved when merging a ParallelSearchContext with a LocalSearchContext's results.
    The new context uses aggregatedCtx's tovisitQueue and merges ctx.seen with aggregatedCtx.tovisitSet. -/
theorem merge_parallel_local_preserves_invs {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (ctx : @ParallelSearchContext ρ σ κ σₕ fp _ _ th sys params)
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (aggregatedCtx : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (h_base_eq : baseCtx.seen = ctx.seen) :
  @SearchContextInvariants ρ σ κ σₕ fp th sys params
    (Membership.mem aggregatedCtx.tovisitQueue)
    (fun h => h ∈ ctx.seen.union aggregatedCtx.tovisitSet) := by
  constructor
  · -- queue_sound
    intro x d h_in_tovisit
    exact aggregatedCtx.invs.queue_sound x d h_in_tovisit
  · -- visited_sound
    intro h_view_inj x h_in_new_seen
    simp only [Std.HashSet.mem_union] at h_in_new_seen
    rcases h_in_new_seen with h_in_ctx_seen | h_in_tovisitSet
    · exact ctx.invs.visited_sound h_view_inj x h_in_ctx_seen
    · exact aggregatedCtx.invs.visited_sound h_view_inj x (Or.inr h_in_tovisitSet)
  · -- queue_sub_visited
    intro x d h_in_tovisit
    have h_sub := aggregatedCtx.invs.queue_sub_visited x d h_in_tovisit
    simp only [Std.HashSet.mem_union]
    rcases h_sub with h_in_agg_seen | h_in_tovisitSet
    · have h_eq := aggregatedCtx.seenUnaltered (fp.view x)
      rw [h_base_eq] at h_eq
      exact Or.inl (h_eq.mpr h_in_agg_seen)
    · exact Or.inr h_in_tovisitSet
  · -- queue_wellformed
    intro fingerprint st d h_in_tovisit
    exact aggregatedCtx.invs.queue_wellformed fingerprint st d h_in_tovisit

end Veil.ModelChecker.Concrete
