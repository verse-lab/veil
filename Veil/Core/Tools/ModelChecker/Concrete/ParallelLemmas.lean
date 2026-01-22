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


/-- Theorem: Inserting a new fingerprint into localSeen and enqueuing the corresponding state preserves deltaConsistent.
    This theorem is used in tryExploreNeighbor when adding a newly discovered neighbor. -/
theorem LocalSearchContext.insert_and_enqueue_preserves_deltaConsistent {ρ σ κ σₕ : Type}
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
  (h_fp : fingerprint = fp.view succ) :
  Function.Injective fp.view →
  ∀x, (fp.view x) ∈ ctx.localSeen.insert fingerprint →
  ∃d, (ctx.tovisit.insert fingerprint ⟨succ, depth + 1⟩)[fp.view x]? = some (x, d) := by
  have h_old := ctx.deltaConsistent
  intro h_inj x h_in_localSeen
  by_cases h_eq : fp.view x = fingerprint
  · have h_x_eq_succ : x = succ := h_inj (by rw [h_eq, h_fp])
    use depth + 1
    rw [h_x_eq_succ, Std.HashMap.getElem?_insert]
    simp
    grind
  · have h_in_old_localSeen : fp.view x ∈ ctx.localSeen := by
      simp only [Std.HashSet.mem_insert] at h_in_localSeen
      cases h_in_localSeen with
      | inl h => grind
      | inr h => exact h
    obtain ⟨d, h_in_tovisit⟩ := h_old h_inj x h_in_old_localSeen
    use d
    rw [Std.HashMap.getElem?_insert]
    grind


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
    ((fun ⟨h, x, d⟩ => (ctx.tovisit.insert fingerprint ⟨succ, depth + 1⟩)[h]? = some (x, d)))
    (fun h => h ∈ ctx.seen ∨ h ∈ ctx.localSeen.insert fingerprint) := by
  constructor
  · intro x d h_in_tovisit
    simp only at h_in_tovisit
    rw [Std.HashMap.getElem?_insert] at h_in_tovisit
    split at h_in_tovisit
    · next h_beq =>
        cases h_in_tovisit
        exact h_neighbor
    · exact ctx.invs.queue_sound x d h_in_tovisit
  · intro h_view_inj x h_in_new_seen
    simp only [Membership.mem] at h_in_new_seen
    by_cases h : fp.view x = fingerprint
    · have h_x_eq_succ : x = succ := by
        rw [h_fp] at h
        exact h_view_inj h
      rw [h_x_eq_succ]
      exact h_neighbor
    · have h_in_old : fp.view x ∈ ctx.seen ∨ fp.view x ∈ ctx.localSeen := by
        cases h_in_new_seen with
        | inl h_seen => left; exact h_seen
        | inr h_in_insert =>
          right
          simp only [Membership.mem]
          have : (ctx.localSeen.insert fingerprint).contains (fp.view x) →
                 fp.view x ≠ fingerprint → ctx.localSeen.contains (fp.view x) := by
            intro h_contains h_neq
            grind
          exact this h_in_insert h
      exact ctx.invs.visited_sound h_view_inj x h_in_old
  · intro x d h_in_queue
    simp only at h_in_queue
    rw [Std.HashMap.getElem?_insert] at h_in_queue
    split at h_in_queue
    · next h_beq =>
      have h_fp_eq : fingerprint = fp.view x := LawfulBEq.eq_of_beq h_beq
      simp only [Membership.mem]
      right; rw [← h_fp_eq]
      exact Std.HashSet.mem_insert_self' ctx.localSeen fingerprint
    · have h_in_old_seen := ctx.invs.queue_sub_visited x d h_in_queue
      simp only [Membership.mem]
      cases h_in_old_seen with
      | inl h_seen => left; exact h_seen
      | inr h_localSeen => right; exact Std.HashSet.mem_of_mem_insert'' ctx.localSeen (fp.view x) fingerprint h_localSeen
  · intro fp' st d h_in_queue
    simp only at h_in_queue
    rw [Std.HashMap.getElem?_insert] at h_in_queue
    split at h_in_queue
    · next h_beq =>
      have h_fp'_eq : fingerprint = fp' := LawfulBEq.eq_of_beq h_beq
      cases h_in_queue
      rw [← h_fp'_eq, h_fp]
    · exact ctx.invs.queue_wellformed fp' st d h_in_queue



-- High-level theorem: updating toBaseSearchContext after processState preserves invariants
-- This is the version for LocalSearchContext (uses HashMap for tovisit)
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
    (fun ⟨h, x, d⟩ => ctx.tovisit[h]? = some (x, d))
    (fun h => h ∈ baseCtx'.seen ∨ h ∈ ctx.localSeen) := by
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


/- Combined lemma for deltaConsistent: when key is in localSeen (from either ctx),
    and both tovisit maps satisfy queue_wellformed, the result tovisit has (x, d) for some d.
    Uses insertIfNew semantics: m2 values take precedence over m1. -/
theorem getElem?_fold_insertIfNew_deltaConsistent {σₕ σ : Type}
  [fp : StateFingerprint σ σₕ]
  (m1 m2 : Std.HashMap σₕ (σ × Nat)) (x : σ)
  (h_m2_wellformed : ∀ k x' d, m2[k]? = some (x', d) → k = fp.view x')
  (h_inj : Function.Injective fp.view)
  (h_exists : (∃ d, m1[fp.view x]? = some (x, d)) ∨ (∃ d, m2[fp.view x]? = some (x, d))) :
  ∃ d', (m1.fold (init := m2) fun acc k' v' => acc.insertIfNew k' v')[fp.view x]? = some (x, d') := by
  rcases h_exists with ⟨d1, h_in_m1⟩ | ⟨d2, h_in_m2⟩
  · -- Case: entry is in m1
    by_cases h_key_in_m2 : (fp.view x) ∈ m2
    · have h_m2_some : (m2[fp.view x]?).isSome := by grind
      obtain ⟨⟨x', d'⟩, h_m2_lookup⟩ := Option.isSome_iff_exists.mp h_m2_some
      have h_wf := h_m2_wellformed (fp.view x) x' d' h_m2_lookup
      have h_eq : x = x' := h_inj h_wf
      subst h_eq
      use d'
      exact Std.HashMap.getElem?_fold_insertIfNew_preserves_m2 m1 m2 (fp.view x) (x, d') h_m2_lookup
    · use d1
      exact Std.HashMap.getElem?_fold_insertIfNew_from_m1 m1 m2 (fp.view x) (x, d1) h_in_m1 h_key_in_m2
  · use d2
    exact Std.HashMap.getElem?_fold_insertIfNew_preserves_m2 m1 m2 (fp.view x) (x, d2) h_in_m2



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
  (h_neighbor_localSeen_mono : ∀ fp_elem, fp_elem ∈ ctx.localSeen → fp_elem ∈ neighbor_ctx.localSeen)
  (h_current_in_seen : neighbor_ctx.seen.contains (fp.view state) ∨ neighbor_ctx.localSeen.contains (fp.view state))
  -- Properties from rest result (recursive processSuccessors)
  (h_rest_complete : ∀ (l : κ) (v : σ), (l, v) ∈ rest → (fp.view v) ∈ rest_ctx.seen ∨ (fp.view v) ∈ rest_ctx.localSeen)
  (h_rest_localSeen_mono : ∀ fp_elem, fp_elem ∈ neighbor_ctx.localSeen → fp_elem ∈ rest_ctx.localSeen) :
  -- Result: combined properties for (label, state) :: rest
  (∀ (l : κ) (v : σ), (l, v) ∈ (label, state) :: rest → (fp.view v) ∈ rest_ctx.seen ∨ (fp.view v) ∈ rest_ctx.localSeen) ∧
  (∀ fp_elem, fp_elem ∈ ctx.localSeen → fp_elem ∈ rest_ctx.localSeen) := by
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
      | inr h_in_localSeen => right; exact h_rest_localSeen_mono (fp.view state) h_in_localSeen
    | tail _ h_in_rest => exact h_rest_complete l v h_in_rest
  · intro fp_elem h_in_ctx
    have h1 : fp_elem ∈ neighbor_ctx.localSeen := h_neighbor_localSeen_mono fp_elem h_in_ctx
    exact h_rest_localSeen_mono fp_elem h1


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
  -- ctx_updated has same localSeen as ctx
  (h_localSeen_eq : res_ctx.localSeen = ctx.localSeen ∨
                    ∃ ctx_updated : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx,
                      ctx_updated.localSeen = ctx.localSeen ∧
                      (∀ fp_elem, fp_elem ∈ ctx_updated.localSeen → fp_elem ∈ res_ctx.localSeen))
  -- Completeness from processSuccessors
  (h_res_complete : ∀ (l : κ) (v : σ), (l, v) ∈ extractSuccessfulTransitions (sys.tr th curr) →
                    (fp.view v) ∈ res_ctx.seen ∨ (fp.view v) ∈ res_ctx.localSeen) :
  -- Result: properties for processState
  (∀ x, x ∈ ctx.localSeen → x ∈ res_ctx.localSeen) ∧
  (!res_ctx.hasFinished → ∀ l v, (l, v) ∈ extractSuccessfulTransitions (sys.tr th curr) →
    (fp.view v) ∈ res_ctx.seen ∨ (fp.view v) ∈ res_ctx.localSeen) := by
  constructor
  · intro x h_in_ctx
    cases h_localSeen_eq with
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
  (h_next_mono : ∀ x, x ∈ ctx.localSeen → x ∈ next_ctx.localSeen)
  (h_next_complete : !next_ctx.hasFinished → ∀ l v, (l, v) ∈ extractSuccessfulTransitions (sys.tr th curr) →
                     (fp.view v) ∈ next_ctx.seen ∨ (fp.view v) ∈ next_ctx.localSeen)
  -- Properties from recursive processWorkQueue (using SuccessorsCollected)
  (h_rest_complete : SuccessorsCollected sys (fun ⟨h, st, d⟩ => (h, st, d) ∈ rest) rest_ctx.hasFinished (fun h => h ∈ rest_ctx.seen ∨ h ∈ rest_ctx.localSeen))
  (h_rest_mono : ∀ fp_elem, fp_elem ∈ next_ctx.localSeen → fp_elem ∈ rest_ctx.localSeen) :
  -- Result: combined properties for (fpSt, curr, depth) :: rest using SuccessorsCollected
  SuccessorsCollected sys (fun ⟨h, st, d⟩ => (h, st, d) ∈ (fpSt, curr, depth) :: rest) rest_ctx.hasFinished (fun h => h ∈ rest_ctx.seen ∨ h ∈ rest_ctx.localSeen) ∧
  (∀ fp_elem, fp_elem ∈ ctx.localSeen → fp_elem ∈ rest_ctx.localSeen)
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
    Used in processState none branch where tovisit and localSeen stay the same. -/
theorem SearchContextInvariants.preserved_when_seen_unchanged {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (tovisit : Std.HashMap σₕ (σ × Nat))
  (old_seen new_seen : Std.HashSet σₕ)
  (localSeen : Std.HashSet σₕ)
  (h_seen_unchanged : new_seen = old_seen)
  (h_old_invs : @SearchContextInvariants ρ σ κ σₕ fp th sys params
    (fun ⟨h, x, d⟩ => tovisit[h]? = some (x, d))
    (fun h => h ∈ old_seen ∨ h ∈ localSeen)) :
  @SearchContextInvariants ρ σ κ σₕ fp th sys params
    (fun ⟨h, x, d⟩ => tovisit[h]? = some (x, d))
    (fun h => h ∈ new_seen ∨ h ∈ localSeen) := by
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
  (h_localSeen_eq : ctx'.localSeen = ctx.localSeen)
  (h_finished : ctx'.hasFinished) :
  (∀ x, x ∈ ctx.localSeen → x ∈ ctx'.localSeen) ∧
  (!ctx'.hasFinished → ∀ l v, (l, v) ∈ extractSuccessfulTransitions (sys.tr th curr) →
    (fp.view v) ∈ ctx'.seen ∨ (fp.view v) ∈ ctx'.localSeen) :=
  ⟨fun x h => h_localSeen_eq ▸ h, fun h_nf => by simp_all⟩



theorem ParallelSearchContext.merge_preserves_frontier_closed {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ]
  {th : ρ} (sys : _) (params : SearchParameters ρ σ)
  (ctx : @ParallelSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (unionSeen : Std.HashSet σₕ)
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

/-- All items in a HashMap's toArray are reachable if the HashMap satisfies queue_sound -/
theorem HashMap_toArray_items_reachable {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (ctx : @ParallelSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (tovisitArr : Array (σₕ × σ × Nat))
  (h_arr_eq : tovisitArr = ctx.tovisit.toArray) :
  ∀ item ∈ tovisitArr.toList, sys.reachable item.2.1 := by
  intro ⟨h, x, d⟩ h_mem
  have h_in_arr : (h, (x, d)) ∈ ctx.tovisit.toArray := by
    rw [← h_arr_eq]; exact Array.mem_toList_iff.mp h_mem
  have h_lookup : ctx.tovisit[h]? = some (x, d) :=
    Std.HashMap.getElem?_of_mem_toArray ctx.tovisit h (x, d) h_in_arr
  have h_wf : h = fp.view x := ctx.invs.queue_wellformed h x d h_lookup
  rw [h_wf] at h_lookup
  exact ctx.invs.queue_sound x d h_lookup

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

/-- Invariants are preserved when merging two LocalSearchContext instances.
    The merged context uses fold insertIfNew for tovisit and unions for seen/localSeen. -/
theorem merge_local_local_preserves_invs {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (ctx1 ctx2 : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx) :
  @SearchContextInvariants ρ σ κ σₕ fp th sys params
    (fun ⟨h, x, d⟩ => (ctx1.tovisit.fold (init := ctx2.tovisit) fun acc k v => acc.insertIfNew k v)[h]? = some (x, d))
    (fun h => h ∈ ctx1.seen.union ctx2.seen ∨ h ∈ ctx1.localSeen.union ctx2.localSeen) := by
  constructor
  · -- queue_sound: states in merged tovisit are reachable
    intro x d h_lookup
    exact fold_insertIfNew_preserves_reachability sys ctx1.tovisit ctx2.tovisit
      ctx1.invs.queue_sound ctx2.invs.queue_sound x d h_lookup
  · -- visited_sound: elements in merged seen/localSeen are reachable
    intro h_inj x h_in_union
    simp only [Std.HashSet.mem_union] at h_in_union
    rcases h_in_union with (h1 | h2) | (h3 | h4)
    · exact ctx1.invs.visited_sound h_inj x (Or.inl h1)
    · exact ctx2.invs.visited_sound h_inj x (Or.inl h2)
    · exact ctx1.invs.visited_sound h_inj x (Or.inr h3)
    · exact ctx2.invs.visited_sound h_inj x (Or.inr h4)
  · -- queue_sub_visited: elements in merged tovisit have fingerprints in merged seen/localSeen
    intro x d h_lookup
    have h_source := Std.HashMap.getElem?_fold_insertIfNew_source ctx1.tovisit ctx2.tovisit (fp.view x) (x, d) h_lookup
    simp only [Std.HashSet.mem_union]
    rcases h_source with h_from_ctx2 | ⟨h_from_ctx1, _⟩
    · rcases ctx2.invs.queue_sub_visited x d h_from_ctx2 with h_seen | h_local
      · exact Or.inl (Or.inr h_seen)
      · exact Or.inr (Or.inr h_local)
    · rcases ctx1.invs.queue_sub_visited x d h_from_ctx1 with h_seen | h_local
      · exact Or.inl (Or.inl h_seen)
      · exact Or.inr (Or.inl h_local)
  · -- queue_wellformed: fingerprints match states in merged tovisit
    intro k x d h_lookup
    rcases Std.HashMap.getElem?_fold_insertIfNew_source ctx1.tovisit ctx2.tovisit k (x, d) h_lookup with h_from_ctx2 | ⟨h_from_ctx1, _⟩
    · exact ctx2.invs.queue_wellformed k x d h_from_ctx2
    · exact ctx1.invs.queue_wellformed k x d h_from_ctx1

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

/-- Delta consistency is preserved when merging two LocalSearchContext instances. -/
theorem merge_local_local_preserves_deltaConsistent {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (ctx1 ctx2 : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (h_inj : Function.Injective fp.view)
  (x : σ)
  (h_in_localSeen : fp.view x ∈ ctx1.localSeen.union ctx2.localSeen) :
  ∃d, (ctx1.tovisit.fold (init := ctx2.tovisit) fun acc k v => acc.insertIfNew k v)[fp.view x]? = some (x, d) := by
  apply getElem?_fold_insertIfNew_deltaConsistent ctx1.tovisit ctx2.tovisit x
    ctx2.invs.queue_wellformed h_inj
  rw [Std.HashSet.mem_union] at h_in_localSeen
  rcases h_in_localSeen with h_in_ctx1 | h_in_ctx2
  · exact Or.inl (ctx1.deltaConsistent h_inj x h_in_ctx1)
  · exact Or.inr (ctx2.deltaConsistent h_inj x h_in_ctx2)

/-- Invariants are preserved when merging a ParallelSearchContext with a LocalSearchContext's results.
    The new context uses aggregatedCtx's tovisit and merges ctx.seen with aggregatedCtx.localSeen. -/
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
    (fun ⟨h, x, d⟩ => aggregatedCtx.tovisit[h]? = some (x, d))
    (fun h => h ∈ ctx.seen.union aggregatedCtx.localSeen) := by
  constructor
  · -- queue_sound
    intro x d h_in_tovisit
    exact aggregatedCtx.invs.queue_sound x d h_in_tovisit
  · -- visited_sound
    intro h_view_inj x h_in_new_seen
    simp only [Std.HashSet.mem_union] at h_in_new_seen
    rcases h_in_new_seen with h_in_ctx_seen | h_in_localSeen
    · exact ctx.invs.visited_sound h_view_inj x h_in_ctx_seen
    · exact aggregatedCtx.invs.visited_sound h_view_inj x (Or.inr h_in_localSeen)
  · -- queue_sub_visited
    intro x d h_in_tovisit
    have h_sub := aggregatedCtx.invs.queue_sub_visited x d h_in_tovisit
    simp only [Std.HashSet.mem_union]
    rcases h_sub with h_in_agg_seen | h_in_localSeen
    · have h_eq := aggregatedCtx.seenUnaltered (fp.view x)
      rw [h_base_eq] at h_eq
      exact Or.inl (h_eq.mpr h_in_agg_seen)
    · exact Or.inr h_in_localSeen
  · -- queue_wellformed
    intro fingerprint st d h_in_tovisit
    exact aggregatedCtx.invs.queue_wellformed fingerprint st d h_in_tovisit

end Veil.ModelChecker.Concrete
