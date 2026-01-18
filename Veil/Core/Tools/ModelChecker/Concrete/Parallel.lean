import Veil.Core.Tools.ModelChecker.Concrete.Core
import Veil.Core.Tools.ModelChecker.Concrete.Progress
import Veil.Core.Tools.ModelChecker.Concrete.ParallelLemmas
import Batteries.Data.Array

namespace Veil.ModelChecker.Concrete


/-- Merge action stats maps by summing counts for each action. -/
private def mergeActionStatsMaps [BEq κ] [Hashable κ] (m1 m2 : Std.HashMap κ ActionStat) : Std.HashMap κ ActionStat :=
  m2.fold (init := m1) fun acc label stat2 =>
    match acc[label]? with
    | some stat1 => acc.insert label { statesGenerated := stat1.statesGenerated + stat2.statesGenerated, distinctStates := stat1.distinctStates + stat2.distinctStates }
    | none => acc.insert label stat2


-- /- Cleaning `tovisit` with enqueueing all their successors should happen
-- at the same time to ensure closed invariants are preserved.
-- Updating tovisit does not unsaify the invariants. -/
def ParallelSearchContextMain.initial {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ) :
  @ParallelSearchContextMain ρ σ κ σₕ fp _ _ th sys params := {
    BaseSearchContext.initial sys params with
    tovisit := sys.initStates.foldl (fun acc s => acc.insert (fp.view s) (s, 0)) Std.HashMap.emptyWithCapacity
    invs := by
      constructor
      · -- queue_sound: all states in tovisit are reachable
        intro x d h_in_tovisit
        dsimp only [Functor.map] at h_in_tovisit
        unfold Membership.mem at h_in_tovisit
        -- tovisit[fp.view x]? = some (x, d)
        have h_in_list : (fp.view x, (x, d)) ∈ (sys.initStates.map (fun s => (fp.view s, (s, 0)))) := by
          have h_cases := HashMap.getElem?_foldl_insert sys.initStates Std.HashMap.emptyWithCapacity
            (fp.view x) (x, d) fp.view (fun s => (s, 0)) h_in_tovisit
          cases h_cases with
          | inl h_empty => simp at h_empty
          | inr h => exact h
        simp only [List.mem_map] at h_in_list
        obtain ⟨s, h_s_in_init, h_eq⟩ := h_in_list
        have h_x_eq : x = s := by grind
        rw [h_x_eq]
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
      · -- queue_sub_visited: elements in tovisit have fingerprints in seen
        intro x d h_in_tovisit
        dsimp only [Functor.map] at h_in_tovisit
        simp only [BaseSearchContext.initial]
        -- If tovisit[fp.view x]? = some (x, d), then fp.view x came from some init state
        have h_in_list : (fp.view x, (x, d)) ∈ (sys.initStates.map (fun s => (fp.view s, (s, 0)))) := by
          have h_cases := HashMap.getElem?_foldl_insert sys.initStates Std.HashMap.emptyWithCapacity
            (fp.view x) (x, d) fp.view (fun s => (s, 0)) h_in_tovisit
          cases h_cases with
          | inl h_empty => simp at h_empty
          | inr h => exact h
        simp only [List.mem_map] at h_in_list
        obtain ⟨s, h_s_in_init, h_eq⟩ := h_in_list
        have h_fp_eq : fp.view s = fp.view x := by grind
        rw [← h_fp_eq]
        apply Std.HashSet.mem_insertMany_of_mem_list
        show fp.view s ∈ List.map fp.view sys.initStates
        simp only [List.mem_map]
        exact ⟨s, h_s_in_init, rfl⟩
      · -- queue_wellformed: fingerprints match states in tovisit
        intro fingerprint st d h_in_tovisit
        dsimp only [Functor.map] at h_in_tovisit
        have h_in_list : (fingerprint, (st, d)) ∈ (sys.initStates.map (fun s => (fp.view s, (s, 0)))) := by
          have h_cases := HashMap.getElem?_foldl_insert sys.initStates Std.HashMap.emptyWithCapacity
            fingerprint (st, d) fp.view (fun s => (s, 0)) h_in_tovisit
          cases h_cases with
          | inl h_empty => simp at h_empty
          | inr h => exact h
        simp only [List.mem_map] at h_in_list
        obtain ⟨s, h_s_in_init, h_eq⟩ := h_in_list
        have h_fp_eq : fp.view s = fingerprint := by grind
        have h_st_eq : s = st := by grind
        rw [← h_st_eq, ← h_fp_eq]
    frontier_closed := by
      intro h_view_inj h_finished s h_in_seen h_not_in_tovisit l next_s h_tr
      unfold BaseSearchContext.initial at h_in_seen
      have h_in_list := Std.HashSet.mem_list_of_mem_insertMany h_in_seen
      simp only [Functor.map, List.mem_map] at h_in_list
      obtain ⟨init_s, h_s_in_init, h_view_eq⟩ := h_in_list
      rw [← h_view_eq] at h_not_in_tovisit
      have h_exists : ∃ val, (sys.initStates.foldl (fun acc st => acc.insert (fp.view st) (st, 0)) Std.HashMap.emptyWithCapacity)[fp.view init_s]? = some val := by
        exact HashMap.mem_of_foldl_insert sys.initStates Std.HashMap.emptyWithCapacity init_s fp.view (fun s => (s, 0)) h_s_in_init
      obtain ⟨val, h_some⟩ := h_exists
      rw [h_some] at h_not_in_tovisit
      simp at h_not_in_tovisit
    terminate_empty_tovisit := by
      intro h_finished_empty_tovisit
      dsimp only [BaseSearchContext.initial] at h_finished_empty_tovisit
      grind
  }

@[inline, specialize]
def ParallelSearchContextSub.tryExploreNeighbor {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ] [Repr κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (fpSt : σₕ)      -- fingerprint of state we're coming from (pre-state), for logging
  (depth : Nat)    -- depth of the current state (neighbor will be at depth + 1)
  (ctx : @ParallelSearchContextMerge ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (neighbor : κ × σ)
  (h_neighbor : sys.reachable neighbor.2)
  (h_not_finished : !ctx.hasFinished)
: {ctx' : @ParallelSearchContextMerge ρ σ κ σₕ fp _ _ th sys params baseCtx //
    ctx'.finished = ctx.finished ∧
    ctx'.seen = ctx.seen ∧
    (∀fp, fp ∈ ctx.localSeen → fp ∈ ctx'.localSeen) ∧
    (ctx'.seen.contains (fp.view neighbor.2) ∨ ctx'.localSeen.contains (fp.view neighbor.2))  } :=
  let ⟨label, succ⟩ := neighbor
  let fingerprint := fp.view succ
  have h_succ_reachable : sys.reachable succ := h_neighbor
  if h_has_seen : ctx.seen.contains fingerprint || ctx.localSeen.contains fingerprint then
    ⟨ctx, by constructor <;> grind⟩
  else
    have h_not_in_seen : !ctx.seen.contains fingerprint := by simp at h_has_seen ⊢; exact h_has_seen.1
    have h_not_in_localSeen : !ctx.localSeen.contains fingerprint := by simp at h_has_seen ⊢; exact h_has_seen.2
    let newActionStatsMap := match ctx.localActionStatsMap[label]? with
      | some stat => ctx.localActionStatsMap.insert label { stat with distinctStates := stat.distinctStates + 1 }
      | none => ctx.localActionStatsMap.insert label { statesGenerated := 0, distinctStates := 1 }
    ⟨{ctx with
      localSeen := ctx.localSeen.insert fingerprint,
      tovisit   := ctx.tovisit.insert fingerprint ⟨succ, depth + 1⟩,
      localLog  := ctx.localLog.insert fingerprint (fpSt, label),
      localActionStatsMap := newActionStatsMap,
      -- seenDisjoint := by
      --   intro h_fp h_fp_in_seen; simp
      --   constructor
      --   . intro h_eq; simp [h_eq] at h_not_in_seen
      --     exact h_not_in_seen h_fp_in_seen
      --   . exact ctx.seenDisjoint h_fp h_fp_in_seen
      invs := ParallelSearchContextMerge.insert_and_enqueue_preserves_invs sys params ctx fingerprint succ depth h_succ_reachable rfl,
      deltaConsistent := by
        have h_old := ctx.deltaConsistent
        intro h_inj x h_in_localSeen
        by_cases h_eq : fp.view x = fingerprint
        · -- Case: fp.view x = fingerprint, so x = succ by injectivity
          have h_x_eq_succ : x = succ := h_inj h_eq
          use depth + 1
          rw [h_x_eq_succ, Std.HashMap.getElem?_insert]
          simp
          grind
        · -- Case: fp.view x ≠ fingerprint, so x was already in ctx.localSeen
          have h_in_old_localSeen : fp.view x ∈ ctx.localSeen := by
            simp only [Std.HashSet.mem_insert] at h_in_localSeen
            cases h_in_localSeen with
            | inl h => grind
            | inr h => exact h
          -- Use the old deltaConsistent
          obtain ⟨d, h_in_tovisit⟩ := h_old h_inj x h_in_old_localSeen
          use d
          rw [Std.HashMap.getElem?_insert]
          grind
    }, (by constructor <;> grind)⟩

-- Helper function: recursively process successors with explicit induction structure
-- Modified to only require that all successors come from sys.tr th curr (subset property)
@[inline, specialize]
def ParallelSearchContextSub.processSuccessors {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ] [Repr κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (curr : σ)      -- current state being processed
  (fpSt : σₕ)     -- fingerprint of curr
  (depth : Nat)   -- depth of curr
  (h_curr : sys.reachable curr)
  (successors : List (κ × σ))
  (h_succ_subset : ∀ x, x ∈ successors → x ∈ extractSuccessfulTransitions (sys.tr th curr))
  (ctx : @ParallelSearchContextMerge ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (h_not_finished : !ctx.hasFinished)
  : {ctx' : @ParallelSearchContextMerge ρ σ κ σₕ fp _ _ th sys params baseCtx //
      ctx'.finished = ctx.finished ∧
      (∀ (l : κ) (v : σ), (l, v) ∈ successors → (fp.view v) ∈ ctx'.seen ∨ (fp.view v) ∈ ctx'.localSeen) ∧
      ctx'.seen = ctx.seen ∧
      (∀ fp_elem, fp_elem ∈ ctx.localSeen → fp_elem ∈ ctx'.localSeen) } :=
  match successors with
  | [] => ⟨ctx, by constructor <;> grind⟩
  | (label, state) :: rest =>
    have h_in_sys_tr : (label, .success state) ∈ sys.tr th curr := by
      have h_in_extracted : (label, state) ∈ extractSuccessfulTransitions (sys.tr th curr) := by grind
      unfold extractSuccessfulTransitions at h_in_extracted;grind
    have h_next : sys.next curr state := ⟨label, h_in_sys_tr⟩
    have h_neighbor_reachable : sys.reachable state := EnumerableTransitionSystem.reachable.step curr state h_curr h_next
    /- `Function Call` -/
    let neighbor_result := ParallelSearchContextSub.tryExploreNeighbor sys fpSt depth ctx ⟨label, state⟩ h_neighbor_reachable h_not_finished
    have h_current_in_seen := neighbor_result.property.2.2.2
    have h_finished_preserved : neighbor_result.val.finished = ctx.finished := neighbor_result.property.1
    have h_still_not_finished : !neighbor_result.val.hasFinished := by
      unfold BaseSearchContext.hasFinished at h_not_finished ⊢; rw [h_finished_preserved]; exact h_not_finished
    have h_rest_subset : ∀ x, x ∈ rest → x ∈ extractSuccessfulTransitions (sys.tr th curr) := by
      intro x h_x_in_rest; apply h_succ_subset; exact List.mem_cons_of_mem (label, state) h_x_in_rest
    have h_neighbor_delta_consistent := neighbor_result.property.2.2.2
    let rest_result := processSuccessors sys curr fpSt depth h_curr rest
      h_rest_subset neighbor_result.val h_still_not_finished
    ⟨rest_result.val, by
      constructor
      · have h1 := rest_result.property.1 -- 1. finished unchanged through the whole process
        rw [h1, h_finished_preserved]
      constructor
      · intro l v h_in_cons   -- 2.All successors are in seen or localSeen
        cases h_in_cons with
        | head =>
          simp at *;
          have h_rest_seen_eq : rest_result.val.seen = neighbor_result.val.seen := rest_result.property.2.2.1
          have h_rest_localSeen_mono := rest_result.property.2.2.2
          cases h_current_in_seen with
          | inl h_in_seen => left; rw [h_rest_seen_eq]; exact h_in_seen
          | inr h_in_localSeen => right; exact h_rest_localSeen_mono (fp.view state) h_in_localSeen
        | tail _ h_in_rest => exact rest_result.property.2.1 l v h_in_rest
      constructor -- seen unchanged: rest_result.val.seen = ctx.seen
      · have h1 : rest_result.val.seen = neighbor_result.val.seen := rest_result.property.2.2.1
        have h2 : neighbor_result.val.seen = ctx.seen := neighbor_result.property.2.1
        rw [h1, h2]
      -- constructor -- localSeen monotonic: ctx.localSeen ⊆ rest_result.val.localSeen
      · intro fp_elem h_in_ctx
        have h1 : fp_elem ∈ neighbor_result.val.localSeen := neighbor_result.property.2.2.1 fp_elem h_in_ctx
        exact rest_result.property.2.2.2 fp_elem h1
  ⟩
termination_by successors.length


@[inline, specialize]
def ParallelSearchContextSub.processState {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ] [Repr σ] [Repr σₕ] [Repr κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (fpSt : σₕ)
  (depth : Nat)
  (curr : σ)
  (h_curr : sys.reachable curr)
  (ctx : @ParallelSearchContextMerge ρ σ κ σₕ fp _ _ th sys params baseCtx) :
  {ctx' : @ParallelSearchContextMerge ρ σ κ σₕ fp _ _ th sys params baseCtx //
    (∀ x, x ∈ ctx.localSeen → x ∈ ctx'.localSeen) ∧ -- 1. Monotonicity
    (ctx'.seen = ctx.seen) ∧                        -- 2. Stability
    (!ctx'.hasFinished → !ctx.hasFinished) ∧        -- 3. Finished reverse implication
    (∀ fp_elem, fp_elem ∈ ctx.localSeen → fp_elem ∈ ctx'.localSeen) ∧
    (!ctx'.hasFinished → ∀l v, (l, v) ∈ extractSuccessfulTransitions (sys.tr th curr) → (fp.view v) ∈ ctx'.seen ∨ (fp.view v) ∈ ctx'.localSeen)} := -- 3. Completeness
  match h_process : ctx.toBaseSearchContext.processState sys fpSt curr with
  | (baseCtx', outcomesOpt) =>
    have h_ctx_not_explored_all : ¬ctx.finished = some .exploredAllReachableStates := by exact ctx.excludeAllStatesFinish
    have h_seen_unchanged : baseCtx'.seen = ctx.seen := by
      have h_preserves := BaseSearchContext.processState_preserves_seen sys params fpSt curr ctx.toBaseSearchContext
      rw [h_process] at h_preserves
      exact h_preserves
    match outcomesOpt with
    | none =>
      -- Case 1: Early Termination (Searching stopped)
      have h_early_terminate : baseCtx'.finished.isSome := by
        unfold BaseSearchContext.processState at h_process
        simp at h_process; grind
      ⟨{ ctx with
        toBaseSearchContext := baseCtx'
        excludeAllStatesFinish := BaseSearchContext.processState_returns_none_excludes_exploredAll sys fpSt curr
          ctx.toBaseSearchContext baseCtx' h_process
        seenUnaltered := by intro s; rw [h_seen_unchanged]; exact ctx.seenUnaltered s
        invs := by
          constructor
          · exact ctx.invs.queue_sound
          · intro h_view_inj x h_in_seen
            rw [h_seen_unchanged] at h_in_seen
            exact ctx.invs.visited_sound h_view_inj x h_in_seen
          · intro x d h_in_queue
            have h_old := ctx.invs.queue_sub_visited x d h_in_queue
            rw [h_seen_unchanged]
            exact h_old
          · exact ctx.invs.queue_wellformed
      }, by
        constructor
        · intro x h; exact h
        constructor
        · dsimp; exact h_seen_unchanged
        constructor
        . intro h_not_finished
          unfold BaseSearchContext.hasFinished at h_not_finished
          dsimp at h_not_finished
          simp at h_not_finished
          grind
        constructor
        . simp
        · intro h_not_finished
          unfold BaseSearchContext.hasFinished at h_not_finished
          dsimp at h_not_finished
          simp at h_not_finished
          grind
      ⟩
    | some ⟨outcomes, heq⟩ =>
      -- Case 2: Normal Processing
      have h_not_explored_all : ¬ctx.finished = some .exploredAllReachableStates := by exact ctx.excludeAllStatesFinish
      have h_not_finished : !baseCtx'.finished.isSome := by
        have := BaseSearchContext.processState_returns_some_implies_not_finished sys fpSt curr ctx.toBaseSearchContext baseCtx' ⟨outcomes, heq⟩ h_not_explored_all h_process
        simp [this]
      let successfulTransitions := extractSuccessfulTransitions outcomes
      let newLocalStatesFound := ctx.localStatesFound + successfulTransitions.length
      let newLocalActionStatsMap := successfulTransitions.foldl (init := ctx.localActionStatsMap) fun acc (label, _) =>
        match acc[label]? with
        | some stat => acc.insert label { stat with statesGenerated := stat.statesGenerated + 1 }
        | none => acc.insert label { statesGenerated := 1, distinctStates := 0 }
      let ctx_updated : @ParallelSearchContextMerge ρ σ κ σₕ fp _ _ th sys params baseCtx :=
      { ctx with
        toBaseSearchContext := baseCtx'
        seenUnaltered := by intro s; rw [h_seen_unchanged]; exact ctx.seenUnaltered s
        localStatesFound := newLocalStatesFound
        localActionStatsMap := newLocalActionStatsMap
        excludeAllStatesFinish := by simp at h_not_finished; simp [h_not_finished]
        invs := by
          have h_process_fst : (ctx.toBaseSearchContext.processState sys fpSt curr).1 = baseCtx' := by
            rw [h_process]
          exact ParallelSearchContextMerge.update_base_after_processState_preserves_invs sys ctx fpSt curr baseCtx' h_process_fst
      }
      have h_ctx_updated_seen_eq : ctx_updated.seen = ctx.seen := h_seen_unchanged
      have h_ctx_updated_localSeen_eq : ctx_updated.localSeen = ctx.localSeen := rfl
      have h_ctx_updated_not_finished : !ctx_updated.hasFinished := by simp only [ctx_updated]; exact h_not_finished
      /-`Function Call`-/
      let res := ParallelSearchContextSub.processSuccessors sys curr fpSt depth h_curr successfulTransitions (by grind) ctx_updated h_ctx_updated_not_finished
      have h_res_completeness := res.property.2.1
      have h_res_seen_eq := res.property.2.2.1
      have h_res_localSeen_mono := res.property.2.2.2
      ⟨res.val, by
        -- constructor
        refine ⟨?mono, ?stability, ?revFinished, ?complete⟩
        · intro x h_in_ctx
          rw [← h_ctx_updated_localSeen_eq] at h_in_ctx
          exact h_res_localSeen_mono x h_in_ctx
        · rw [h_res_seen_eq]; rw [h_ctx_updated_seen_eq] -- ctx_updated.seen -> ctx.seen
        · intro h_res_not_finished
          unfold BaseSearchContext.hasFinished
          have h_ctx_finished_none : ctx.finished = none := by
            cases h_ctx_finished : ctx.finished with
            | none => rfl
            | some finished_reason =>
              cases finished_reason with
              | earlyTermination condition =>
                unfold BaseSearchContext.processState at h_process
                simp only at h_process
                unfold BaseSearchContext.checkViolationsAndMaybeTerminate at h_process
                rw [h_ctx_finished] at h_process
                simp at h_process
                grind
              | exploredAllReachableStates =>
                exact absurd h_ctx_finished h_not_explored_all
          rw [h_ctx_finished_none];simp
        · grind
      ⟩


@[inline, specialize]
def ParallelSearchContextMerge.processWorkQueue {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ] [Repr σ] [Repr σₕ] [Repr κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (queueList : List (σₕ × σ × Nat)) -- Input as a List, matching processSuccessors style
  (h_reachable : ∀ q ∈ queueList, sys.reachable q.2.1)
  (ctx : @ParallelSearchContextMerge ρ σ κ σₕ fp _ _ th sys params baseCtx)
  -- (h_not_finished : !ctx.hasFinished) -- Precondition: We are not finished yet
  : {ctx' : @ParallelSearchContextMerge ρ σ κ σₕ fp _ _ th sys params baseCtx //
      (!ctx'.hasFinished → ∀ item ∈ queueList, ∀ l v, (l, .success v) ∈ (sys.tr th item.2.1) → ((fp.view v) ∈ ctx'.seen ∨ (fp.view v) ∈ ctx'.localSeen)) ∧
      (ctx'.seen = ctx.seen) ∧  -- Stability
      (∀ fp_elem, fp_elem ∈ ctx.localSeen → fp_elem ∈ ctx'.localSeen) ∧ -- Monotonicity
      (!ctx'.hasFinished → !ctx.hasFinished) } :=
  match queueList with
  | [] => ⟨ctx, by constructor <;> grind⟩
  | item :: rest =>
    let ⟨fpSt, curr, depth⟩ := item
    have h_curr_reachable : sys.reachable curr :=
      h_reachable (fpSt, curr, depth) List.mem_cons_self
    /- `Function Call` -/
    let ⟨next_ctx, h_next_props⟩ := ParallelSearchContextSub.processState sys fpSt depth curr h_curr_reachable ctx
    if h_next_finished : next_ctx.hasFinished then
      ⟨next_ctx, by grind⟩
    else
      have h_next_not_finished : !next_ctx.hasFinished := by grind
      have h_rest_subset : ∀ x ∈ rest, sys.reachable x.2.1 := by intro x hx; apply h_reachable; exact List.mem_cons_of_mem _ hx
        /- `Recursive Call` -/
      let rest_result := processWorkQueue sys rest h_rest_subset next_ctx
      ⟨rest_result.val, by
        have h_res_props := rest_result.property
        refine ⟨?complete, ?stability, ?mono, ?revFinished⟩
        · intro h_final_nf item_arg item_mem l v h_tr
          rw [List.mem_cons] at item_mem
          cases item_mem with
          | inl h_eq =>
            subst h_eq
            -- Convert (l, .success v) ∈ sys.tr th curr to (l, v) ∈ extractSuccessfulTransitions (sys.tr th curr)
            have h_in_extracted : (l, v) ∈ extractSuccessfulTransitions (sys.tr th curr) := by
              unfold extractSuccessfulTransitions
              simp only [List.mem_filterMap]
              exact ⟨(l, .success v), h_tr, rfl⟩
            have h_head_processed := h_next_props.2.2.2.2 h_next_not_finished l v h_in_extracted
            have h_mono := h_res_props.2.2.1
            have h_stable := h_res_props.2.1
            cases h_head_processed with
            | inl h_seen => left; rw [h_stable]; exact h_seen
            | inr h_local => right; exact h_mono _ h_local
          | inr h_in_rest => exact h_res_props.1 h_final_nf _ h_in_rest l v h_tr
        · rw [h_res_props.2.1, h_next_props.2.1]
        · intro x hx
          apply h_res_props.2.2.1
          apply h_next_props.1
          exact hx
        · intro h_nf
          have h1 := h_res_props.2.2.2 h_nf
          exact h_next_props.2.2.1 h1
      ⟩
termination_by queueList.length




def ParallelSearchContextMerge.Merge {ρ σ κ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ] {th : ρ}
  (sys : _) (params : _)
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (ctx1 ctx2 : @ParallelSearchContextMerge ρ σ κ σₕ fp _ _ th sys params baseCtx) :
  @ParallelSearchContextMerge ρ σ κ σₕ fp _ _ th sys params baseCtx := {
    ctx1 with
      seen := ctx1.seen.union ctx2.seen,
      localLog := ctx1.localLog.union ctx2.localLog,
      localSeen := ctx1.localSeen.union ctx2.localSeen,
      violatingStates := ctx2.violatingStates ++ ctx1.violatingStates,
      finished := Option.or ctx1.finished ctx2.finished
      tovisit := ctx1.tovisit.fold (init := ctx2.tovisit) fun acc k v => acc.insertIfNew k v
      localStatesFound := ctx1.localStatesFound + ctx2.localStatesFound,
      localActionStatsMap := mergeActionStatsMaps ctx1.localActionStatsMap ctx2.localActionStatsMap

      invs := by
        constructor
        · -- queue_sound: states in merged tovisit are reachable
          intro x d h_lookup
          -- Use the reachability preservation theorem
          have h_ctx1_sound : ∀ x d, ctx1.tovisit[fp.view x]? = some (x, d) → sys.reachable x := by
            intro x d h_in
            exact ctx1.invs.queue_sound x d h_in
          have h_ctx2_sound : ∀ x d, ctx2.tovisit[fp.view x]? = some (x, d) → sys.reachable x := by
            intro x d h_in
            exact ctx2.invs.queue_sound x d h_in
          exact HashMap.fold_insertIfNew_preserves_reachability sys ctx1.tovisit ctx2.tovisit
            h_ctx1_sound h_ctx2_sound x d h_lookup
        · -- visited_sound: elements in merged seen/localSeen are reachable
          intro h_inj x h_in_union
          -- h_in_union : fp.view x ∈ (ctx1.seen ∪ ctx2.seen) ∪ (ctx1.localSeen ∪ ctx2.localSeen)
          simp only [Std.HashSet.mem_union] at h_in_union
          rcases h_in_union with (h_in_ctx1_seen | h_in_ctx2_seen) | (h_in_ctx1_local | h_in_ctx2_local)
          · -- Case 1: fp.view x ∈ ctx1.seen
            apply ctx1.invs.visited_sound h_inj x
            left; exact h_in_ctx1_seen
          · -- Case 2: fp.view x ∈ ctx2.seen
            apply ctx2.invs.visited_sound h_inj x
            left; exact h_in_ctx2_seen
          · -- Case 3: fp.view x ∈ ctx1.localSeen
            apply ctx1.invs.visited_sound h_inj x
            right; exact h_in_ctx1_local
          · -- Case 4: fp.view x ∈ ctx2.localSeen
            apply ctx2.invs.visited_sound h_inj x
            right; exact h_in_ctx2_local
        · -- queue_sub_visited: elements in merged tovisit have fingerprints in merged seen/localSeen
          intro x d h_lookup
          have h_source := HashMap.getElem?_fold_insertIfNew_source ctx1.tovisit ctx2.tovisit (fp.view x) (x, d) h_lookup
          simp only [Std.HashSet.mem_union]
          cases h_source with
          | inl h_from_ctx2 =>
            have h_sub := ctx2.invs.queue_sub_visited x d h_from_ctx2
            rcases h_sub with h_in_seen | h_in_local
            · left; right; exact h_in_seen
            · right; right; exact h_in_local
          | inr h_from_ctx1 =>
            have h_sub := ctx1.invs.queue_sub_visited x d h_from_ctx1.1
            rcases h_sub with h_in_seen | h_in_local
            · left; left; exact h_in_seen
            · right; left; exact h_in_local
        · -- queue_wellformed: fingerprints match states in merged tovisit
          intro k x d h_lookup
          have h_source := HashMap.getElem?_fold_insertIfNew_source ctx1.tovisit ctx2.tovisit k (x, d) h_lookup
          cases h_source with
          | inl h_from_ctx2 =>
            exact ctx2.invs.queue_wellformed k x d h_from_ctx2
          | inr h_from_ctx1 =>
            exact ctx1.invs.queue_wellformed k x d h_from_ctx1.1
      excludeAllStatesFinish := by
        have ctx1_finished := ctx1.excludeAllStatesFinish
        have ctx2_finished := ctx2.excludeAllStatesFinish
        by_contra h_not_finished
        unfold Option.or at h_not_finished
        split at h_not_finished <;> rename_i h_ctx1_def
        · simp at h_not_finished
          rw [← h_not_finished] at ctx1_finished
          contradiction
        · contradiction
      seenUnaltered := by
        have h1 := ctx1.seenUnaltered
        have h2 := ctx2.seenUnaltered
        intro s; rw [Std.HashSet.mem_union, ←h1 s, ←h2 s]; simp
      deltaConsistent := by
        intro h_inj x h_in_localSeen
        have h1 := ctx1.deltaConsistent h_inj x
        have h2 := ctx2.deltaConsistent h_inj x
        have h2_tovisit_wellformed := ctx2.invs.queue_wellformed
        apply HashMap.getElem?_fold_insertIfNew_deltaConsistent ctx1.tovisit ctx2.tovisit x h2_tovisit_wellformed h_inj
        rw [Std.HashSet.mem_union] at h_in_localSeen
        rcases h_in_localSeen with h_in_ctx1 | h_in_ctx2
        · left; exact h1 h_in_ctx1
        · right; exact h2 h_in_ctx2

  }


-- Helper lemma: foldl preserves seen membership (from any merged context)
theorem IteratedProd.foldlMergePreservesSeen {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ] {th : ρ}
  (sys : _) (params : _)
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  {splitArrays : List (Array (σₕ × σ × Nat))}
  (init : @ParallelSearchContextMerge ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (results : IteratedProd (List.map (fun x => { ctx' //
    (!ctx'.hasFinished) → ∀ item ∈ x,
    ∀ (l : κ) (v : σ), (l, .success v) ∈ sys.tr th item.2.1 →
    StateView.view v ∈ ctx'.seen ∨ StateView.view v ∈ ctx'.localSeen })
    splitArrays))
  (x : σₕ) (h : x ∈ init.seen) :
  x ∈ (IteratedProd.foldl init (fun acc r => .Merge sys params baseCtx acc r.val) results).seen := by
  induction splitArrays generalizing init with
  | nil => exact h
  | cons arr rest ih =>
    obtain ⟨headRes, tailRes⟩ := results
    simp only [IteratedProd.foldl]
    apply ih
    simp only [ParallelSearchContextMerge.Merge, Std.HashSet.mem_union]
    left; exact h

-- Helper lemma: foldl preserves localSeen membership (from any merged context)
theorem IteratedProd.foldlMergePreservesLocalSeen {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ] {th : ρ}
  (sys : _) (params : _)
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  {splitArrays : List (Array (σₕ × σ × Nat))}
  (init : @ParallelSearchContextMerge ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (results : IteratedProd (List.map (fun x => { ctx' //
    (!ctx'.hasFinished) → ∀ item ∈ x,
    ∀ (l : κ) (v : σ), (l, .success v) ∈ sys.tr th item.2.1 →
    StateView.view v ∈ ctx'.seen ∨ StateView.view v ∈ ctx'.localSeen })
    splitArrays))
  (x : σₕ) (h : x ∈ init.localSeen) :
  x ∈ (IteratedProd.foldl init (fun acc r => .Merge sys params baseCtx acc r.val) results).localSeen := by
  induction splitArrays generalizing init with
  | nil => exact h
  | cons arr rest ih =>
    obtain ⟨headRes, tailRes⟩ := results
    simp only [IteratedProd.foldl]
    apply ih
    simp only [ParallelSearchContextMerge.Merge, Std.HashSet.mem_union]
    left; exact h

-- Helper: foldl Merge preserves hasFinished = true
theorem IteratedProd.foldlMergePreservesHasFinished {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ] {th : ρ}
  (sys : _) (params : _)
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (rest : List (Array (σₕ × σ × Nat)))
  (init : @ParallelSearchContextMerge ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (tailRes : IteratedProd (List.map (fun x => { ctx' : ParallelSearchContextMerge sys params baseCtx //
    (!ctx'.hasFinished) → ∀ item ∈ x,
      ∀ (l : κ) (v : σ), (l, .success v) ∈ sys.tr th item.2.1 →
        StateView.view v ∈ ctx'.seen ∨ StateView.view v ∈ ctx'.localSeen }) rest))
  (h_init_finished : init.hasFinished) :
  (IteratedProd.foldl init (fun acc r => .Merge sys params baseCtx acc r.val) tailRes).hasFinished := by
  induction rest generalizing init with
  | nil =>
    simp only [IteratedProd.foldl]
    exact h_init_finished
  | cons arr rest' ih =>
    obtain ⟨headRes, tailRes'⟩ := tailRes
    simp only [IteratedProd.foldl]
    apply ih
    -- Show (Merge init headRes.val).hasFinished
    simp only [ParallelSearchContextMerge.Merge, BaseSearchContext.hasFinished, Option.isSome_or]
    simp only [BaseSearchContext.hasFinished] at h_init_finished
    simp only [h_init_finished, Bool.true_or]

-- Helper lemma: if foldl result is not finished, then the first merged context's second arg is not finished
theorem IteratedProd.foldlMergeNotFinishedHead {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ] {th : ρ}
  (sys : _) (params : _)
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (init : ParallelSearchContextMerge sys params baseCtx)
  {arr : Array (σₕ × σ × Nat)} {rest : List (Array (σₕ × σ × Nat))}
  (headRes : { ctx' : @ParallelSearchContextMerge ρ σ κ σₕ fp _ _ th sys params baseCtx //
    (!ctx'.hasFinished) → ∀ item ∈ arr,
      ∀ (l : κ) (v : σ), (l, .success v) ∈ sys.tr th item.2.1 →
      StateView.view v ∈ ctx'.seen ∨ StateView.view v ∈ ctx'.localSeen })
  (tailRes : IteratedProd (List.map (fun x => { ctx' : ParallelSearchContextMerge sys params baseCtx //
    (!ctx'.hasFinished) → ∀ item ∈ x,
      ∀ (l : κ) (v : σ), (l, .success v) ∈ sys.tr th item.2.1 →
        StateView.view v ∈ ctx'.seen ∨ StateView.view v ∈ ctx'.localSeen }) rest))
  (h_init_not_finished : init.finished = none)
  (h : !(IteratedProd.foldl
    (ParallelSearchContextMerge.Merge sys params baseCtx init headRes.val)
    (fun acc r => .Merge sys params baseCtx acc r.val) tailRes).hasFinished) :
  !headRes.val.hasFinished := by
  by_contra h_finished
  simp only [Bool.not_eq_true] at h_finished
  have h_head_finished : headRes.val.hasFinished = true := by
    cases h_eq : headRes.val.hasFinished with
    | true => rfl
    | false => simp only [h_eq, Bool.not_false] at h_finished; cases h_finished
  have h_merge_finished : (ParallelSearchContextMerge.Merge sys params baseCtx init headRes.val).hasFinished := by
    simp only [ParallelSearchContextMerge.Merge, BaseSearchContext.hasFinished, Option.isSome_or]
    simp only [BaseSearchContext.hasFinished] at h_head_finished
    simp only [h_init_not_finished, Option.isSome_none, Bool.false_or]
    exact h_head_finished
  -- Now show that foldl preserves hasFinished = true
  have h_foldl_finished : (IteratedProd.foldl
    (ParallelSearchContextMerge.Merge sys params baseCtx init headRes.val)
    (fun acc r => .Merge sys params baseCtx acc r.val) tailRes).hasFinished :=
    IteratedProd.foldlMergePreservesHasFinished sys params baseCtx rest
      (.Merge sys params baseCtx init headRes.val) tailRes h_merge_finished
  simp only [h_foldl_finished, Bool.not_true] at h
  grind


def initializeNeutralCtx {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : _) (params : _)
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (h_seen_sound : Function.Injective fp.view → ∀ (x : σ), fp.view x ∈ baseCtx.seen → sys.reachable x)
  : @ParallelSearchContextMerge ρ σ κ σₕ fp _ _ th sys params baseCtx := {
    toBaseSearchContext := { baseCtx with finished := none},
    tovisit := Std.HashMap.emptyWithCapacity,
    localSeen := Std.HashSet.emptyWithCapacity,
    localLog := Std.HashMap.emptyWithCapacity,
    localStatesFound := 0,
    localActionStatsMap := Std.HashMap.emptyWithCapacity,
    invs := by constructor <;> grind
    excludeAllStatesFinish := by grind
    seenUnaltered := by grind
    deltaConsistent := by grind
  }

@[inline, specialize]
def ParallelSearchContextMerge.bfsBigStep {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ] [Repr σ] [Repr σₕ] [Repr κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (queue : Array (σₕ × σ × Nat))
  (h_seen_sound : Function.Injective fp.view → ∀ (x : σ), fp.view x ∈ baseCtx.seen → sys.reachable x)
  -- (h_inits_in : ∀ (s₀ : σ), s₀ ∈ sys.initStates → (fp.view s₀) ∈ baseCtx.seen)
  (h_reachable : ∀ item ∈ queue.toList, sys.reachable item.2.1)
: m ( {ctx' : @ParallelSearchContextMerge ρ σ κ σₕ fp _ _ th sys params baseCtx //
    !ctx'.hasFinished → ∀item ∈ queue,
      (∀l v, (l, .success v) ∈ (sys.tr th item.2.1) →
        (fp.view v) ∈ ctx'.seen ∨ (fp.view v) ∈ ctx'.localSeen)})
  := do
  let ctx := initializeNeutralCtx sys params baseCtx h_seen_sound
  let startTime ← IO.monoMsNow
  let result := processWorkQueue sys queue.toList h_reachable ctx
  -- let ctxAfter := result.val
  let endTime ← IO.monoMsNow
  IO.eprintln s!"[{endTime} @ tid {← IO.getTID}] took {endTime - startTime}ms to process {queue.size} states (queue size now: {result.val.tovisit.size})"
  pure ⟨result.val, by
    intro h_not_finished item h_item_in_queue l v h_tr
    have h_item_in_list : item ∈ queue.toList := Array.mem_toList_iff.mpr h_item_in_queue
    exact result.property.1 h_not_finished item h_item_in_list l v h_tr
  ⟩


-- Helper: generalized version that works with any init
theorem liftBfsBigStepPropertiesAux {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : _)
  {params : SearchParameters ρ σ}
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (splitArrays : List (Array (σₕ × σ × Nat)))
  (init : ParallelSearchContextMerge sys params baseCtx)
  (h_init_not_finished : init.finished = none)
  (results : IteratedProd (List.map (fun x => { ctx' //
    (!ctx'.hasFinished) → ∀ item ∈ x, ∀ (l : κ) (v : σ), (l, .success v) ∈ sys.tr th item.2.1 →
    StateView.view v ∈ ctx'.seen ∨ StateView.view v ∈ ctx'.localSeen })
    splitArrays))
  (h_not_finished : !(IteratedProd.foldl init (fun acc r => .Merge sys params baseCtx acc r.val) results).hasFinished)
  (item : σₕ × σ × Nat) (h_item_in_flatten : item ∈ splitArrays.toArray.flatten)
  (l : κ) (v : σ) (h_tr : (l, .success v) ∈ sys.tr th item.2.1) :
  (fp.view v) ∈ (IteratedProd.foldl init (fun acc r => .Merge sys params baseCtx acc r.val) results).seen ∨
  (fp.view v) ∈ (IteratedProd.foldl init (fun acc r => .Merge sys params baseCtx acc r.val) results).localSeen := by
  induction splitArrays generalizing init with
  | nil =>
    -- If splitArrays is empty, flatten is empty, contradiction
    have : ([] : List (Array (σₕ × σ × Nat))).toArray.flatten = #[] := rfl
    rw [this] at h_item_in_flatten
    exact absurd h_item_in_flatten (Array.not_mem_empty item)
  | cons arr rest ih =>
    obtain ⟨headRes, tailRes⟩ := results
    -- item is either in arr or in the rest
    have h_flatten : (arr :: rest).toArray.flatten = arr ++ rest.toArray.flatten := by
      apply Array.ext'
      simp [Array.toList_append]
    rw [h_flatten, Array.mem_append] at h_item_in_flatten
    simp only [IteratedProd.foldl]
    cases h_item_in_flatten with
    | inl h_in_arr =>
      -- item is in the first array `arr`
      have h_headRes_prop := headRes.property
      -- Show headRes.val is not finished
      have h_head_not_finished : !headRes.val.hasFinished :=
        IteratedProd.foldlMergeNotFinishedHead sys params baseCtx init headRes tailRes h_init_not_finished h_not_finished
      have h_succ := h_headRes_prop h_head_not_finished item h_in_arr l v h_tr
      cases h_succ with
      | inl h_in_seen =>
        left
        apply IteratedProd.foldlMergePreservesSeen
        simp only [ParallelSearchContextMerge.Merge, Std.HashSet.mem_union]
        right; exact h_in_seen
      | inr h_in_localSeen =>
        right
        apply IteratedProd.foldlMergePreservesLocalSeen
        simp only [ParallelSearchContextMerge.Merge, Std.HashSet.mem_union]
        right; exact h_in_localSeen
    | inr h_in_rest =>
      -- item is in rest, apply IH with init' = Merge init headRes.val
      have h_init'_not_finished : (ParallelSearchContextMerge.Merge sys params baseCtx init headRes.val).finished = none := by
        simp only [ParallelSearchContextMerge.Merge]
        -- (Merge init headRes.val).finished = Option.or init.finished headRes.val.finished
        -- Since init.finished = none, this equals headRes.val.finished
        simp only [h_init_not_finished, Option.none_or]
        -- Need to show headRes.val.finished = none
        -- If not, then headRes.val.hasFinished, contradicting foldlMergeNotFinishedHead
        by_contra h_head_fin
        have h_head_finished : headRes.val.hasFinished := by
          simp only [BaseSearchContext.hasFinished, Option.isSome_iff_ne_none]
          exact h_head_fin
        have h_head_not_finished : !headRes.val.hasFinished :=
          IteratedProd.foldlMergeNotFinishedHead sys params baseCtx init headRes tailRes h_init_not_finished h_not_finished
        simp only [h_head_finished, Bool.not_true] at h_head_not_finished
        cases h_head_not_finished
      exact ih (ParallelSearchContextMerge.Merge sys params baseCtx init headRes.val)
        h_init'_not_finished tailRes h_not_finished h_in_rest

theorem liftBfsBigStepProperties {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : _)
  {params : SearchParameters ρ σ}
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (h_seen_sound : Function.Injective fp.view → ∀ (x : σ), fp.view x ∈ baseCtx.seen → sys.reachable x)
  -- (h_baseCtx_not_finished : baseCtx.finished = none)
  (splitArrays : List (Array (σₕ × σ × Nat)))
  (postCtx : ParallelSearchContextMerge sys params baseCtx)
  --------------------------------------------------------------------------------------------------------
  (results : IteratedProd (List.map (fun x => { ctx' //
    (!ctx'.hasFinished) → ∀ item ∈ x,
      ∀ (l : κ) (v : σ), (l, .success v) ∈ sys.tr th item.2.1 →
        StateView.view v ∈ ctx'.seen ∨ StateView.view v ∈ ctx'.localSeen })
    splitArrays))
  --------------------------------------------------------------------------------------------------------
  (h_postCtx_eq : postCtx = IteratedProd.foldl
    (init := initializeNeutralCtx sys params baseCtx h_seen_sound)
    (fun acc r => .Merge sys params baseCtx acc r.val) results) :
  --------------------------------------------------------------------------------------------------------
  (!postCtx.hasFinished →
    ∀ item ∈ splitArrays.toArray.flatten,
      ∀ l v, (l, .success v) ∈ (sys.tr th item.2.1) →
        (fp.view v) ∈ postCtx.seen ∨ (fp.view v) ∈ postCtx.localSeen)
  := by
  intro h_not_finished item h_item_in_flatten l v h_tr
  rw [h_postCtx_eq]
  have h_init_not_finished : (initializeNeutralCtx sys params baseCtx h_seen_sound).finished = none := by
    simp only [initializeNeutralCtx];
    -- remove: exact h_baseCtx_not_finished
  rw [h_postCtx_eq] at h_not_finished
  exact liftBfsBigStepPropertiesAux sys baseCtx splitArrays
    (initializeNeutralCtx sys params baseCtx h_seen_sound) h_init_not_finished
    results h_not_finished item h_item_in_flatten l v h_tr




@[specialize]
def breadthFirstSearchParallel {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ] [Repr σ] [Repr σₕ] [Repr κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (parallelCfg : ParallelConfig)
  (progressInstanceId : Nat)
  (cancelToken : IO.CancelToken) :
  m (@ParallelSearchContextMain ρ σ κ σₕ fp _ _ th sys params) := do
  let mut ctx : @ParallelSearchContextMain ρ σ κ σₕ fp _ _ th sys params := ParallelSearchContextMain.initial sys params
  let mut lastUpdateTime : Nat := 0
  while h_not_finished : !ctx.hasFinished do
    let currentCtx := ctx
    -- In this setting, the queue emptiness check needs to be done here
    if h_tovisit_empty : ctx.tovisit.isEmpty then
      ctx := { ctx with
        finished := some (.exploredAllReachableStates),
        frontier_closed := by
          intro h_view_inj h_finished s h_in_seen h_not_in_tovisit l next_s h_tr
          have h_pre_no_terminate : ctx.finished = none := by unfold BaseSearchContext.hasFinished at h_not_finished;simp at h_not_finished; exact h_not_finished
          exact ctx.frontier_closed h_view_inj (by grind) s h_in_seen h_not_in_tovisit l next_s h_tr
        terminate_empty_tovisit := by intro h_finished_empty_tovisit; exact h_tovisit_empty
      }
      updateProgress progressInstanceId
        ctx.currentFrontierDepth ctx.statesFound ctx.seen.size ctx.tovisit.size
        (toActionStatsList ctx.actionStatsMap)
      return ctx
    else
      -- let _tovisitArr := ctx.tovisit
      -- let tovisitArr := _tovisitArr.toArray
      let tovisitArr := ctx.tovisit.toArray

      -- Explicitly compute chunk ranges for proof purposes
      -- Spawn tasks for each chunk range
      let ranges := ParallelConfig.chunkRanges parallelCfg tovisitArr.size
      let splitArrays := ranges.map (fun lr => tovisitArr.extract lr.1 lr.2)
      let baseCtx := ctx.toBaseSearchContext

      have h_baseCtx_not_finished : baseCtx.finished = none := by
        unfold BaseSearchContext.hasFinished at h_not_finished
        simp at h_not_finished; exact h_not_finished
      have h_baseCtx_seen_sound := ctx.invs.visited_sound

      -- Prove all items in tovisitArr are reachable
      have h_tovisitArr_reachable : ∀ item ∈ tovisitArr.toList, sys.reachable item.2.1 := by
        intro ⟨h, x, d⟩ h_mem
        have h_in_arr : (h, (x, d)) ∈ ctx.tovisit.toArray := Array.mem_toList_iff.mp h_mem
        have h_lookup : ctx.tovisit[h]? = some (x, d) :=
          HashMap.getElem?_of_mem_toArray ctx.tovisit h (x, d) h_in_arr
        have h_wf : h = fp.view x := ctx.invs.queue_wellformed h x d h_lookup
        rw [h_wf] at h_lookup
        exact ctx.invs.queue_sound x d h_lookup

      -- Prove elements in any extract are also reachable
      have h_extract_reachable : ∀ (lr : Nat × Nat), ∀ item ∈ (tovisitArr.extract lr.1 lr.2).toList,
          sys.reachable item.2.1 := by
        intro lr item h_mem
        have h_in_original : item ∈ tovisitArr.toList := by
          rw [Array.mem_toList_iff] at h_mem ⊢
          exact Array.mem_of_mem_extract tovisitArr lr.1 lr.2 item (by grind)
        exact h_tovisitArr_reachable item h_in_original

      -- Prove all sub-arrays in splitArrays have reachable items
      have h_splitArrays_sound : ∀ subArr ∈ splitArrays, ∀ item ∈ subArr.toList,
          sys.reachable item.2.1 := by
        intro subArr h_subArr_in item h_item_in
        obtain ⟨lr, _, h_subArr_eq⟩ := List.mem_map.mp h_subArr_in
        rw [← h_subArr_eq] at h_item_in
        exact h_extract_reachable lr item h_item_in

      let tasks ← IteratedProd.ofListMWithMem (as := splitArrays) fun subArr h_subArr_in => do
        have h_reachable : ∀ item ∈ subArr.toList, sys.reachable item.2.1 :=
          h_splitArrays_sound subArr h_subArr_in
        IO.asTask (ParallelSearchContextMerge.bfsBigStep sys baseCtx subArr h_baseCtx_seen_sound h_reachable)
        -- IO.eprintln s!"[{← IO.monoMsNow} @ tid {← IO.getTID}] spawned {tasks.length} tasks"
      let totalTasks := IteratedProd.foldl (init := 0) (fun acc _ => acc + 1) tasks
      IO.eprintln s!"[{← IO.monoMsNow} @ tid {← IO.getTID}] spawned {totalTasks} tasks"
      let results ← IteratedProd.mapM (fun task => IO.ofExcept task.get) tasks
      have t := results

      let aggregatedCtx := IteratedProd.foldl
        -- (init := ParallelSearchContextMerge.initialization sys params baseCtx)
        (init := initializeNeutralCtx sys params baseCtx h_baseCtx_seen_sound)
        (fun acc r => .Merge sys params baseCtx acc r.val) results

      -- Proof: ctx.finished = none (from while loop condition)
      have h_ctx_not_finished : ctx.finished = none := by
        unfold BaseSearchContext.hasFinished at h_not_finished
        simp at h_not_finished
        exact h_not_finished

      ctx := { ctx with
        seen := ctx.seen.union aggregatedCtx.localSeen,
        tovisit := aggregatedCtx.tovisit,
        log := ctx.log.union aggregatedCtx.localLog,
        completedDepth := ctx.currentFrontierDepth,
        currentFrontierDepth := ctx.currentFrontierDepth + 1,
        violatingStates := ctx.violatingStates ++ aggregatedCtx.violatingStates,
        finished := Option.or ctx.finished aggregatedCtx.finished,
        statesFound := ctx.statesFound + aggregatedCtx.localStatesFound,
        actionStatsMap := mergeActionStatsMaps ctx.actionStatsMap aggregatedCtx.localActionStatsMap,
        invs := by
          constructor
          · -- queue_sound: states in new tovisit (= aggregatedCtx.tovisit) are reachable
            intro x d h_in_tovisit
            exact aggregatedCtx.invs.queue_sound x d h_in_tovisit
          · -- visited_sound: states in new seen (= ctx.seen ∪ aggregatedCtx.localSeen) are reachable
            intro h_view_inj x h_in_new_seen
            simp only [Std.HashSet.mem_union] at h_in_new_seen
            cases h_in_new_seen with
            | inl h_in_ctx_seen =>
              exact ctx.invs.visited_sound h_view_inj x h_in_ctx_seen
            | inr h_in_localSeen =>
              -- x ∈ aggregatedCtx.localSeen implies x is reachable
              -- Use aggregatedCtx.invs.visited_sound with the fact that localSeen ⊆ (seen ∨ localSeen)
              have h_in_combined : fp.view x ∈ aggregatedCtx.seen ∨ fp.view x ∈ aggregatedCtx.localSeen :=
                Or.inr h_in_localSeen
              exact aggregatedCtx.invs.visited_sound h_view_inj x h_in_combined
          · -- queue_sub_visited: elements in tovisit have fingerprints in seen
            intro x d h_in_tovisit
            have h_sub := aggregatedCtx.invs.queue_sub_visited x d h_in_tovisit
            simp only [Std.HashSet.mem_union]
            -- h_sub : fp.view x ∈ aggregatedCtx.seen ∨ fp.view x ∈ aggregatedCtx.localSeen
            cases h_sub with
            | inl h_in_agg_seen =>
              -- aggregatedCtx.seen = baseCtx.seen = ctx.seen (via seenUnaltered)
              have h_eq := aggregatedCtx.seenUnaltered (fp.view x)
              -- h_eq : fp.view x ∈ baseCtx.seen ↔ fp.view x ∈ aggregatedCtx.seen
              -- We have h_in_agg_seen : fp.view x ∈ aggregatedCtx.seen
              -- We need: fp.view x ∈ ctx.seen, and baseCtx.seen = ctx.seen
              left; exact h_eq.mpr h_in_agg_seen
            | inr h_in_localSeen =>
              right; exact h_in_localSeen
          · -- queue_wellformed: fingerprints match states
            intro fingerprint st d h_in_tovisit
            exact aggregatedCtx.invs.queue_wellformed fingerprint st d h_in_tovisit
        frontier_closed := by
          intro h_view_inj h_finished s h_in_seen h_not_in_tovisit l next_s h_tr
          have h_pre_no_terminate : ctx.finished = none := by grind
          have h_baseCtx_not_finished : baseCtx.finished = none := h_pre_no_terminate
          have tt := liftBfsBigStepProperties sys baseCtx h_baseCtx_seen_sound /- h_baseCtx_not_finished-/
            splitArrays aggregatedCtx results (by rfl)
          -- Use merge_preserves_frontier_closed from ParallelLemmas
          -- We need: unionSeen = aggregatedCtx.localSeen, currTovisit = aggregatedCtx.tovisit
          have h_collect_all : ∀ (s' : σ) (d : Nat),
              ctx.tovisit[fp.view s']? = some (s', d) →
              (∀l' v, (l', .success v) ∈ (sys.tr th s')
                → ((fp.view v) ∈ ctx.seen ∨ (fp.view v) ∈ aggregatedCtx.localSeen)) := by
            intro s' d h_s'_in_old_tovisit l' v h_tr'
            -- Need to show: (fp.view v) ∈ ctx.seen ∨ (fp.view v) ∈ aggregatedCtx.localSeen
            -- From liftBfsBigStepProperties: if !aggregatedCtx.hasFinished,
            --   successors of items in splitArrays.flatten are in aggregatedCtx.seen ∨ aggregatedCtx.localSeen
            -- From aggregatedCtx.seenUnaltered: aggregatedCtx.seen = baseCtx.seen = ctx.seen
            have h_seen_eq : ∀ x, x ∈ aggregatedCtx.seen ↔ x ∈ ctx.seen := by
              intro x
              have h := aggregatedCtx.seenUnaltered x
              simp only [baseCtx] at h
              exact h.symm
            -- Show item is in splitArrays.flatten
            have h_item_in_flatten : (fp.view s', s', d) ∈ splitArrays.toArray.flatten := by
              have h_in_tovisitArr : (fp.view s', s', d) ∈ tovisitArr := by
                simp only [tovisitArr]
                exact HashMap.mem_toArray_of_getElem? ctx.tovisit (fp.view s') ⟨s', d⟩ h_s'_in_old_tovisit
              -- Step 2: Show element is in one of the subarrays
              simp only [splitArrays]
              have h_ranges_valid := ParallelConfig.chunkRanges_valid parallelCfg tovisitArr.size
              have h_ranges_cover := ParallelConfig.chunkRanges_cover parallelCfg tovisitArr.size
              exact Array.mem_flatten_of_partition tovisitArr ranges (fp.view s', s', d) h_in_tovisitArr h_ranges_cover h_ranges_valid
            by_cases h_agg_finished : aggregatedCtx.hasFinished
            · -- If aggregatedCtx has finished, we derive a contradiction from h_finished
              -- aggregatedCtx.finished can only be none or some (.earlyTermination _)
              -- (exploredAllReachableStates is only set at the outer BFS level, not in sub-contexts)
              -- But h_finished (with h_pre_no_terminate) says it must be
              -- some .exploredAllReachableStates or none
              simp [h_pre_no_terminate] at h_finished
              simp [BaseSearchContext.hasFinished] at h_agg_finished
              -- h_finished : aggregatedCtx.finished = some .exploredAllReachableStates ∨ aggregatedCtx.finished = none
              -- h_agg_finished : aggregatedCtx.finished.isSome
              cases h_finished with
              | inl h_explored =>
                -- aggregatedCtx.finished = some .exploredAllReachableStates
                -- This cannot happen: sub-context merge only propagates earlyTermination
                exact absurd h_explored aggregatedCtx.excludeAllStatesFinish
              | inr h_none =>
                -- aggregatedCtx.finished = none contradicts h_agg_finished
                simp [h_none] at h_agg_finished
            · -- aggregatedCtx has not finished, use liftBfsBigStepProperties
              have h_not_finished_bool : !aggregatedCtx.hasFinished := by simp [h_agg_finished]
              have h_succ := tt h_not_finished_bool (fp.view s', s', d) h_item_in_flatten l' v h_tr'
              cases h_succ with
              | inl h_in_agg_seen =>
                left
                rw [h_seen_eq] at h_in_agg_seen
                exact h_in_agg_seen
              | inr h_in_localSeen =>
                right
                exact h_in_localSeen
          -- Now apply merge_preserves_frontier_closed
          exact ParallelSearchContextMain.merge_preserves_frontier_closed sys params ctx
            aggregatedCtx.localSeen aggregatedCtx.tovisit h_pre_no_terminate h_view_inj
            aggregatedCtx.deltaConsistent h_collect_all s h_in_seen h_not_in_tovisit l next_s h_tr
        terminate_empty_tovisit := by
          have h_pre_no_terminate : ctx.finished = none := by
            simp at h_not_finished;
            grind
          have h_aggr_not_explore := aggregatedCtx.excludeAllStatesFinish
          grind
      }


      -- If we found a violation, mark it so handoff is prevented
      if let some (.earlyTermination cond) := ctx.finished then
        if EarlyTerminationReason.isViolation cond then setViolationFound progressInstanceId
      -- Update progress and check for cancellation/handoff at most once per second
      let now ← IO.monoMsNow
      if now - lastUpdateTime >= 1000 then
        lastUpdateTime := now
        -- TLC-style stats: diameter, statesFound, distinctStates, queue, actionStats
        updateProgress progressInstanceId
          ctx.currentFrontierDepth ctx.statesFound ctx.seen.size ctx.tovisit.size
          (toActionStatsList ctx.actionStatsMap)
        if ← shouldStop cancelToken progressInstanceId then
          ctx := { ctx with
            finished := some (.earlyTermination .cancelled),
            frontier_closed := by intro h_view_inj h_finished _ ; simp at h_finished
            terminate_empty_tovisit := by intro h_finished_empty_tovisit; simp at h_finished_empty_tovisit}
          break
  -- Final update to ensure stats reflect finished state
  updateProgress progressInstanceId
    ctx.currentFrontierDepth ctx.statesFound ctx.seen.size ctx.tovisit.size
    (toActionStatsList ctx.actionStatsMap)
  return ctx

end Veil.ModelChecker.Concrete
