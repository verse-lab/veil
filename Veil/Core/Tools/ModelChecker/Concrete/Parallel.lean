import Veil.Core.Tools.ModelChecker.Concrete.Progress
import Veil.Core.Tools.ModelChecker.Concrete.ParallelLemmas

namespace Veil.ModelChecker.Concrete


/-- Merge action stats maps by summing counts for each action. -/
private def mergeActionStatsMaps [BEq κ] [Hashable κ] (m1 m2 : Std.HashMap κ ActionStat) : Std.HashMap κ ActionStat :=
  m2.fold (init := m1) fun acc label stat2 =>
    match acc[label]? with
    | some stat1 => acc.insert label { statesGenerated := stat1.statesGenerated + stat2.statesGenerated, distinctStates := stat1.distinctStates + stat2.distinctStates }
    | none => acc.insert label stat2


/-- Helper: foldl push over list produces array with same toList as map -/
private theorem foldl_push_toList_eq_map {α β : Type} (f : α → β) (xs : List α) :
  (xs.foldl (fun acc x => acc.push (f x)) #[]).toList = xs.map f := by
  suffices ∀ (acc : Array β), (xs.foldl (fun acc x => acc.push (f x)) acc).toList = acc.toList ++ xs.map f by
    simpa using this #[]
  induction xs with
  | nil => simp
  | cons hd tl ih =>
    intro acc
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp only [Array.toList_push, List.append_assoc, List.singleton_append]

/-- Helper: membership in foldl insert is characterized by list membership -/
private theorem foldl_insert_mem_iff {α : Type} [BEq α] [Hashable α] [LawfulBEq α] (xs : List α) (h : α)
  (init : Std.HashSet α) :
  h ∈ xs.foldl (fun acc x => acc.insert x) init ↔ h ∈ init ∨ h ∈ xs := by
  induction xs generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih]
    constructor
    · intro h_or
      rcases h_or with h_in_insert | h_in_tl
      · rw [Std.HashSet.mem_insert] at h_in_insert
        rcases h_in_insert with h_eq_hd | h_in_init
        · right; left; exact (LawfulBEq.eq_of_beq h_eq_hd).symm
        · left; exact h_in_init
      · right; right; exact h_in_tl
    · intro h_or
      rcases h_or with h_in_init | (h_eq_hd | h_in_tl)
      · left; rw [Std.HashSet.mem_insert]; right; exact h_in_init
      · left; rw [Std.HashSet.mem_insert]; left; subst h_eq_hd; exact BEq.refl _
      · right; exact h_in_tl

/-- Helper: foldl insert over list equals insertMany for membership -/
private theorem foldl_insert_mem_iff_insertMany_mem {α : Type} [BEq α] [Hashable α] [LawfulBEq α] (xs : List α) (h : α) :
  h ∈ xs.foldl (fun acc x => acc.insert x) Std.HashSet.emptyWithCapacity ↔
  h ∈ Std.HashSet.insertMany Std.HashSet.emptyWithCapacity xs := by
  rw [foldl_insert_mem_iff, Std.HashSet.mem_insertMany_list]
  simp only [Std.HashSet.not_mem_emptyWithCapacity, false_or]
  constructor
  · intro h_mem; exact List.elem_eq_true_of_mem h_mem
  · intro h_contains; exact List.mem_of_elem_eq_true h_contains

/-- Helper: foldl insert over mapped list, for membership -/
private theorem foldl_insert_map_mem_iff {α β : Type} [BEq β] [Hashable β] [LawfulBEq β]
  (f : α → β) (xs : List α) (h : β) :
  h ∈ xs.foldl (fun acc x => acc.insert (f x)) Std.HashSet.emptyWithCapacity ↔
  h ∈ (xs.map f).foldl (fun acc x => acc.insert x) Std.HashSet.emptyWithCapacity := by
  suffices ∀ (acc : Std.HashSet β),
    h ∈ xs.foldl (fun acc x => acc.insert (f x)) acc ↔
    h ∈ (xs.map f).foldl (fun acc x => acc.insert x) acc by
    exact this _
  induction xs with
  | nil => simp
  | cons hd tl ih =>
    intro acc
    simp only [List.foldl_cons, List.map_cons]
    exact ih _

def ParallelSearchContext.initial {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ] {th : ρ}
  (sys : _) (params : SearchParameters ρ σ) :
  @ParallelSearchContext ρ σ κ σₕ fp _ _ th sys params := {
    BaseSearchContext.initial sys params with
    tovisitQueue := sys.initStates.foldl (fun acc s =>
      acc.push ⟨fp.view s, s, 0⟩) #[]
    tovisitSet := sys.initStates.foldl (fun acc s =>
      acc.insert (fp.view s)) Std.HashSet.emptyWithCapacity
    tovisitConsistent := by
      intro h
      have h_queue_eq := foldl_push_toList_eq_map (fun s => (⟨fp.view s, s, 0⟩ : QueueItem σₕ σ)) sys.initStates
      constructor
      · -- h ∈ tovisitSet → ∃ item ∈ tovisitQueue, item.fingerprint = h
        intro h_in_set
        -- h is in the set, so it came from some init state
        have h_in_list : h ∈ sys.initStates.map fp.view := by
          rw [foldl_insert_map_mem_iff, foldl_insert_mem_iff_insertMany_mem] at h_in_set
          exact Std.HashSet.mem_list_of_mem_insertMany h_in_set
        simp only [List.mem_map] at h_in_list
        obtain ⟨s, h_s_in_init, h_eq⟩ := h_in_list
        -- The corresponding item is in the queue
        use (⟨fp.view s, s, 0⟩ : QueueItem σₕ σ)
        constructor
        · -- Show ⟨fp.view s, s, 0⟩ ∈ tovisitQueue
          rw [Array.mem_def, h_queue_eq, List.mem_map]
          exact ⟨s, h_s_in_init, rfl⟩
        · exact h_eq
      · -- ∃ item ∈ tovisitQueue, item.fingerprint = h → h ∈ tovisitSet
        intro ⟨item, h_in_queue, h_fp_eq⟩
        rw [Array.mem_def, h_queue_eq, List.mem_map] at h_in_queue
        obtain ⟨s, h_s_in_init, h_item_eq⟩ := h_in_queue
        rw [← h_item_eq] at h_fp_eq
        simp only at h_fp_eq
        rw [← h_fp_eq]
        rw [foldl_insert_map_mem_iff, foldl_insert_mem_iff_insertMany_mem]
        apply Std.HashSet.mem_insertMany_of_mem_list
        simp only [List.mem_map]
        exact ⟨s, h_s_in_init, rfl⟩
    invs := by
      have h_queue_eq := foldl_push_toList_eq_map (fun s => (⟨fp.view s, s, 0⟩ : QueueItem σₕ σ)) sys.initStates
      constructor
      · -- queue_sound: all states in tovisitQueue are reachable
        intro x d h_in_tovisit
        rw [Array.mem_def, h_queue_eq, List.mem_map] at h_in_tovisit
        obtain ⟨s, h_s_in_init, h_eq⟩ := h_in_tovisit
        have h_x_eq : x = s := by simp only [QueueItem.mk.injEq] at h_eq; exact h_eq.2.1.symm
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
      · -- queue_sub_visited: elements in tovisitQueue have fingerprints in seen
        intro x d h_in_tovisit
        unfold BaseSearchContext.initial
        rw [Array.mem_def, h_queue_eq, List.mem_map] at h_in_tovisit
        obtain ⟨s, h_s_in_init, h_eq⟩ := h_in_tovisit
        have h_fp_eq : fp.view s = fp.view x := by simp only [QueueItem.mk.injEq] at h_eq; exact h_eq.1
        rw [← h_fp_eq]
        apply Std.HashSet.mem_insertMany_of_mem_list
        simp only [Functor.map, List.mem_map]
        exact ⟨s, h_s_in_init, rfl⟩
      · -- queue_wellformed: fingerprints match states in tovisitQueue
        intro fingerprint st d h_in_tovisit
        rw [Array.mem_def, h_queue_eq, List.mem_map] at h_in_tovisit
        obtain ⟨s, h_s_in_init, h_eq⟩ := h_in_tovisit
        simp only [QueueItem.mk.injEq] at h_eq
        rw [← h_eq.1, ← h_eq.2.1]
    frontier_closed := by
      intro h_view_inj h_finished s h_in_seen h_not_in_tovisit l next_s h_tr
      unfold BaseSearchContext.initial at h_in_seen
      have h_in_list := Std.HashSet.mem_list_of_mem_insertMany h_in_seen
      simp only [Functor.map, List.mem_map] at h_in_list
      obtain ⟨init_s, h_s_in_init, h_view_eq⟩ := h_in_list
      rw [← h_view_eq] at h_not_in_tovisit
      -- init_s is in initStates, so fp.view init_s should be in tovisitSet
      have h_in_set : fp.view init_s ∈ sys.initStates.foldl (fun acc s => acc.insert (fp.view s)) Std.HashSet.emptyWithCapacity := by
        rw [foldl_insert_map_mem_iff, foldl_insert_mem_iff_insertMany_mem]
        apply Std.HashSet.mem_insertMany_of_mem_list
        simp only [List.mem_map]
        exact ⟨init_s, h_s_in_init, rfl⟩
      exact absurd h_in_set h_not_in_tovisit
    terminate_empty_tovisit := by
      intro h_finished_empty_tovisit
      dsimp only [BaseSearchContext.initial] at h_finished_empty_tovisit
      grind
    starts_in_seen := by
      intro s0 h_s0_in_init
      simp only [BaseSearchContext.initial]
      apply Std.HashSet.mem_insertMany_of_mem_list
      show fp.view s0 ∈ List.map fp.view sys.initStates
      simp only [List.mem_map]
      exact ⟨s0, h_s0_in_init, rfl⟩
  }


@[inline, specialize]
def LocalSearchContext.tryExploreNeighbor {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ] [Repr κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (fpSt : σₕ)      -- fingerprint of state we're coming from (pre-state), for logging
  (depth : Nat)    -- depth of the current state (neighbor will be at depth + 1)
  (ctx : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (neighbor : κ × σ)
  (h_neighbor : sys.reachable neighbor.2)
  (h_not_finished : !ctx.hasFinished)
: {ctx' : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx //
    ctx'.finished = ctx.finished ∧
    (∀fp, fp ∈ ctx.tovisitSet → fp ∈ ctx'.tovisitSet) ∧
    (ctx'.seen.contains (fp.view neighbor.2) ∨ ctx'.tovisitSet.contains (fp.view neighbor.2))  } :=
  let ⟨label, succ⟩ := neighbor
  let fingerprint := fp.view succ
  have h_succ_reachable : sys.reachable succ := h_neighbor
  if h_has_seen : ctx.seen.contains fingerprint || ctx.tovisitSet.contains fingerprint then
    ⟨ctx, by constructor <;> grind⟩
  else
    have h_not_in_seen : !ctx.seen.contains fingerprint := by simp at h_has_seen ⊢; exact h_has_seen.1
    have h_not_in_tovisitSet : !ctx.tovisitSet.contains fingerprint := by simp at h_has_seen ⊢; exact h_has_seen.2
    let newActionStatsMap := match ctx.localActionStatsMap[label]? with
      | some stat => ctx.localActionStatsMap.insert label { stat with distinctStates := stat.distinctStates + 1 }
      | none => ctx.localActionStatsMap.insert label { statesGenerated := 0, distinctStates := 1 }
    ⟨{ctx with
      tovisitQueue := ctx.tovisitQueue.push ⟨fingerprint, succ, depth + 1⟩,
      tovisitSet := ctx.tovisitSet.insert fingerprint,
      localLog  := ctx.localLog.insert fingerprint (fpSt, label),
      localActionStatsMap := newActionStatsMap,
      tovisitConsistent := LocalSearchContext.push_insert_preserves_tovisitConsistent ctx fingerprint succ depth,
      invs := LocalSearchContext.insert_and_enqueue_preserves_invs sys params ctx fingerprint succ depth h_succ_reachable rfl
    }, (by constructor <;> grind)⟩


-- Helper function: recursively process successors with explicit induction structure
-- Modified to only require that all successors come from sys.tr th curr (subset property)
@[inline, specialize]
def LocalSearchContext.processSuccessors {ρ σ κ σₕ : Type}
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
  (ctx : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (h_not_finished : !ctx.hasFinished)
  : {ctx' : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx //
      (∀ (l : κ) (v : σ), (l, v) ∈ successors → (fp.view v) ∈ ctx'.seen ∨ (fp.view v) ∈ ctx'.tovisitSet) ∧
      (∀ fp_elem, fp_elem ∈ ctx.tovisitSet → fp_elem ∈ ctx'.tovisitSet) } :=
  match successors with
  | [] => ⟨ctx, by constructor <;> grind⟩
  | (label, state) :: rest =>
    have h_in_sys_tr : (label, .success state) ∈ sys.tr th curr := by
      have h_in_extracted : (label, state) ∈ extractSuccessfulTransitions (sys.tr th curr) := by grind
      unfold extractSuccessfulTransitions at h_in_extracted;grind
    have h_next : sys.next curr state := ⟨label, h_in_sys_tr⟩
    have h_neighbor_reachable : sys.reachable state := EnumerableTransitionSystem.reachable.step curr state h_curr h_next
    /- `Function Call` -/
    let neighbor_result := LocalSearchContext.tryExploreNeighbor sys fpSt depth ctx ⟨label, state⟩ h_neighbor_reachable h_not_finished
    have h_current_in_seen := neighbor_result.property.2.2
    have h_finished_preserved := neighbor_result.property.1
    have h_still_not_finished : !neighbor_result.val.hasFinished := by
      unfold BaseSearchContext.hasFinished at h_not_finished ⊢; rw [h_finished_preserved]; exact h_not_finished
    have h_rest_subset : ∀ x, x ∈ rest → x ∈ extractSuccessfulTransitions (sys.tr th curr) := by
      intro x h_x_in_rest; apply h_succ_subset; exact List.mem_cons_of_mem (label, state) h_x_in_rest
    /- `Recursive Call` -/
    let rest_result := processSuccessors sys curr fpSt depth h_curr _ h_rest_subset neighbor_result.val h_still_not_finished
    have h_rest_completeness := rest_result.property.1
    have h_rest_tovisitSet_mono := rest_result.property.2
    have h_current_tovisitSet_mono := neighbor_result.property.2.1
    ⟨rest_result.val,
      processSuccessors_cons_step _ _ _ _ _ _ _
        h_current_tovisitSet_mono h_current_in_seen
        h_rest_completeness h_rest_tovisitSet_mono⟩
termination_by successors.length


@[inline, specialize]
def ParallelSearchContextSub.processState {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ] [Repr σ] [Repr σₕ] [Repr κ]
  {th : ρ}
  (sys : _)
  {params : SearchParameters ρ σ}
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (fpSt : σₕ)
  (depth : Nat)
  (curr : σ)
  (h_curr : sys.reachable curr)
  (ctx : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx) :
  {ctx' : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx //
    (∀ x, x ∈ ctx.tovisitSet → x ∈ ctx'.tovisitSet) ∧ -- 1. Monotonicity
    (!ctx'.hasFinished → ∀l v, (l, v) ∈ extractSuccessfulTransitions (sys.tr th curr) →
    (fp.view v) ∈ ctx'.seen ∨ (fp.view v) ∈ ctx'.tovisitSet)} := -- 2. Completeness
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
      let ctx' : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx := { ctx with
        toBaseSearchContext := baseCtx'
        excludeAllStatesFinish := by unfold BaseSearchContext.processState at h_process; simp only at h_process; grind
        seenUnaltered := by intro s; rw [h_seen_unchanged]; exact ctx.seenUnaltered s
        invs := SearchContextInvariants.preserved_when_seen_unchanged sys params ctx.tovisitQueue ctx.seen baseCtx'.seen ctx.tovisitSet h_seen_unchanged ctx.invs
      }
      have h_ctx'_finished : ctx'.hasFinished := by simp only [ctx']; exact h_early_terminate
      ⟨ctx', processState_none_subtype sys ctx ctx' curr rfl h_ctx'_finished⟩
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

      let ctx_updated : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx :=
      { ctx with
        toBaseSearchContext := baseCtx'
        seenUnaltered := by intro s; rw [h_seen_unchanged]; exact ctx.seenUnaltered s
        localStatesFound := newLocalStatesFound
        localActionStatsMap := newLocalActionStatsMap
        excludeAllStatesFinish := by simp at h_not_finished; simp [h_not_finished]
        invs := by
          have h_process_fst : (ctx.toBaseSearchContext.processState sys fpSt curr).1 = baseCtx' := by
            rw [h_process]
          exact LocalSearchContext.update_base_after_processState_preserves_invs sys ctx fpSt curr baseCtx' h_process_fst
      }
      have h_ctx_updated_tovisitSet_eq : ctx_updated.tovisitSet = ctx.tovisitSet := rfl
      have h_ctx_updated_not_finished : !ctx_updated.hasFinished := by simp only [ctx_updated]; exact h_not_finished
      /-`Function Call`-/
      let res := LocalSearchContext.processSuccessors sys curr fpSt depth h_curr successfulTransitions (by grind) ctx_updated h_ctx_updated_not_finished
      have h_res_completeness := res.property.1
      have h_res_tovisitSet_mono := res.property.2
      ⟨res.val, by
        refine ⟨?mono, ?complete⟩
        · intro x h_in_ctx
          rw [← h_ctx_updated_tovisitSet_eq] at h_in_ctx
          exact h_res_tovisitSet_mono x h_in_ctx
        · grind
      ⟩


@[inline, specialize]
def LocalSearchContext.processWorkQueue {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ] [Repr σ] [Repr σₕ] [Repr κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  {baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params}
  (queueList : List (σₕ × σ × Nat))
  (h_reachable : ∀ q ∈ queueList, sys.reachable q.2.1)
  (ctx : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx)
  : {ctx' : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx //
      SuccessorsCollected sys (fun ⟨h, st, d⟩ => (h, st, d) ∈ queueList) ctx'.hasFinished (fun h => h ∈ ctx'.seen ∨ h ∈ ctx'.tovisitSet) ∧
      (∀ fp_elem, fp_elem ∈ ctx.tovisitSet → fp_elem ∈ ctx'.tovisitSet) } :=
  match queueList with
  | [] => ⟨ctx, by constructor <;> grind⟩
  | item :: rest =>
    let ⟨fpSt, curr, depth⟩ := item
    have h_curr_reachable : sys.reachable curr :=
      h_reachable (fpSt, curr, depth) List.mem_cons_self
    let ⟨next_ctx, h_next_props⟩ := ParallelSearchContextSub.processState sys fpSt depth curr h_curr_reachable ctx
    if h_next_finished : next_ctx.hasFinished then ⟨next_ctx, by grind⟩
    else
      have h_next_not_finished : !next_ctx.hasFinished := by grind
      have h_rest_subset : ∀ x ∈ rest, sys.reachable x.2.1 := by intro x hx; apply h_reachable; exact List.mem_cons_of_mem _ hx
      let rest_result := processWorkQueue sys rest h_rest_subset next_ctx
      ⟨rest_result.val, processWorkQueue_cons_step _ _ _ _ _ _ _ _
        h_next_not_finished h_next_props.1 h_next_props.2 rest_result.property.1 rest_result.property.2⟩
termination_by queueList.length


@[inline, specialize]
def LocalSearchContext.Merge {ρ σ σₕ κ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ] {th : ρ}
  (sys : _) (params : _)
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (ctx1 ctx2 : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx) :
  @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx :=
  -- Filter ctx2's queue to only include items not already in ctx1's set
  let filteredQueue := ctx2.tovisitQueue.filter fun item => !ctx1.tovisitSet.contains item.fingerprint
  {
    ctx1 with
    seen := ctx1.seen.union ctx2.seen,
    localLog := ctx1.localLog.union ctx2.localLog,
    violatingStates := ctx2.violatingStates ++ ctx1.violatingStates,
    finished := Option.or ctx1.finished ctx2.finished
    tovisitQueue := ctx1.tovisitQueue ++ filteredQueue
    tovisitSet := ctx1.tovisitSet.union ctx2.tovisitSet
    localStatesFound := ctx1.localStatesFound + ctx2.localStatesFound,
    localActionStatsMap := mergeActionStatsMaps ctx1.localActionStatsMap ctx2.localActionStatsMap
    tovisitConsistent := merge_local_local_preserves_tovisitConsistent sys params ctx1 ctx2
    invs := merge_local_local_preserves_invs sys params ctx1 ctx2
    excludeAllStatesFinish := merge_local_local_excludes_exploredAll sys params ctx1 ctx2
    seenUnaltered := merge_local_local_preserves_seenUnaltered sys params ctx1 ctx2
  }


def LocalSearchContext.NeutralContext {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : _) (params : _)
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (h_seen_sound : Function.Injective fp.view → ∀ (x : σ), fp.view x ∈ baseCtx.seen → sys.reachable x)
  : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx := {
    toBaseSearchContext := { baseCtx with finished := none},
    tovisitQueue := #[],
    tovisitSet := Std.HashSet.emptyWithCapacity,
    localLog := Std.HashMap.emptyWithCapacity,
    localStatesFound := 0,
    localActionStatsMap := Std.HashMap.emptyWithCapacity,
    tovisitConsistent := by simp [Std.HashSet.not_mem_emptyWithCapacity, Array.not_mem_empty]
    invs := by constructor <;> simp_all [Array.not_mem_empty, Std.HashSet.not_mem_emptyWithCapacity]
    excludeAllStatesFinish := by simp
    seenUnaltered := by simp
  }


@[inline, specialize]
def LocalSearchContext.bfsBigStep {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ] [Repr σ] [Repr σₕ] [Repr κ]
  {th : ρ}
  (sys : _) {params : SearchParameters ρ σ}
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (queue : Array (σₕ × σ × Nat))
  (h_seen_sound : Function.Injective fp.view → ∀ (x : σ), fp.view x ∈ baseCtx.seen → sys.reachable x)
  (h_reachable : ∀ item ∈ queue.toList, sys.reachable item.2.1)
  : m ( {ctx' : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx //
    SuccessorsCollected sys (fun ⟨h, st, d⟩ => (h, st, d) ∈ queue) ctx'.hasFinished (fun h => h ∈ ctx'.seen ∨ h ∈ ctx'.tovisitSet)})
  := do
  let ctx := NeutralContext sys params baseCtx h_seen_sound
  -- let startTime ← IO.monoMsNow
  let result := processWorkQueue sys queue.toList h_reachable ctx
  -- let endTime ← IO.monoMsNow
  -- IO.eprintln s!"[{endTime} @ tid {← IO.getTID}] took {endTime - startTime}ms to process {queue.size} states (queue size now: {result.val.tovisit.size})"
  pure ⟨result.val, by
    intro h_not_finished fingerprint st d h_item_in_queue l v h_tr
    simp only at h_item_in_queue
    have h_item_in_list : (fingerprint, st, d) ∈ queue.toList := Array.mem_toList_iff.mpr h_item_in_queue
    exact result.property.1 h_not_finished fingerprint st d h_item_in_list l v h_tr ⟩


-- Helper lemma: foldl preserves seenUnaltered (seen = baseCtx.seen after merge)
theorem IteratedProd.foldl_merge_seen_unaltered {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ] {th : ρ}
  (sys : _) (params : _)
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  {splitArrays : List (Array (σₕ × σ × Nat))}
  (init : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (results : IteratedProd (List.map (fun (x : Array (σₕ × σ × Nat)) => { ctx' : LocalSearchContext sys params baseCtx //
    SuccessorsCollected sys (fun ⟨h, st, d⟩ => (h, st, d) ∈ x) ctx'.hasFinished (fun h => h ∈ ctx'.seen ∨ h ∈ ctx'.tovisitSet) })
    splitArrays))
  (x : σₕ) :
  x ∈ baseCtx.seen ↔ x ∈ (IteratedProd.foldl init (fun acc r => .Merge sys params baseCtx acc r.val) results).seen := by
  induction splitArrays generalizing init with
  | nil => exact init.seenUnaltered x
  | cons arr rest ih =>
    obtain ⟨headRes, tailRes⟩ := results
    simp only [IteratedProd.foldl]
    have h_ih := ih (LocalSearchContext.Merge sys params baseCtx init headRes.val) tailRes
    exact h_ih


-- Helper lemma: foldl preserves seen membership (from any merged context)
theorem IteratedProd.foldl_merge_preserves_seen {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ] {th : ρ}
  (sys : _) (params : _)
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  {splitArrays : List (Array (σₕ × σ × Nat))}
  (init : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (results : IteratedProd (List.map (fun (x : Array (σₕ × σ × Nat)) => { ctx' : LocalSearchContext sys params baseCtx //
    SuccessorsCollected sys (fun ⟨h, st, d⟩ => (h, st, d) ∈ x) ctx'.hasFinished (fun h => h ∈ ctx'.seen ∨ h ∈ ctx'.tovisitSet) })
    splitArrays))
  (x : σₕ) (h : x ∈ init.seen) :
  x ∈ (IteratedProd.foldl init (fun acc r => .Merge sys params baseCtx acc r.val) results).seen := by
  induction splitArrays generalizing init with
  | nil => exact h
  | cons arr rest ih =>
    obtain ⟨headRes, tailRes⟩ := results
    simp only [IteratedProd.foldl]
    apply ih
    simp only [LocalSearchContext.Merge, Std.HashSet.mem_union]
    left; exact h


-- Helper lemma: foldl preserves tovisitSet membership (from any merged context)
theorem IteratedProd.foldl_merge_preserves_tovisitSet {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ] {th : ρ}
  (sys : _) (params : _)
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  {splitArrays : List (Array (σₕ × σ × Nat))}
  (init : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (results : IteratedProd (List.map (fun (x : Array (σₕ × σ × Nat)) => { ctx' : LocalSearchContext sys params baseCtx //
    SuccessorsCollected sys (fun ⟨h, st, d⟩ => (h, st, d) ∈ x) ctx'.hasFinished (fun h => h ∈ ctx'.seen ∨ h ∈ ctx'.tovisitSet) })
    splitArrays))
  (x : σₕ) (h : x ∈ init.tovisitSet) :
  x ∈ (IteratedProd.foldl init (fun acc r => .Merge sys params baseCtx acc r.val) results).tovisitSet := by
  induction splitArrays generalizing init with
  | nil => exact h
  | cons arr rest ih =>
    obtain ⟨headRes, tailRes⟩ := results
    simp only [IteratedProd.foldl]
    apply ih
    simp only [LocalSearchContext.Merge, Std.HashSet.mem_union]
    left; exact h

-- Helper: foldl Merge preserves hasFinished = true
theorem IteratedProd.foldl_merge_preserves_has_finished {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ] {th : ρ}
  (sys : _) (params : _)
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (rest : List (Array (σₕ × σ × Nat)))
  (init : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx)
  (tailRes : IteratedProd (List.map (fun (x : Array (σₕ × σ × Nat)) => { ctx' : LocalSearchContext sys params baseCtx //
    SuccessorsCollected sys (fun ⟨h, st, d⟩ => (h, st, d) ∈ x) ctx'.hasFinished (fun h => h ∈ ctx'.seen ∨ h ∈ ctx'.tovisitSet) }) rest))
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
    simp only [LocalSearchContext.Merge, BaseSearchContext.hasFinished, Option.isSome_or]
    simp only [BaseSearchContext.hasFinished] at h_init_finished
    simp only [h_init_finished, Bool.true_or]


-- Helper lemma: if foldl result is not finished, then the first merged context's second arg is not finished
theorem IteratedProd.foldl_merge_not_finished_head {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ] {th : ρ}
  (sys : _) (params : _)
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (init : LocalSearchContext sys params baseCtx)
  {arr : Array (σₕ × σ × Nat)} {rest : List (Array (σₕ × σ × Nat))}
  (headRes : { ctx' : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx //
    SuccessorsCollected sys (fun ⟨h, st, d⟩ => (h, st, d) ∈ arr) ctx'.hasFinished (fun h => h ∈ ctx'.seen ∨ h ∈ ctx'.tovisitSet) })
  (tailRes : IteratedProd (List.map (fun (x : Array (σₕ × σ × Nat)) => { ctx' : LocalSearchContext sys params baseCtx //
    SuccessorsCollected sys (fun ⟨h, st, d⟩ => (h, st, d) ∈ x) ctx'.hasFinished (fun h => h ∈ ctx'.seen ∨ h ∈ ctx'.tovisitSet) }) rest))
  (h_init_not_finished : init.finished = none)
  (h : !(IteratedProd.foldl
    (LocalSearchContext.Merge sys params baseCtx init headRes.val)
    (fun acc r => .Merge sys params baseCtx acc r.val) tailRes).hasFinished) :
  !headRes.val.hasFinished := by
  by_contra h_finished
  simp only [Bool.not_eq_true] at h_finished
  have h_head_finished : headRes.val.hasFinished = true := by
    cases h_eq : headRes.val.hasFinished with
    | true => rfl
    | false => simp only [h_eq, Bool.not_false] at h_finished; cases h_finished
  have h_merge_finished : (LocalSearchContext.Merge sys params baseCtx init headRes.val).hasFinished := by
    simp only [LocalSearchContext.Merge, BaseSearchContext.hasFinished, Option.isSome_or]
    simp only [BaseSearchContext.hasFinished] at h_head_finished
    simp only [h_init_not_finished, Option.isSome_none, Bool.false_or]
    exact h_head_finished
  -- Now show that foldl preserves hasFinished = true
  have h_foldl_finished : (IteratedProd.foldl
    (LocalSearchContext.Merge sys params baseCtx init headRes.val)
    (fun acc r => .Merge sys params baseCtx acc r.val) tailRes).hasFinished :=
    IteratedProd.foldl_merge_preserves_has_finished sys params baseCtx rest
      (.Merge sys params baseCtx init headRes.val) tailRes h_merge_finished
  simp only [h_foldl_finished, Bool.not_true] at h
  grind



-- Proves that merging parallel BFS results preserves successor collection property.
-- Generalized version that works with any initial context.
theorem foldl_merge_preserves_successors_collected {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : _)
  {params : SearchParameters ρ σ}
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (splitArrays : List (Array (σₕ × σ × Nat)))
  (init : LocalSearchContext sys params baseCtx)
  (h_init_not_finished : init.finished = none)
  (results : IteratedProd (List.map (fun (x : Array (σₕ × σ × Nat)) => { ctx' : @LocalSearchContext ρ σ κ σₕ fp _ _ th sys params baseCtx //
    SuccessorsCollected sys (fun ⟨h, st, d⟩ => (h, st, d) ∈ x) ctx'.hasFinished (fun h => h ∈ ctx'.seen ∨ h ∈ ctx'.tovisitSet) })
    splitArrays))
  (h_not_finished : !(IteratedProd.foldl init (fun acc r => .Merge sys params baseCtx acc r.val) results).hasFinished)
  (item : σₕ × σ × Nat) (h_item_in_flatten : item ∈ splitArrays.toArray.flatten)
  (l : κ) (v : σ) (h_tr : (l, .success v) ∈ sys.tr th item.2.1) :
  (fp.view v) ∈ baseCtx.seen ∨
  (fp.view v) ∈ (IteratedProd.foldl init (fun acc r => .Merge sys params baseCtx acc r.val) results).tovisitSet := by
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
        IteratedProd.foldl_merge_not_finished_head sys params baseCtx init headRes tailRes h_init_not_finished h_not_finished
      have h_succ := h_headRes_prop h_head_not_finished _ _ _ h_in_arr l v h_tr
      cases h_succ with
      | inl h_in_seen =>
        -- h_in_seen : fp.view v ∈ headRes.val.seen
        -- By seenUnaltered, headRes.val.seen = baseCtx.seen
        left
        exact (headRes.val.seenUnaltered (fp.view v)).mpr h_in_seen
      | inr h_in_tovisitSet =>
        right
        apply IteratedProd.foldl_merge_preserves_tovisitSet
        simp only [LocalSearchContext.Merge, Std.HashSet.mem_union]
        right; exact h_in_tovisitSet
    | inr h_in_rest =>
      -- item is in rest, apply IH with init' = Merge init headRes.val
      have h_init'_not_finished : (LocalSearchContext.Merge sys params baseCtx init headRes.val).finished = none := by
        simp only [LocalSearchContext.Merge]
        simp only [h_init_not_finished, Option.none_or]
        by_contra h_head_fin
        have h_head_finished : headRes.val.hasFinished := by
          simp only [BaseSearchContext.hasFinished, Option.isSome_iff_ne_none]
          exact h_head_fin
        have h_head_not_finished : !headRes.val.hasFinished :=
          IteratedProd.foldl_merge_not_finished_head sys params baseCtx init headRes tailRes h_init_not_finished h_not_finished
        simp only [h_head_finished, Bool.not_true] at h_head_not_finished
        cases h_head_not_finished
      exact ih (LocalSearchContext.Merge sys params baseCtx init headRes.val)
        h_init'_not_finished tailRes h_not_finished h_in_rest


-- Proves that aggregating parallel BFS results collects all successors.
-- Specialized version starting from NeutralContext.
theorem parallel_bfs_successors_collected {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : _)
  {params : SearchParameters ρ σ}
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (h_seen_sound : Function.Injective fp.view → ∀ (x : σ), fp.view x ∈ baseCtx.seen → sys.reachable x)
  (splitArrays : List (Array (σₕ × σ × Nat)))
  (postCtx : LocalSearchContext sys params baseCtx)
  (results : IteratedProd (List.map (fun (x : Array (σₕ × σ × Nat)) => { ctx' : LocalSearchContext sys params baseCtx //
    SuccessorsCollected sys (fun ⟨h, st, d⟩ => (h, st, d) ∈ x) ctx'.hasFinished (fun h => h ∈ ctx'.seen ∨ h ∈ ctx'.tovisitSet) })
    splitArrays))
  (h_postCtx_eq : postCtx = IteratedProd.foldl
    (init := .NeutralContext sys params baseCtx h_seen_sound)
    (fun acc r => .Merge sys params baseCtx acc r.val) results) :
  -- (!postCtx.hasFinished →
  --   ∀ item ∈ splitArrays.toArray.flatten,
  --     ∀ l v, (l, .success v) ∈ (sys.tr th item.2.1) →
  --       (fp.view v) ∈ baseCtx.seen ∨ (fp.view v) ∈ postCtx.tovisitSet)
  SuccessorsCollected sys (fun ⟨h, st, d⟩ => (h, st, d) ∈ splitArrays.toArray.flatten)
    postCtx.hasFinished (fun h => h ∈ baseCtx.seen ∨ h ∈ postCtx.tovisitSet)
  := by
  intro h_not_finished fingerprint st d h_item_in_flatten l v h_tr
  rw [h_postCtx_eq]
  have h_init_not_finished : (LocalSearchContext.NeutralContext sys params baseCtx h_seen_sound).finished = none := by
    simp only [LocalSearchContext.NeutralContext]
  rw [h_postCtx_eq] at h_not_finished
  exact foldl_merge_preserves_successors_collected sys baseCtx splitArrays
    (LocalSearchContext.NeutralContext sys params baseCtx h_seen_sound) h_init_not_finished
    results h_not_finished (fingerprint, st, d) h_item_in_flatten l v h_tr


/-- Combined lemma: derives h_collect_all from parallel BFS results for use in merge_preserves_frontier_closed.
    This handles the conversion from tovisit membership to splitArrays.flatten membership,
    and the hasFinished case analysis. -/
theorem parallel_bfs_collect_all {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  (ctx : @ParallelSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (tovisitArr : Array (QueueItem σₕ σ))
  (h_tovisitArr_eq : tovisitArr = ctx.tovisitQueue)
  (ranges : List (Nat × Nat))
  (h_ranges_cover : ∀ i, i < tovisitArr.size → ∃ lr ∈ ranges, lr.1 ≤ i ∧ i < lr.2)
  (h_ranges_valid : ∀ lr ∈ ranges, lr.1 ≤ lr.2 ∧ lr.2 ≤ tovisitArr.size)
  (splitArrays : List (Array (σₕ × σ × Nat)))
  (h_splitArrays_eq : splitArrays = ranges.map (fun lr => (tovisitArr.extract lr.1 lr.2).map (fun item => (item.fingerprint, item.state, item.depth))))
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (h_baseCtx_eq : baseCtx = ctx.toBaseSearchContext)
  (aggregatedCtx : LocalSearchContext sys params baseCtx)
  (h_liftBfs : SuccessorsCollected sys (fun ⟨h, st, d⟩ => (h, st, d) ∈ splitArrays.toArray.flatten)
    aggregatedCtx.hasFinished (fun h => h ∈ baseCtx.seen ∨ h ∈ aggregatedCtx.tovisitSet))
  (h_ctx_not_finished : ctx.finished = none)
  (h_new_finished : Option.or ctx.finished aggregatedCtx.finished = some .exploredAllReachableStates ∨
                    Option.or ctx.finished aggregatedCtx.finished = none)
  (h_view_inj : Function.Injective fp.view) :
  ∀ (s : σ),
    fp.view s ∈ ctx.tovisitSet →
    (∀l v, (l, .success v) ∈ sys.tr th s → (fp.view v) ∈ ctx.seen ∨ (fp.view v) ∈ aggregatedCtx.tovisitSet) := by
  intro s h_s_in_old_tovisit l v h_tr
  -- Get item from set via consistency
  have ⟨item, h_item_in_queue, h_item_fp⟩ := ctx.tovisitConsistent (fp.view s) |>.mp h_s_in_old_tovisit
  -- Show item is in splitArrays.flatten (as a tuple)
  have h_item_in_flatten : (item.fingerprint, item.state, item.depth) ∈ splitArrays.toArray.flatten := by
    have h_in_tovisitArr : item ∈ tovisitArr := by rw [h_tovisitArr_eq]; exact h_item_in_queue
    rw [h_splitArrays_eq]
    exact Array.mem_flatten_of_partition_map tovisitArr ranges item h_in_tovisitArr h_ranges_cover h_ranges_valid (fun item => (item.fingerprint, item.state, item.depth))
  -- Get the actual state from the queue item - use wellformedness to establish s = item.state
  have h_wf : item.fingerprint = fp.view item.state := ctx.invs.queue_wellformed item.fingerprint item.state item.depth h_item_in_queue
  have h_s_eq : s = item.state := by
    have h_fp_eq : fp.view s = fp.view item.state := by rw [← h_item_fp, h_wf]
    exact h_view_inj h_fp_eq
  -- Note: we don't rewrite s here, we use h_s_eq later when calling h_liftBfs
  by_cases h_agg_finished : aggregatedCtx.hasFinished
  · -- aggregatedCtx has finished → contradiction with h_new_finished
    simp [h_ctx_not_finished] at h_new_finished
    simp [BaseSearchContext.hasFinished] at h_agg_finished
    cases h_new_finished with
    | inl h_explored => exact absurd h_explored aggregatedCtx.excludeAllStatesFinish
    | inr h_none => simp [h_none] at h_agg_finished
  · -- aggregatedCtx has not finished → use SuccessorsCollected
    -- baseCtx.seen = ctx.seen since baseCtx = ctx.toBaseSearchContext
    have h_result := h_liftBfs (by simp [h_agg_finished]) item.fingerprint item.state item.depth h_item_in_flatten l v (by rw [← h_s_eq]; exact h_tr)
    simp only [h_baseCtx_eq] at h_result
    exact h_result


/-- Reduce operation: merges a ParallelSearchContext with aggregated LocalSearchContext results.
    This is the main reduction step in parallel BFS that combines global and local search results. -/
@[inline, specialize]
def ParallelSearchContext.Reduce {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (ctx : @ParallelSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (aggregatedCtx : LocalSearchContext sys params ctx.toBaseSearchContext)
  (tovisitArr : Array (QueueItem σₕ σ))
  (h_tovisitArr_eq : tovisitArr = ctx.tovisitQueue)
  (ranges : List (Nat × Nat))
  (h_ranges_cover : ∀ i, i < tovisitArr.size → ∃ lr ∈ ranges, lr.1 ≤ i ∧ i < lr.2)
  (h_ranges_valid : ∀ lr ∈ ranges, lr.1 ≤ lr.2 ∧ lr.2 ≤ tovisitArr.size)
  (splitArrays : List (Array (σₕ × σ × Nat)))
  (h_splitArrays_eq : splitArrays = ranges.map (fun lr => (tovisitArr.extract lr.1 lr.2).map (fun item => (item.fingerprint, item.state, item.depth))))
  (results : IteratedProd (List.map (fun (x : Array (σₕ × σ × Nat)) => { ctx' : LocalSearchContext sys params ctx.toBaseSearchContext //
    SuccessorsCollected sys (fun ⟨h, st, d⟩ => (h, st, d) ∈ x) ctx'.hasFinished (fun h => h ∈ ctx'.seen ∨ h ∈ ctx'.tovisitSet) })
    splitArrays))
  (h_aggregatedCtx_eq : aggregatedCtx = IteratedProd.foldl
    (init := LocalSearchContext.NeutralContext sys params ctx.toBaseSearchContext ctx.invs.visited_sound)
    (fun acc r => .Merge sys params ctx.toBaseSearchContext acc r.val) results)
  (h_ctx_not_finished : ctx.finished = none) :
  @ParallelSearchContext ρ σ κ σₕ fp _ _ th sys params :=
  -- Build new tovisitSet from aggregatedCtx's queue
  let newTovisitSet := aggregatedCtx.tovisitQueue.foldl (fun acc item => acc.insert item.fingerprint) Std.HashSet.emptyWithCapacity
  { ctx with
    seen := ctx.seen.union aggregatedCtx.tovisitSet,
    tovisitQueue := aggregatedCtx.tovisitQueue,
    tovisitSet := newTovisitSet,
    log := ctx.log.union aggregatedCtx.localLog,
    completedDepth := ctx.currentFrontierDepth,
    currentFrontierDepth := ctx.currentFrontierDepth + 1,
    violatingStates := ctx.violatingStates ++ aggregatedCtx.violatingStates,
    finished := Option.or ctx.finished aggregatedCtx.finished,
    statesFound := ctx.statesFound + aggregatedCtx.localStatesFound,
    actionStatsMap := mergeActionStatsMaps ctx.actionStatsMap aggregatedCtx.localActionStatsMap,
    tovisitConsistent := reduce_preserves_tovisitConsistent aggregatedCtx
    invs := merge_parallel_local_preserves_invs sys params ctx aggregatedCtx rfl
    frontier_closed := by
      intro h_view_inj h_finished s h_in_seen h_not_in_tovisit l next_s h_tr
      have h_pre_no_terminate : ctx.finished = none := by simp_all
      have h_liftBfs := parallel_bfs_successors_collected sys ctx.toBaseSearchContext ctx.invs.visited_sound
        splitArrays aggregatedCtx results h_aggregatedCtx_eq
      have h_collect_all := parallel_bfs_collect_all sys ctx tovisitArr h_tovisitArr_eq ranges
        h_ranges_cover h_ranges_valid
        splitArrays h_splitArrays_eq ctx.toBaseSearchContext rfl aggregatedCtx h_liftBfs h_pre_no_terminate h_finished h_view_inj
      -- Convert h_not_in_tovisit from newTovisitSet to aggregatedCtx.tovisitSet
      -- Both sets have the same membership by construction (newTovisitSet is built from aggregatedCtx.tovisitQueue)
      have h_new_tovisit_consistent := reduce_preserves_tovisitConsistent aggregatedCtx
      have h_sets_equiv : ∀ h, h ∈ newTovisitSet ↔ h ∈ aggregatedCtx.tovisitSet := by
        intro h
        constructor
        · intro h_in_new
          have ⟨item, h_item_in, h_fp_eq⟩ := h_new_tovisit_consistent h |>.mp h_in_new
          rw [← h_fp_eq]
          exact aggregatedCtx.tovisitConsistent item.fingerprint |>.mpr ⟨item, h_item_in, rfl⟩
        · intro h_in_old
          have ⟨item, h_item_in, h_fp_eq⟩ := aggregatedCtx.tovisitConsistent h |>.mp h_in_old
          exact h_new_tovisit_consistent h |>.mpr ⟨item, h_item_in, h_fp_eq⟩
      have h_not_in_agg_tovisit : fp.view s ∉ aggregatedCtx.tovisitSet := by
        intro h_in; exact h_not_in_tovisit ((h_sets_equiv (fp.view s)).mpr h_in)
      -- tovisitSet membership trivially implies tovisitSet membership (identity function)
      have h_delta_set : Function.Injective fp.view →
          ∀ x, (fp.view x) ∈ aggregatedCtx.tovisitSet → fp.view x ∈ aggregatedCtx.tovisitSet := fun _ _ h => h
      exact ParallelSearchContext.merge_preserves_frontier_closed sys params ctx
        aggregatedCtx.tovisitSet aggregatedCtx.tovisitSet h_pre_no_terminate h_view_inj
        h_delta_set h_collect_all s h_in_seen h_not_in_agg_tovisit l next_s h_tr
    terminate_empty_tovisit := by
      intro h_finished
      rw [h_aggregatedCtx_eq] at h_finished
      have : (IteratedProd.foldl (LocalSearchContext.NeutralContext sys params ctx.toBaseSearchContext ctx.invs.visited_sound)
        (fun acc r => .Merge sys params ctx.toBaseSearchContext acc r.val) results).finished ≠ some .exploredAllReachableStates := by
        rw [← h_aggregatedCtx_eq]
        exact aggregatedCtx.excludeAllStatesFinish
      simp [h_ctx_not_finished] at h_finished
      exact absurd h_finished this
    starts_in_seen := by
      intro s0 h_s0_in_init; have h_init := ctx.starts_in_seen s0 h_s0_in_init
      exact Std.HashSet.mem_union_of_left h_init
  }

@[specialize]
def breadthFirstSearchParallel {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ] [Repr σ] [Repr σₕ] [Repr κ]
  {th : ρ} (sys : _)
  (params : SearchParameters ρ σ)
  (parallelCfg : ParallelConfig)
  (progressInstanceId : Nat)
  (cancelToken : IO.CancelToken) :
  m (@ParallelSearchContext ρ σ κ σₕ fp _ _ th sys params) := do
  let mut ctx : @ParallelSearchContext ρ σ κ σₕ fp _ _ th sys params := ParallelSearchContext.initial sys params
  let mut lastUpdateTime : Nat := 0
  while h_not_finished : !ctx.hasFinished do
    let currentCtx := ctx
    -- In this setting, the queue emptiness check needs to be done here
    if h_tovisit_empty : ctx.tovisitQueue.isEmpty then
      ctx := { ctx with
        finished := some (.exploredAllReachableStates),
        frontier_closed := by
          intro h_view_inj h_finished s h_in_seen h_not_in_tovisit l next_s h_tr
          have : ctx.finished = none := by unfold BaseSearchContext.hasFinished at h_not_finished; simp at h_not_finished; exact h_not_finished
          exact ctx.frontier_closed h_view_inj (Or.inr this) s h_in_seen h_not_in_tovisit l next_s h_tr
        terminate_empty_tovisit := by intro _; exact h_tovisit_empty
      }
      updateProgress progressInstanceId
        ctx.currentFrontierDepth ctx.statesFound ctx.seen.size ctx.tovisitQueue.size
        (toActionStatsList ctx.actionStatsMap)
      return ctx
    else
      let tovisitArr := ctx.tovisitQueue
      -- Spawn tasks for each chunk range
      let ranges := ParallelConfig.chunkRanges parallelCfg tovisitArr.size
      -- Convert QueueItem to tuples for bfsBigStep
      let splitArrays := ranges.map (fun lr => (tovisitArr.extract lr.1 lr.2).map (fun item => (item.fingerprint, item.state, item.depth)))
      let baseCtx := ctx.toBaseSearchContext

      have h_baseCtx_not_finished : baseCtx.finished = none := by
        unfold BaseSearchContext.hasFinished at h_not_finished
        simp at h_not_finished; exact h_not_finished
      have h_baseCtx_seen_sound := ctx.invs.visited_sound

      /- Show that:
      * all items in tovisitArr are _reachable_
      * elements in any extract are also _reachable_
      * all sub-arrays in splitArrays have _reachable_ items -/
      have h_tovisitArr_reachable := tovisitQueue_items_reachable sys params ctx
      have h_extract_reachable := Array_extract_items_reachable_QueueItem sys tovisitArr h_tovisitArr_reachable
      have h_splitArrays_sound := splitArrays_items_reachable_QueueItem sys tovisitArr ranges splitArrays rfl h_extract_reachable

      -- CAVEAT: The call to `IO.asTask` **SHOULD NOT** be put in this procedure,
      -- as that might cause parallelism to vanish!!! Instead, the call should be defined
      -- in some other file.
      let tasks ← IteratedProd.taskSplit splitArrays fun subArr h_subArr_in =>
        have h_reachable : ∀ item ∈ subArr.toList, sys.reachable item.2.1 :=
          h_splitArrays_sound subArr h_subArr_in
        LocalSearchContext.bfsBigStep sys baseCtx subArr h_baseCtx_seen_sound h_reachable

      -- let totalTasks := IteratedProd.foldl (init := 0) (fun acc _ => acc + 1) tasks
      -- IO.eprintln s!"[{← IO.monoMsNow} @ tid {← IO.getTID}] spawned {totalTasks} tasks"
      let results ← IteratedProd.mapM (fun task => IO.ofExcept task.get) tasks

      -- Aggregate all of the local contexts
      let aggregatedCtx := IteratedProd.foldl
        (init := LocalSearchContext.NeutralContext _ _ baseCtx _)
        (fun acc r => .Merge sys params baseCtx acc r.val) results

      have h_ctx_not_finished : ctx.finished = none := by
        unfold BaseSearchContext.hasFinished at h_not_finished
        simp at h_not_finished
        exact h_not_finished

      -- Reduce step: merge aggregatedCtx into ctx
      ctx := .Reduce _ _ ctx aggregatedCtx tovisitArr rfl ranges
        (ParallelConfig.chunkRanges_cover parallelCfg tovisitArr.size)
        (ParallelConfig.chunkRanges_valid parallelCfg tovisitArr.size)
        splitArrays rfl results rfl h_ctx_not_finished

      -- If we found a violation, mark it so handoff is prevented
      if let some (.earlyTermination cond) := ctx.finished then
        if EarlyTerminationReason.isViolation cond then setViolationFound progressInstanceId
      -- Update progress and check for cancellation/handoff at most once per second
      let now ← IO.monoMsNow
      if now - lastUpdateTime >= 1000 then
        lastUpdateTime := now
        -- TLC-style stats: diameter, statesFound, distinctStates, queue, actionStats
        updateProgress progressInstanceId
          ctx.currentFrontierDepth ctx.statesFound ctx.seen.size ctx.tovisitQueue.size
          (toActionStatsList ctx.actionStatsMap)
        if ← shouldStop cancelToken progressInstanceId then
          ctx := { ctx with
            finished := some (.earlyTermination .cancelled),
            frontier_closed := by intro h_view_inj h_finished _ ; simp at h_finished
            terminate_empty_tovisit := by intro h_finished_empty_tovisit; simp at h_finished_empty_tovisit}
          break
  -- Final update to ensure stats reflect finished state
  updateProgress progressInstanceId
    ctx.currentFrontierDepth ctx.statesFound ctx.seen.size ctx.tovisitQueue.size
    (toActionStatsList ctx.actionStatsMap)
  return ctx

end Veil.ModelChecker.Concrete
