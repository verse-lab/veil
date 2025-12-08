import Veil.Core.Tools.Checker.Concrete.State

variable {σₕ : Type}
variable {σ κ ρ ℂ ℝ: Type}
variable [Inhabited σ] [Hashable σ]
variable [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [EquivBEq σₕ] [LawfulHashable σₕ]
variable (allLabels : List κ)
variable (INV : ρ → σ → Prop)
variable (Terminate : ρ → σ → Prop)
variable [dec_inv: ∀rd : ρ, ∀st : σ, Decidable (INV rd st)]
variable [dec_term: ∀rd : ρ, ∀st : σ, Decidable (Terminate rd st)]
variable [IsSubStateOf ℂ σ]
variable [IsSubReaderOf ℝ ρ]


def closed_invariant (starts : List σ) (adj : σ → List (κ × σ)) (view : σ → σₕ)
    (st : SearchContext σ κ σₕ starts adj view) : Prop :=
  Function.Injective view →
    st.counterexample = [] →
      ∀ u, (view u) ∈ st.seen →
        ⟨view u, u⟩ ∉ st.sq.toList →
          ∀l v, (l, v) ∈ adj u → (view v) ∈ st.seen


/-- st.termination = true ∧ st.counterexample = [] → st.sq.toList = []-/
def normal_termination_implies_empty_queue
  (starts : List σ)
  (adj : σ → List (κ × σ))
  (view : σ → σₕ)
  (st : SearchContext σ κ σₕ starts adj view) : Prop :=
    st.termination = true ∧ st.counterexample = [] →
      st.sq.toList = []

/-- Initial states are in seen -/
def starts_in_seen
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (st : SearchContext σ κ σₕ starts adj view) : Prop :=
  ∀ s, s ∈ starts → view s ∈ st.seen


/-- Completeness property: When the search terminates successfully (termination = true and
    counterexample = []), all reachable states have been visited (their fingerprints are in seen).
    If the search completes without finding a counterexample, then we have explored the entire reachable state space.
    Note: We require view to be injective so that fingerprints uniquely identify states.
    The property states that for every reachable state x, its fingerprint (view x) is in seen. -/
def bfsStep_completeness
  (starts : List σ)
  (adj : σ → List (κ × σ))
  (view : σ → σₕ)
  (st : SearchContext σ κ σₕ starts adj view) : Prop :=
  Function.Injective view →
    (st.termination = true ∧ st.counterexample = []) →
      ∀ x : σ, Reachable adj starts x → (view x) ∈ st.seen



/-- Helper lemma: processNeighbor preserves seen monotonicity -/
lemma processNeighbor_seen_monotone
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ) (fpSt : σₕ)
    (st : SearchContext σ κ σₕ starts adj view)
    (neighbor : κ × σ)
    (h_reach : Reachable adj starts neighbor.2)
    (fp : σₕ)
    (h_in : fp ∈ st.seen) :
    fp ∈ (processNeighbor INV starts adj view rd fpSt st neighbor h_reach).seen := by
  unfold processNeighbor
  split; grind

/-- Helper lemma: processNeighbor adds the neighbor's fingerprint to seen -/
lemma processNeighbor_adds_neighbor
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ) (fpSt : σₕ)
    (st : SearchContext σ κ σₕ starts adj view)
    (neighbor : κ × σ)
    (h_reach : Reachable adj starts neighbor.2) :
    (view neighbor.2) ∈ (processNeighbor INV starts adj view rd fpSt st neighbor h_reach).seen := by
  unfold processNeighbor
  split; grind

/-- Helper lemma: foldl with processNeighbor preserves seen monotonicity -/
lemma foldl_processNeighbor_seen_monotone
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ) (fpSt : σₕ)
    (curr : σ)
    (h_curr : Reachable adj starts curr)
    (list : List {x // x ∈ adj curr})
    (st : SearchContext σ κ σₕ starts adj view)
    (fp : σₕ)
    (h_in : fp ∈ st.seen) :
    fp ∈ (list.foldl (fun current_st ⟨neighbor, h_neighbor_in_adj⟩ =>
      if current_st.termination then current_st
      else
        let h_neighbor_reachable := Reachable.step h_curr h_neighbor_in_adj
        processNeighbor INV starts adj view rd fpSt current_st neighbor h_neighbor_reachable
    ) st).seen := by
  induction list generalizing st with
  | nil =>
    rw [List.foldl_nil]
    exact h_in
  | cons head tail ih =>
    rw [List.foldl_cons]
    obtain ⟨neighbor, h_neighbor_in_adj⟩ := head
    let h_reach := Reachable.step h_curr h_neighbor_in_adj
    conv_lhs => arg 1; arg 2; simp only []
    by_cases h_term : st.termination = true
    · simp only [h_term, ite_true]
      exact ih st h_in
    · have h_term_false : st.termination = false := by grind
      simp only [h_term_false]
      let st' := processNeighbor INV starts adj view rd fpSt st neighbor h_reach
      have h_in_st' : fp ∈ st'.seen :=
        processNeighbor_seen_monotone INV starts adj view rd fpSt st neighbor h_reach fp h_in
      exact ih st' h_in_st'


/-- processNeighbor preserves existing queue elements -/
lemma processNeighbor_queue_monotone
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ) (fpSt : σₕ)
    (st : SearchContext σ κ σₕ starts adj view)
    (neighbor : κ × σ)
    (h_reach : Reachable adj starts neighbor.2)
    (x : σ)
    (h_in : (view x, x) ∈ st.sq.toList) :
    (view x, x) ∈ (processNeighbor INV starts adj view rd fpSt st neighbor h_reach).sq.toList := by
  unfold processNeighbor
  grind [toList_enqueue]

/-- foldl with processNeighbor preserves queue elements -/
lemma foldl_processNeighbor_queue_monotone
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ) (fpSt : σₕ)
    (curr : σ)
    (h_curr : Reachable adj starts curr)
    (list : List {y // y ∈ adj curr})
    (st : SearchContext σ κ σₕ starts adj view)
    (x : σ)
    (h_in : (view x, x) ∈ st.sq.toList) :
    (view x, x) ∈ (list.foldl (fun current_st ⟨neighbor, h_neighbor_in_adj⟩ =>
      if current_st.termination then current_st
      else
        let h_neighbor_reachable := Reachable.step h_curr h_neighbor_in_adj
        processNeighbor INV starts adj view rd fpSt current_st neighbor h_neighbor_reachable
    ) st).sq.toList := by
  induction list generalizing st with
  | nil =>
    rw [List.foldl_nil]
    exact h_in
  | cons head tail ih =>
    rw [List.foldl_cons]
    obtain ⟨neighbor, h_neighbor_in_adj⟩ := head
    let h_reach := Reachable.step h_curr h_neighbor_in_adj
    by_cases h_term : st.termination = true
    · simp only [h_term, ite_true]
      exact ih st h_in
    · have h_term_false : st.termination = false := by grind
      simp only [h_term_false]
      let st' := processNeighbor INV starts adj view rd fpSt st neighbor h_reach
      have h_in_st' : (view x, x) ∈ st'.sq.toList :=
        processNeighbor_queue_monotone INV starts adj view rd fpSt st neighbor h_reach x h_in
      exact ih st' h_in_st'


lemma processSuccessors_queue_monotone
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ) (fpSt : σₕ)
    (curr : σ)
    (h_curr : Reachable adj starts curr)
    (st : SearchContext σ κ σₕ starts adj view)
    (x : σ)
    (h_in : (view x, x) ∈ st.sq.toList) :
    (view x, x) ∈ (processSuccessors INV starts adj view rd fpSt curr h_curr st).sq.toList := by
  unfold processSuccessors
  exact foldl_processNeighbor_queue_monotone INV starts adj view rd fpSt curr h_curr (adj curr).attach st x h_in


lemma processSuccessors_seen_monotone
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ) (fpSt : σₕ)
    (curr : σ)
    (h_curr : Reachable adj starts curr)
    (st : SearchContext σ κ σₕ starts adj view)
    (fp : σₕ)
    (h_in : fp ∈ st.seen) :
    fp ∈ (processSuccessors INV starts adj view rd fpSt curr h_curr st).seen := by
  unfold processSuccessors
  exact foldl_processNeighbor_seen_monotone INV starts adj view rd fpSt curr h_curr (adj curr).attach st fp h_in


lemma bfsStep_seen_monotone
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ)
    (pre : SearchContext σ κ σₕ starts adj view)
    (fp : σₕ)
    (h_in : fp ∈ pre.seen) :
    fp ∈ (bfsStep INV Terminate starts adj view rd pre).seen := by
  unfold bfsStep
  by_cases h_deq : pre.sq.dequeue? = none
  · grind
  · have ⟨val, h_some⟩ : ∃ val, pre.sq.dequeue? = some val := by grind
    obtain ⟨⟨fpSt, curr⟩, q_tail⟩ := val
    have h_toList : pre.sq.toList = (fpSt, curr) :: q_tail.toList := by grind
    have h_curr_reach : Reachable adj starts curr := by
      have h_fp_eq : fpSt = view curr := by
        apply pre.queue_wellformed; grind
      have h_in_q : (view curr, curr) ∈ pre.sq.toList := by grind
      exact pre.queue_sound curr h_in_q
    by_cases h_adj : adj curr = []
    · grind
    · have ⟨head, tail, h_cons⟩ : ∃ head tail, adj curr = head :: tail := by
        cases h : adj curr with
        | nil => contradiction
        | cons h t => grind
      have htem := processSuccessors_seen_monotone INV starts adj view rd fpSt curr h_curr_reach
      grind


lemma bfs_preserves_starts_in_seen
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ)
    (st : SearchContext σ κ σₕ starts adj view)
    (h_starts : starts_in_seen starts adj view st) :
    starts_in_seen starts adj view (bfsStep INV Terminate starts adj view rd st) := by
  unfold starts_in_seen
  intro s h_in_starts
  have h_in_seen := h_starts s h_in_starts
  have h_in_seen_after := bfsStep_seen_monotone INV Terminate starts adj view rd st
  grind


lemma processNeighbor_counterexample_monotone
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ) (fpSt : σₕ)
    (st : SearchContext σ κ σₕ starts adj view)
    (neighbor : κ × σ)
    (h_reach : Reachable adj starts neighbor.2)
    (x : σₕ)
    (h_in : x ∈ st.counterexample) :
    x ∈ (processNeighbor INV starts adj view rd fpSt st neighbor h_reach).counterexample := by
  unfold processNeighbor
  by_cases h_seen : st.seen.contains (view neighbor.2)
  · simp [h_seen]
    exact h_in
  · simp [h_seen]
    by_cases h_inv : decide (INV rd neighbor.2) = true
    <;> grind

lemma processSuccessors_counterexample_monotone
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ) (fpSt : σₕ)
    (curr : σ)
    (h_curr : Reachable adj starts curr)
    (st : SearchContext σ κ σₕ starts adj view)
    (x : σₕ)
    (h_in : x ∈ st.counterexample) :
    x ∈ (processSuccessors INV starts adj view rd fpSt curr h_curr st).counterexample := by
  unfold processSuccessors
  let neighbors := (adj curr).attach
  suffices ∀ (list : List {x // x ∈ adj curr}) (s : SearchContext σ κ σₕ starts adj view),
    x ∈ s.counterexample →
    x ∈ (list.foldl (fun current_st ⟨neighbor, h_neighbor_in_adj⟩ =>
      if current_st.termination then current_st
      else
        let h_neighbor_reachable := Reachable.step h_curr h_neighbor_in_adj
        processNeighbor INV starts adj view rd fpSt current_st neighbor h_neighbor_reachable
    ) s).counterexample by
    exact this neighbors st h_in
  intro list s h_x_in
  induction list generalizing s with
  | nil => simp; exact h_x_in
  | cons head tail ih =>
    simp [List.foldl_cons]
    obtain ⟨neighbor, h_neighbor_in_adj⟩ := head
    let h_reach := Reachable.step h_curr h_neighbor_in_adj
    by_cases h_term : s.termination = true
    · simp [h_term]
      have h_x_in_s : x ∈ s.counterexample := h_x_in
      aesop
    · simp [h_term]
      let s' := processNeighbor INV starts adj view rd fpSt s neighbor h_reach
      have h_x_in_s' : x ∈ s'.counterexample :=
        processNeighbor_counterexample_monotone INV starts adj view rd fpSt s neighbor h_reach x h_x_in
      aesop


lemma bfsStep_counterexample_monotone
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ)
    (pre : SearchContext σ κ σₕ starts adj view)
    (x : σₕ)
    (h_in : x ∈ pre.counterexample) :
    x ∈ (bfsStep INV Terminate starts adj view rd pre).counterexample := by
  simp only [bfsStep]
  split
  · simp; exact h_in
  · rename_i fpSt curr q_tail h_deq
    have h_toList : pre.sq.toList = (fpSt, curr) :: q_tail.toList := by
      have spec := dequeue?_spec pre.sq
      rw [h_deq] at spec; simp at spec; exact spec
    have h_fpSt_eq : fpSt = view curr := by
      have h_in_queue : (fpSt, curr) ∈ pre.sq.toList := by
        rw [h_toList]; simp
      exact pre.queue_wellformed fpSt curr h_in_queue
    have h_curr_reach : Reachable adj starts curr := by
      have h_in_q : (view curr, curr) ∈ pre.sq.toList := by
        rw [h_toList]; simp; left; rw [←h_fpSt_eq]
      exact pre.queue_sound curr h_in_q
    let st_dequeued : SearchContext σ κ σₕ starts adj view := {
      pre with
      sq := q_tail,
      queue_sound := by
        intros y hy
        apply pre.queue_sound
        rw [h_toList]
        simp [hy]
      visited_sound := pre.visited_sound
      queue_sub_visited := by
        intros y hy
        have h_in_pre : (view y, y) ∈ pre.sq.toList := by grind
        exact pre.queue_sub_visited y h_in_pre
      queue_wellformed := by
        intros fp st hy
        have h_in_pre : (fp, st) ∈ pre.sq.toList := by grind
        exact pre.queue_wellformed fp st h_in_pre
    }
    split
    · exact processSuccessors_counterexample_monotone INV starts adj view rd fpSt curr h_curr_reach st_dequeued x h_in
    · by_cases h_term : decide (Terminate rd curr) = true
      · simp [h_term]; exact h_in
      · simp [h_term]; right; exact h_in

lemma bfsStep_empty_counterexample_implies_pre_empty
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ)
    (pre : SearchContext σ κ σₕ starts adj view)
    (h_post_empty : (bfsStep INV Terminate starts adj view rd pre).counterexample = []) :
    pre.counterexample = [] := by
  by_contra h_ne
  have ⟨x, h_x_in⟩ : ∃ x, x ∈ pre.counterexample := by
    cases h : pre.counterexample with
    | nil => contradiction
    | cons head tail => exact ⟨head, by simp⟩
  have h_x_in_post := bfsStep_counterexample_monotone INV Terminate starts adj view rd pre x h_x_in
  rw [h_post_empty] at h_x_in_post
  simp at h_x_in_post

theorem processNeighbor_preserves_consistency
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ) (fpSt : σₕ)
    (st : SearchContext σ κ σₕ starts adj view)
    (neighbor : κ × σ)
    (h_reach : Reachable adj starts neighbor.2)
    (h_st_term : st.termination = false) :
    let st' := processNeighbor INV starts adj view rd fpSt st neighbor h_reach
    ¬(st'.termination = true ∧ st'.counterexample = []) := by
  unfold processNeighbor
  split; simp; grind

theorem processSuccessors_preserves_consistency
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ) (fpSt : σₕ)
    (curr : σ) (h_curr : Reachable adj starts curr)
    (st : SearchContext σ κ σₕ starts adj view)
    (h_st_consistent : st.termination → st.counterexample ≠ []) :
    let st' := processSuccessors INV starts adj view rd fpSt curr h_curr st
    ¬(st'.termination = true ∧ st'.counterexample = []) := by
  unfold processSuccessors
  intro st'
  simp
  let list := (adj curr).attach
  have h_fold : ∀ (s : SearchContext σ κ σₕ starts adj view), (s.termination → s.counterexample ≠ []) →
      let s' := List.foldl (fun (current_st : SearchContext σ κ σₕ starts adj view) ⟨neighbor, h⟩ =>
        if current_st.termination then current_st
        else processNeighbor INV starts adj view rd fpSt current_st neighbor (Reachable.step h_curr h)) s list
      (s'.termination → s'.counterexample ≠ []) := by
    intro s0 h0
    induction list generalizing s0 with
    | nil =>
      simp [List.foldl]
      exact h0
    | cons head tail ih =>
      let ⟨neighbor, h_neighbor_in_adj⟩ := head
      let h_reach := Reachable.step h_curr h_neighbor_in_adj
      rw [List.foldl]
      split_ifs with h_term
      · grind
      · let s' := processNeighbor INV starts adj view rd fpSt s0 neighbor h_reach
        apply ih
        intro h_term_new
        have h_term_false : s0.termination = false := by
          by_cases h : s0.termination = true
          · exfalso; exact h_term h
          · by_cases h' : s0.termination = false
            · exact h'
            · exfalso
              have : s0.termination = true ∨ s0.termination = false := by grind
              cases this with
              | inl h_eq => exact h h_eq
              | inr h_eq => exact h' h_eq
        have h_impossible := processNeighbor_preserves_consistency INV starts adj view rd fpSt s0 neighbor h_reach h_term_false
        by_contra h_cex_empty
        apply h_impossible
        constructor
        · exact h_term_new
        · exact h_cex_empty
  have h_res_prop := h_fold st h_st_consistent
  intro h_bad
  have h_cex_not_empty := h_res_prop h_bad
  grind


theorem bfsStep_preserves_normal_termination_implies_empty_queue
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ)
    (pre : SearchContext σ κ σₕ starts adj view)
    (h_pre : normal_termination_implies_empty_queue starts adj view pre) :
    let post := bfsStep INV Terminate starts adj view rd pre
    normal_termination_implies_empty_queue starts adj view post := by
  intro post
  cases h_deq : pre.sq.dequeue? with
  | none =>
    unfold normal_termination_implies_empty_queue; simp
    intro h_post_term_and_clean h_post_cex_empty
    simp at h_deq
    simp [post, bfsStep]
    simp [fQueue.dequeue?]
    have h_sq_front_empty : pre.sq.norm.front = [] := by grind
    split <;> grind
  | some val =>
    unfold normal_termination_implies_empty_queue
    intro h_post_term_and_clean
    match val with
    | ((fpSt, curr), q_tail) =>
      have h_toList : pre.sq.toList = (fpSt, curr) :: q_tail.toList := by grind
      let st_dequeued : SearchContext σ κ σₕ starts adj view := {
        pre with
        sq := q_tail,
        queue_sound := by
          intros x h_in
          have h_pre_sound := pre.queue_sound; grind
        visited_sound := pre.visited_sound
        queue_sub_visited := by
          intros x h_in
          have h_in_pre : (view x, x) ∈ pre.sq.toList := by grind
          exact pre.queue_sub_visited x h_in_pre
        queue_wellformed := by
          intros fp st h_in
          have h_in_pre : (fp, st) ∈ pre.sq.toList := by grind
          exact pre.queue_wellformed fp st h_in_pre
      }
      let successors := adj curr
      match h_succ : successors with
      | [] =>
        simp [post, bfsStep] at h_post_term_and_clean
        by_cases h_term : Terminate rd curr
        . obtain ⟨h_post_term, h_post_cex_empty⟩ := h_post_term_and_clean
          have h_post_eq_st_dequeued : post = st_dequeued := by simp [post, bfsStep]; grind
          have h_pre_term : pre.termination = true := by grind
          have h_pre_cex_empty : pre.counterexample = [] := by grind
          have h_pre_empty_queue : pre.sq.toList = [] := h_pre ⟨h_pre_term, h_pre_cex_empty⟩
          rw [h_toList] at h_pre_empty_queue
          simp at h_pre_empty_queue
        . obtain ⟨h_post_term, h_post_cex_empty⟩ := h_post_term_and_clean
          have h_post_cex : post.counterexample = fpSt :: st_dequeued.counterexample := by grind
          grind
      | _ :: _ =>
        simp [post, bfsStep] at h_post_term_and_clean
        obtain ⟨h_post_term, h_post_cex_empty⟩ := h_post_term_and_clean
        have h_st_dequeued_consistent : st_dequeued.termination → st_dequeued.counterexample ≠ [] := by
          intro h_term_deq
          have h_pre_term : pre.termination = true := h_term_deq
          by_contra h_cex_empty
          have h_pre_empty : pre.sq.toList = [] := h_pre ⟨h_pre_term, h_cex_empty⟩
          rw [h_toList] at h_pre_empty
          simp at h_pre_empty
        have h_fpSt_eq : fpSt = view curr := by
          have h_in_queue : (fpSt, curr) ∈ pre.sq.toList := by grind
          exact pre.queue_wellformed fpSt curr h_in_queue
        have h_curr_reach : Reachable adj starts curr := by
          have h_in : (view curr, curr) ∈ pre.sq.toList := by grind
          exact pre.queue_sound curr h_in
        have h_post_eq : post = processSuccessors INV starts adj view rd fpSt curr h_curr_reach st_dequeued := by
          simp [post, bfsStep]; grind
        let post := processSuccessors INV starts adj view rd fpSt curr h_curr_reach st_dequeued
        have h_no_bad_raw : ¬(post.termination = true ∧ post.counterexample = []) :=
          processSuccessors_preserves_consistency INV starts adj view rd fpSt curr h_curr_reach st_dequeued h_st_dequeued_consistent
        have h_post_consistent : ¬(post.termination = true ∧ post.counterexample = []) := by grind
        exfalso
        grind


lemma processNeighbor_sees_self
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ) (fpSt : σₕ)
    (st : SearchContext σ κ σₕ starts adj view)
    (neighbor : κ × σ)
    (h_reach : Reachable adj starts neighbor.2) :
    let post := processNeighbor INV starts adj view rd fpSt st neighbor h_reach
    view neighbor.2 ∈ post.seen := by
  unfold processNeighbor
  split; grind


lemma processSuccessors_sees_neighbors_of_no_cex
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ) (fpSt : σₕ)
    (curr : σ)
    (h_curr : Reachable adj starts curr)
    (st : SearchContext σ κ σₕ starts adj view)
    (l : κ) (v : σ)
    (h_in : (l, v) ∈ adj curr)
    (h_pre_term : st.termination = false)
    (h_pre_cex : st.counterexample = [])
    (h_post_no_cex : (processSuccessors INV starts adj view rd fpSt curr h_curr st).counterexample = []) :
    view v ∈ (processSuccessors INV starts adj view rd fpSt curr h_curr st).seen := by
  unfold processSuccessors at h_post_no_cex
  let neighbors := (adj curr).attach
  have h_lv_in_neighbors : ⟨(l, v), h_in⟩ ∈ neighbors := by
    simp [neighbors, List.mem_attach]
  have h_fold_adds_all : ∀ (list : List {x // x ∈ adj curr}) (s : SearchContext σ κ σₕ starts adj view),
      s.termination = false →
      s.counterexample = [] →
      (list.foldl (fun current_st ⟨neighbor, h_neighbor_in_adj⟩ =>
        if current_st.termination then current_st
        else
          let h_neighbor_reachable := Reachable.step h_curr h_neighbor_in_adj
          processNeighbor INV starts adj view rd fpSt current_st neighbor h_neighbor_reachable
      ) s).counterexample = [] →
      ∀ (neighbor : κ × σ) (h_mem : neighbor ∈ adj curr),
        ⟨neighbor, h_mem⟩ ∈ list →
        view neighbor.2 ∈ (list.foldl (fun current_st ⟨neighbor, h_neighbor_in_adj⟩ =>
          if current_st.termination then current_st
          else
            let h_neighbor_reachable := Reachable.step h_curr h_neighbor_in_adj
            processNeighbor INV starts adj view rd fpSt current_st neighbor h_neighbor_reachable
        ) s).seen := by
    intro list s h_s_no_term h_s_no_cex h_result_no_cex neighbor h_mem h_neighbor_in_list
    induction list generalizing s with
    | nil =>
      simp at h_neighbor_in_list
    | cons head tail ih =>
      obtain ⟨head_neighbor, head_h⟩ := head
      let h_head_reach := Reachable.step h_curr head_h
      rw [List.foldl_cons]
      simp at h_neighbor_in_list
      cases h_neighbor_in_list with
      | inl h_is_head =>
        simp at h_is_head
        rw [h_is_head]
        by_cases h_term : s.termination = true
        · simp [h_term]; grind
        · have h_term_false : s.termination = false := by grind
          simp only [h_term_false]
          have h_in_s' : view head_neighbor.2 ∈ (processNeighbor INV starts adj view rd fpSt s head_neighbor h_head_reach).seen :=
            processNeighbor_adds_neighbor INV starts adj view rd fpSt s head_neighbor h_head_reach
          exact foldl_processNeighbor_seen_monotone INV starts adj view rd fpSt curr h_curr
            tail (processNeighbor INV starts adj view rd fpSt s head_neighbor h_head_reach) (view head_neighbor.2) h_in_s'
      | inr h_in_tail =>
        by_cases h_term : s.termination = true
        · simp [h_term]; grind
        · have h_term_false : s.termination = false := by grind
          simp only [h_term_false]
          let s' := processNeighbor INV starts adj view rd fpSt s head_neighbor h_head_reach
          have h_tail_result_no_cex : (tail.foldl (fun current_st ⟨neighbor, h_neighbor_in_adj⟩ =>
              if current_st.termination then current_st
              else
                let h_neighbor_reachable := Reachable.step h_curr h_neighbor_in_adj
                processNeighbor INV starts adj view rd fpSt current_st neighbor h_neighbor_reachable
            ) s').counterexample = [] := by
            have h_expand : (⟨head_neighbor, head_h⟩ :: tail).foldl (fun current_st ⟨neighbor, h_neighbor_in_adj⟩ =>
                if current_st.termination then current_st
                else
                  let h_neighbor_reachable := Reachable.step h_curr h_neighbor_in_adj
                  processNeighbor INV starts adj view rd fpSt current_st neighbor h_neighbor_reachable
              ) s = tail.foldl (fun current_st ⟨neighbor, h_neighbor_in_adj⟩ =>
                if current_st.termination then current_st
                else
                  let h_neighbor_reachable := Reachable.step h_curr h_neighbor_in_adj
                  processNeighbor INV starts adj view rd fpSt current_st neighbor h_neighbor_reachable
              ) s' := by
              rw [List.foldl_cons]
              show tail.foldl _ (if s.termination then s else processNeighbor INV starts adj view rd fpSt s head_neighbor h_head_reach) =
                   tail.foldl _ s'
              simp only [h_term_false]
              rfl
            rw [←h_expand]
            exact h_result_no_cex
          have h_s'_no_cex : s'.counterexample = [] := by
            by_contra h_not_empty
            have ⟨x, hx⟩ : ∃ x, x ∈ s'.counterexample := by
              cases h : s'.counterexample with
              | nil => contradiction
              | cons head tail => exact ⟨head, by simp⟩
            have h_cex_mono_local : ∀ (lst : List {y // y ∈ adj curr}) (st_base : SearchContext σ κ σₕ starts adj view) (elem : σₕ),
                elem ∈ st_base.counterexample →
                elem ∈ (lst.foldl (fun current_st ⟨neighbor, h_neighbor_in_adj⟩ =>
                  if current_st.termination then current_st
                  else processNeighbor INV starts adj view rd fpSt current_st neighbor (Reachable.step h_curr h_neighbor_in_adj)
                ) st_base).counterexample := by
              intro lst st_base elem h_elem
              induction lst generalizing st_base with
              | nil => simp; exact h_elem
              | cons list_hd list_tl list_ih =>
                obtain ⟨nb_elem, nb_proof⟩ := list_hd
                rw [List.foldl_cons]
                by_cases h_st_term : st_base.termination = true
                · simp only [h_st_term, ite_true]
                  exact list_ih st_base h_elem
                · simp only [h_st_term]
                  have h_elem_next : elem ∈ (processNeighbor INV starts adj view rd fpSt st_base nb_elem (Reachable.step h_curr nb_proof)).counterexample :=
                    processNeighbor_counterexample_monotone INV starts adj view rd fpSt st_base nb_elem _ elem h_elem
                  exact list_ih _ h_elem_next
            have hx_in_result := h_cex_mono_local tail s' x hx
            rw [h_tail_result_no_cex] at hx_in_result
            simp at hx_in_result
          have h_s'_no_term : s'.termination = false := by
            grind [processNeighbor]
          grind
  exact h_fold_adds_all neighbors st h_pre_term h_pre_cex h_post_no_cex (l, v) h_in h_lv_in_neighbors

lemma foldl_processNeighbor_counterexample_monotone
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ) (fpSt : σₕ)
    (curr : σ)
    (h_curr : Reachable adj starts curr)
    (list : List {x // x ∈ adj curr})
    (st : SearchContext σ κ σₕ starts adj view)
    (x : σₕ)
    (h_in : x ∈ st.counterexample) :
    x ∈ (list.foldl (fun current_st ⟨neighbor, h_neighbor_in_adj⟩ =>
      if current_st.termination then current_st
      else
        let h_neighbor_reachable := Reachable.step h_curr h_neighbor_in_adj
        processNeighbor INV starts adj view rd fpSt current_st neighbor h_neighbor_reachable
    ) st).counterexample := by
  induction list generalizing st with
  | nil =>
    rw [List.foldl_nil]
    exact h_in
  | cons head tail ih =>
    rw [List.foldl_cons]
    obtain ⟨neighbor, h_neighbor_in_adj⟩ := head
    let h_reach := Reachable.step h_curr h_neighbor_in_adj
    by_cases h_term : st.termination = true
    · simp only [h_term, ite_true]
      exact ih st h_in
    · have h_term_false : st.termination = false := by grind
      simp only [h_term_false]
      let st' := processNeighbor INV starts adj view rd fpSt st neighbor h_reach
      have h_in_st' : x ∈ st'.counterexample :=
        processNeighbor_counterexample_monotone INV starts adj view rd fpSt st neighbor h_reach x h_in
      exact ih st' h_in_st'

lemma processNeighbor_newly_seen_in_queue
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ) (fpSt : σₕ)
    (st : SearchContext σ κ σₕ starts adj view)
    (neighbor : κ × σ)
    (h_reach : Reachable adj starts neighbor.2)
    (fp : σₕ)
    (h_fp_not_in_st : fp ∉ st.seen)
    (h_fp_eq : fp = view neighbor.2)
    (h_result_no_cex : (processNeighbor INV starts adj view rd fpSt st neighbor h_reach).counterexample = []) :
    ∃ s, (fp, s) ∈ (processNeighbor INV starts adj view rd fpSt st neighbor h_reach).sq.toList ∧ view s = fp := by
  unfold processNeighbor
  obtain ⟨label, succ⟩ := neighbor
  simp at h_fp_eq
  subst h_fp_eq
  by_cases h_contains : st.seen.contains (view succ)
  <;> grind[processNeighbor]

lemma processSuccessors_newly_seen_in_queue
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ) (fpSt : σₕ)
    (curr : σ)
    (h_curr : Reachable adj starts curr)
    (st : SearchContext σ κ σₕ starts adj view)
    (fp : σₕ)
    (h_fp_not_in_st : fp ∉ st.seen)
    (h_st_no_term : st.termination = false)
    (h_st_no_cex : st.counterexample = [])
    (h_fp_in_result : fp ∈ (processSuccessors INV starts adj view rd fpSt curr h_curr st).seen)
    (h_result_no_cex : (processSuccessors INV starts adj view rd fpSt curr h_curr st).counterexample = []) :
    ∃ s, (fp, s) ∈ (processSuccessors INV starts adj view rd fpSt curr h_curr st).sq.toList ∧ view s = fp := by
  unfold processSuccessors at h_fp_in_result h_result_no_cex
  let neighbors := (adj curr).attach
  suffices ∀ (list : List {x // x ∈ adj curr}) (s : SearchContext σ κ σₕ starts adj view),
    fp ∉ s.seen →
    s.termination = false →
    s.counterexample = [] →
    fp ∈ (list.foldl (fun current_st ⟨neighbor, h_neighbor_in_adj⟩ =>
      if current_st.termination then current_st
      else
        let h_neighbor_reachable := Reachable.step h_curr h_neighbor_in_adj
        processNeighbor INV starts adj view rd fpSt current_st neighbor h_neighbor_reachable
    ) s).seen →
    (list.foldl (fun current_st ⟨neighbor, h_neighbor_in_adj⟩ =>
      if current_st.termination then current_st
      else
        let h_neighbor_reachable := Reachable.step h_curr h_neighbor_in_adj
        processNeighbor INV starts adj view rd fpSt current_st neighbor h_neighbor_reachable
    ) s).counterexample = [] →
    ∃ s_res, (fp, s_res) ∈ (list.foldl (fun current_st ⟨neighbor, h_neighbor_in_adj⟩ =>
      if current_st.termination then current_st
      else
        let h_neighbor_reachable := Reachable.step h_curr h_neighbor_in_adj
        processNeighbor INV starts adj view rd fpSt current_st neighbor h_neighbor_reachable
    ) s).sq.toList ∧ view s_res = fp by
    exact this neighbors st h_fp_not_in_st h_st_no_term h_st_no_cex h_fp_in_result h_result_no_cex
  intro list s h_fp_not_in_s h_s_no_term h_s_no_cex h_fp_in_result_local h_result_no_cex_local
  induction list generalizing s with
  | nil => grind
  | cons head tail ih =>
    obtain ⟨neighbor, h_neighbor_in_adj⟩ := head
    let h_reach := Reachable.step h_curr h_neighbor_in_adj
    rw [List.foldl_cons] at h_fp_in_result_local h_result_no_cex_local ⊢
    simp only [h_s_no_term] at h_fp_in_result_local h_result_no_cex_local ⊢
    let s' := processNeighbor INV starts adj view rd fpSt s neighbor h_reach
    by_cases h_fp_in_s' : fp ∈ s'.seen
    · have h_fp_eq : fp = view neighbor.2 := by
        unfold processNeighbor at h_fp_in_s'
        by_cases h_contains : s.seen.contains (view neighbor.2)
        <;> grind[processNeighbor]
      have h_s'_no_cex : s'.counterexample = [] := by
        by_contra h_not_empty
        have ⟨x, hx⟩ : ∃ x, x ∈ s'.counterexample := by
          cases h : s'.counterexample with
          | nil => contradiction
          | cons head tail => exact ⟨head, by simp⟩
        have hx_in_result := foldl_processNeighbor_counterexample_monotone INV starts adj view rd fpSt
          curr h_curr tail s' x hx
        grind
      have ⟨s_neighbor, h_in_s'_queue, h_view_s_neighbor⟩ :=
        processNeighbor_newly_seen_in_queue INV starts adj view rd fpSt s neighbor h_reach fp
          h_fp_not_in_s h_fp_eq h_s'_no_cex
      have h_in_result_queue := foldl_processNeighbor_queue_monotone INV starts adj view rd fpSt
      grind
    · -- fp ∉ s'.seen
      have h_s'_no_term : s'.termination = false := by
        have h_s'_no_cex : s'.counterexample = [] := by
          by_contra h_not_empty
          have ⟨x, hx⟩ : ∃ x, x ∈ s'.counterexample := by
            cases h : s'.counterexample with
            | nil => contradiction
            | cons head tail => exact ⟨head, by simp⟩
          have hx_in_result := foldl_processNeighbor_counterexample_monotone INV starts adj view rd fpSt
            curr h_curr tail s' x hx
          grind
        grind[processNeighbor]
      have h_s'_no_cex : s'.counterexample = [] := by
        by_contra h_not_empty
        have ⟨x, hx⟩ : ∃ x, x ∈ s'.counterexample := by
          cases h : s'.counterexample with
          | nil => contradiction
          | cons head tail => exact ⟨head, by simp⟩
        have hx_in_result := foldl_processNeighbor_counterexample_monotone INV starts adj view rd fpSt
          curr h_curr tail s' x hx
        grind
      exact ih s' h_fp_in_s' h_s'_no_term h_s'_no_cex h_fp_in_result_local h_result_no_cex_local


theorem bfsStep_preserves_closed_invariant
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (rd : ρ)
    (pre : SearchContext σ κ σₕ starts adj view)
    (h_term_consist : normal_termination_implies_empty_queue starts adj view pre)
    (h_inv : closed_invariant starts adj view pre) :
    closed_invariant starts adj view (bfsStep INV Terminate starts adj view rd pre) := by
  unfold closed_invariant at *
  intro h_view_inj h_post_no_cex u h_u_in_seen h_u_not_in_queue l v h_lv_in_adj
  have h_pre_no_cex : pre.counterexample = [] :=
    bfsStep_empty_counterexample_implies_pre_empty INV Terminate starts adj view rd pre h_post_no_cex
  have h_pre_closed := h_inv h_view_inj h_pre_no_cex
  unfold bfsStep at h_u_in_seen h_u_not_in_queue h_post_no_cex
  split at h_u_in_seen
  case h_1 h_none =>
    simp at h_u_in_seen
    simp at h_u_not_in_queue
    have h_pre_u_not_in_q : ⟨view u, u⟩ ∉ pre.sq.toList := by grind
    have h_pre_closed' := h_pre_closed u h_u_in_seen h_pre_u_not_in_q l v h_lv_in_adj
    rw [bfsStep]; grind
  case h_2 h_some val =>
    simp at h_u_in_seen
    simp at h_u_not_in_queue
    rename_i fpSt curr
    cases h_adj : adj curr with
    | nil =>
      simp only [h_adj] at h_u_in_seen h_u_not_in_queue ⊢
      by_cases h_eq : u = curr
      · subst h_eq; rw [h_adj] at h_lv_in_adj
        contradiction
      · have h_u_not_in_pre_sq : (view u, u) ∉ pre.sq.toList := by
          have h_q_decomp : pre.sq.toList = (fpSt, curr) :: h_some.toList := by
            have spec := dequeue?_spec pre.sq
            grind
          rw [h_q_decomp]
          simp only [List.mem_cons, Prod.mk.injEq]
          push_neg
          constructor
          · intro h_view_eq _
            apply h_eq
            grind
          · split at h_u_not_in_queue <;> grind
        have h_v_in_pre_seen := h_pre_closed u (by
            split at h_u_in_seen <;> assumption
          ) h_u_not_in_pre_sq l v h_lv_in_adj
        simp [bfsStep]
        grind
    | cons head tail =>
      by_cases h_eq : u = curr
      · have h_toList : pre.sq.toList = (fpSt, curr) :: h_some.toList := by
          have spec := dequeue?_spec pre.sq
          grind
        have h_fpSt_eq : fpSt = view curr := by
          apply pre.queue_wellformed
          grind
        have h_curr_reach : Reachable adj starts curr := by
          have h_in : (view curr, curr) ∈ pre.sq.toList := by grind
          exact pre.queue_sound curr h_in
        -- Build st_dequeued
        let st_dequeued : SearchContext σ κ σₕ starts adj view := {
          pre with
          sq := h_some,
          queue_sound := by grind
          visited_sound := pre.visited_sound
          queue_sub_visited := by grind
          queue_wellformed := by grind }
        have h_st_no_term : st_dequeued.termination = false := by
          simp [st_dequeued]
          by_contra h_term
          simp at h_term
          have h_pre_queue_empty := h_term_consist ⟨h_term, h_pre_no_cex⟩
          rw [h_toList] at h_pre_queue_empty
          simp at h_pre_queue_empty
        have h_st_no_cex : st_dequeued.counterexample = [] := by grind
        have h_result_no_cex : (processSuccessors INV starts adj view rd fpSt curr h_curr_reach st_dequeued).counterexample = [] := by
          simp at h_post_no_cex
          grind
        have h_lv_in_adj_curr : (l, v) ∈ adj curr := h_eq ▸ h_lv_in_adj
        have h_v_in_result : view v ∈ (processSuccessors INV starts adj view rd fpSt curr h_curr_reach st_dequeued).seen :=
          processSuccessors_sees_neighbors_of_no_cex INV starts adj view rd fpSt curr h_curr_reach
            st_dequeued l v h_lv_in_adj_curr h_st_no_term h_st_no_cex h_result_no_cex
        show view v ∈ (bfsStep INV Terminate starts adj view rd pre).seen
        simp only [bfsStep]
        grind
      · have h_curr_reach : Reachable adj starts curr := by
          have h_sound := pre.queue_sound
          have h_fp_eq := pre.queue_wellformed fpSt curr
          grind
        have h_u_not_in_pre_queue : (view u, u) ∉ pre.sq.toList := by
          intro h_in_pre_q
          have h_toList : pre.sq.toList = (fpSt, curr) :: h_some.toList := by
            have spec := dequeue?_spec pre.sq
            rw [val] at spec
            simp at spec
            exact spec
          rw [h_toList] at h_in_pre_q
          simp at h_in_pre_q
          cases h_in_pre_q with
          | inl h_is_curr =>
            obtain ⟨h_fp_eq, h_u_eq_curr⟩ := h_is_curr
            exact h_eq h_u_eq_curr
          | inr h_in_tail =>
            have h_toList_pre : pre.sq.toList = (fpSt, curr) :: h_some.toList := by grind
            have h_fpSt_eq : fpSt = view curr := by apply pre.queue_wellformed; grind
            have h_curr_reach : Reachable adj starts curr := by grind
            apply h_u_not_in_queue
            have h_queue_monotone := processSuccessors_queue_monotone INV starts adj view rd fpSt curr h_curr_reach
              { pre with
                sq := h_some,
                queue_sound := by grind
                visited_sound := pre.visited_sound
                queue_sub_visited := by grind
                queue_wellformed := by grind
              } u h_in_tail
            grind
        have h_u_in_pre_seen : view u ∈ pre.seen := by
          by_contra h_not_in_pre_seen
          let st_dequeued : SearchContext σ κ σₕ starts adj view := {
            pre with
            sq := h_some,
            queue_sound := by grind
            visited_sound := pre.visited_sound
            queue_sub_visited := by grind
            queue_wellformed := by grind }
          let post := processSuccessors INV starts adj view rd fpSt curr h_curr_reach st_dequeued
          have h_curr_reach : Reachable adj starts curr := by grind
          have h_st_dequeued_no_term : st_dequeued.termination = false := by
            simp [st_dequeued]
            by_contra h_term
            simp at h_term
            have h_pre_queue_empty := h_term_consist ⟨h_term, h_pre_no_cex⟩
            have h_toList : pre.sq.toList = (fpSt, curr) :: h_some.toList := by grind
            rw [h_toList] at h_pre_queue_empty
            simp at h_pre_queue_empty
          have h_result_no_cex : (processSuccessors INV starts adj view rd fpSt curr h_curr_reach st_dequeued).counterexample = [] := by
            simp at h_post_no_cex
            grind
          have h_u_not_in_st_seen : view u ∉ st_dequeued.seen := by
            simp [st_dequeued]
            exact h_not_in_pre_seen
          have h_u_in_post_seen : view u ∈ post.seen := by
            simp only [h_adj] at h_u_in_seen
            exact h_u_in_seen
          have ⟨s, h_in_queue, h_view_s⟩ := processSuccessors_newly_seen_in_queue INV
              starts adj view rd fpSt
              curr h_curr_reach st_dequeued (view u)
              h_u_not_in_st_seen h_st_dequeued_no_term h_pre_no_cex
              h_u_in_post_seen h_result_no_cex
          have h_s_eq_u : s = u := h_view_inj h_view_s
          have h_u_in_post_sq : (view u, u) ∈ post.sq.toList := by
            rw [←h_s_eq_u]
            grind
          have h_bfs_eq_post : (bfsStep INV Terminate starts adj view rd pre).sq.toList = post.sq.toList := by
            simp [bfsStep, h_adj]
            grind
          rw [←h_bfs_eq_post] at h_u_in_post_sq
          grind
        have h_v_in_pre_seen := h_pre_closed u h_u_in_pre_seen h_u_not_in_pre_queue l v h_lv_in_adj
        exact bfsStep_seen_monotone INV Terminate starts adj view rd pre (view v) h_v_in_pre_seen


/-- The `completeness` theorem for BFS search, states that:
if the algorithm can terminate without finding any counterexample,
then all the reachable states have been `visited`.

Here `bfs_preserves_starts_in_seen`, `bfsStep_preserves_closed_invariant`, and
`bfsStep_preserves_normal_termination_implies_empty_queue`
are the lemmas that correspond to the three invariants,
which have been proved for `bfsStep`.
 -/
theorem bfsStep_completeness_from_invariants
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    (st : SearchContext σ κ σₕ starts adj view)
    (h_view_inj : Function.Injective view)
    /- Corresponds to `bfs_preserves_starts_in_seen` -/
    (h_starts : starts_in_seen starts adj view st)
    /- Corresponds to `bfsStep_preserves_closed_invariant` -/
    (h_closed : closed_invariant starts adj view st)
    /- Corresponds to `bfsStep_preserves_normal_termination_implies_empty_queue` -/
    (h_term_consist : normal_termination_implies_empty_queue starts adj view st)
    (h_term : st.termination = true)
    (h_no_cex : st.counterexample = []) :
    ∀ x : σ, Reachable adj starts x → (view x) ∈ st.seen := by
  intro x h_reach
  induction h_reach
  case base s h_s_in_starts =>
    exact h_starts s h_s_in_starts
  case step u v h_u_reach h_lv_in_adj ih =>
    have h_queue_empty : st.sq.toList = [] :=
      h_term_consist ⟨h_term, h_no_cex⟩
    have h_u_not_in_queue : ⟨view u, u⟩ ∈ st.sq.toList → False := by
      intros h_in
      rw [h_queue_empty] at h_in
      simp at h_in
    have h_closed_u := h_closed h_view_inj h_no_cex u ih h_u_not_in_queue
    exact h_closed_u _ _ h_lv_in_adj
