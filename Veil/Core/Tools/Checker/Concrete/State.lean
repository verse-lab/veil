import Veil.Frontend.DSL.State.SubState
import Veil.Frontend.DSL.Action.Semantics.Definitions
import Veil.Core.Tools.Checker.Concrete.DataStructure
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Lean
open Veil
open Std

variable {ℂ ℝ 𝔸: Type}
/-
- `κᵣ` :  set as Std.Format by default
- `κ`  :  State.Label
- `ρ`  :  Reader type
- `σ` :  Concrete state representation type
-/
variable {κ κᵣ ρ σ α: Type}
variable {ε σ: Type}

/-- Extract the resulting state from an ExceptT-wrapped execution, if successful. -/
def getStateFromExceptT (c : ExceptT ε DivM (α × σ)) : Option σ :=
  match c.run with
  | .res (.ok (_, st)) => .some st
  | .res (.error _)    => .none
  | .div => none

def getAllStatesFromExceptT (c : List (ExceptT ε DivM (α × σ))) : List (Option σ) :=
  c.map getStateFromExceptT

/-- Extract all valid states from a VeilMultiExecM computation -/
def extractValidStates (exec : VeilMultiExecM κᵣ ℤ ρ σ Unit) (rd : ρ) (st : σ) : List (Option σ) :=
  exec rd st |>.map Prod.snd |> getAllStatesFromExceptT

/- Corresponds to `after_init` action, used for initialization -/
variable (initVeilMultiExecM : VeilMultiExecM κᵣ ℤ ρ σ Unit)
variable (nextVeilMultiExecM : κ → VeilMultiExecM κᵣ ℤ ρ σ Unit)

abbrev TsilE (κᵣ σ : Type) := TsilT (ExceptT ℤ (PeDivM (List κᵣ))) (Unit × σ)

def afterInit (rd : ρ) (s₀ : σ) : TsilE κᵣ σ :=
  ((initVeilMultiExecM |> ReaderT.run) rd |> StateT.run) s₀

/- Get all possible next states from current state `s` under label `l`. -/
def nonDetNexts (rd : ρ) (st : σ) (l : κ) : TsilE κᵣ σ :=
  nextVeilMultiExecM l rd st

def adjExec (rd : ρ) (st : σ) (l : κ) : List σ:=
  let execs := nextVeilMultiExecM l rd st
  let succs := getAllStatesFromExceptT (execs.map Prod.snd) |> List.filterMap id
  succs

/-
We do not require `Repr` instances for `σ` and `κ` here, aimming to
seperate the concerns of model checking algorithm and representation.

`σₕ` is the type fingerprint, used for storage.
`σₕ` is usually in HashSet, which requires `Ord` and `Hashable` instance.

`σ` need `Inhabited` instance, which is used in initialization.

TODO: If we hope to allow use `symmetric reduction`, then `σ` requires
`Ord` instance, to make it comparable between each other.
-/
variable {σₕ : Type}
variable [Inhabited σ] [Hashable σ]
variable [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [EquivBEq σₕ] [LawfulHashable σₕ]
variable (allLabels : List κ)
variable (INV : ρ → σ → Prop)
variable (Terminate : ρ → σ → Prop)
variable [dec_inv: ∀rd : ρ, ∀st : σ, Decidable (INV rd st)]
variable [dec_term: ∀rd : ρ, ∀st : σ, Decidable (Terminate rd st)]
variable [IsSubStateOf ℂ σ]
variable [IsSubReaderOf ℝ ρ]


def adjMap (rd : ρ) (pre : σ) : List (κ × σ) := Id.run do
  let mut res : List (κ × σ) := []
  for l in allLabels do
    let succs := adjExec nextVeilMultiExecM rd pre l
    for s in succs do
      res := res.append [(l, s)]
  res


/-- Process a single neighbor node during BFS traversal.
If the neighbor has been seen, return the current state unchanged
Otherwise, add it to seen set and log,
then either enqueue it (if valid) or mark as counterexample.-/
def processNeighbor
    (starts : List σ)
    (adj : σ → List (κ × σ))
    (view : σ → σₕ)
    -- (h_view_inj : Function.Injective view)
    (rd : ρ) (fpSt : σₕ)
    (current_st : SearchContext σ κ σₕ starts adj view)
    (neighbor : κ × σ)
    (h_neighbor : Reachable adj starts neighbor.2)
  : SearchContext σ κ σₕ starts adj view :=
  let ⟨label, succ⟩ := neighbor
  let fingerprint := view succ
  if current_st.seen.contains fingerprint then current_st
  else
    let st_with_seen : SearchContext σ κ σₕ starts adj view :=
      { current_st with
          seen := current_st.seen.insert fingerprint,
          log := current_st.log.insert fingerprint (fpSt, label),
          queue_sound := by
            intros x h_in
            by_cases h_eq : x = succ
            . simp at h_neighbor
              rw [←h_eq] at h_neighbor
              exact h_neighbor
            . have h_neq : x ≠ succ := h_eq
              have h_in_seen := current_st.queue_sound x h_in
              exact h_in_seen
          visited_sound := by
            intro h_view_inj
            intros x h_in
            rw [HashSet.mem_insert] at h_in
            cases h_in with
            | inl h_eq =>
              -- (fingerprint == view x) = true
              simp [fingerprint] at h_eq
              -- h_eq : view succ = view x (after simp)
              have h_x_eq_succ : x = succ := h_view_inj h_eq.symm
              rw [h_x_eq_succ]
              exact h_neighbor
            | inr h_in_old =>
              -- view x ∈ current_st.seen
              exact current_st.visited_sound h_view_inj x h_in_old
          queue_sub_visited := by
            intros x h_in
            have h_in_old_seen := current_st.queue_sub_visited x h_in
            rw [HashSet.mem_insert]
            right
            exact h_in_old_seen
          queue_wellformed := current_st.queue_wellformed
           }
    if decide (INV rd succ) then
      { st_with_seen with
          sq := st_with_seen.sq.enqueue (fingerprint, succ),
          termination := false,
          queue_sound := by
            intros x h_in
            rw [toList_enqueue] at h_in
            rw [List.mem_append] at h_in
            cases h_in with
            | inl h_in_old => exact st_with_seen.queue_sound x h_in_old
            | inr h_is_new =>
              simp at h_is_new
              obtain ⟨h_fp_eq, h_x_eq⟩ := h_is_new
              rw [h_x_eq]
              exact h_neighbor
          queue_sub_visited := by
            intros x h_in
            rw [toList_enqueue] at h_in
            rw [List.mem_append] at h_in
            cases h_in with
            | inl h_in_old => exact st_with_seen.queue_sub_visited x h_in_old
            | inr h_is_new =>
              simp at h_is_new
              obtain ⟨h_fp_eq, h_x_eq⟩ := h_is_new
              rw [h_fp_eq]
              rw [HashSet.mem_insert]
              left
              simp
          queue_wellformed := by
            intros fp st h_in
            rw [toList_enqueue] at h_in
            rw [List.mem_append] at h_in
            cases h_in with
            | inl h_in_old => exact st_with_seen.queue_wellformed fp st h_in_old
            | inr h_is_new =>
              simp at h_is_new
              obtain ⟨h_fp_eq, h_st_eq⟩ := h_is_new
              rw [h_st_eq]
              exact h_fp_eq }
    else
      { st_with_seen with
          counterexample := fingerprint :: st_with_seen.counterexample,
          termination := true,
          queue_wellformed := st_with_seen.queue_wellformed }


def processSuccessors
  (starts : List σ)
  (adj : σ → List (κ × σ))
  (view : σ → σₕ)
  (rd : ρ) (fpSt : σₕ)
  (curr : σ)
  (h_curr : Reachable adj starts curr)
  (st : SearchContext σ κ σₕ starts adj view)
  : SearchContext σ κ σₕ starts adj view :=
  (adj curr).attach.foldl (fun current_st ⟨neighbor, h_neighbor_in_adj⟩ =>
    if current_st.termination then current_st
    else
      let h_neighbor_reachable := Reachable.step h_curr h_neighbor_in_adj
      processNeighbor INV starts adj view rd fpSt current_st neighbor h_neighbor_reachable
  ) st


def bfsStep (starts : List σ)
  (adj : σ → List (κ × σ))
  (view : σ → σₕ) (rd : ρ)
  (pre : SearchContext σ κ σₕ starts adj view)
  : SearchContext σ κ σₕ starts adj view :=
  match h_deq : pre.sq.dequeue? with
  | none => { pre with termination := true }
  | some ((fpSt, curr), q_tail) =>
    have h_toList : pre.sq.toList = (fpSt, curr) :: q_tail.toList := by grind
    have h_fpSt_eq : fpSt = view curr := by
      have h_in_queue : (fpSt, curr) ∈ pre.sq.toList := by grind
      exact pre.queue_wellformed fpSt curr h_in_queue
    have h_curr : Reachable adj starts curr := by
      have h_in : (view curr, curr) ∈ pre.sq.toList := by grind
      exact pre.queue_sound curr h_in
    let st_dequeued : SearchContext σ κ σₕ starts adj view := {
      pre with
      sq := q_tail,
      queue_sound := by
        intros x h_in
        apply pre.queue_sound
        grind
      visited_sound := pre.visited_sound
      queue_sub_visited := by
        intros x h_in
        have h_in_pre : (view x, x) ∈ pre.sq.toList := by grind
        exact pre.queue_sub_visited x h_in_pre
      queue_wellformed := by
        intros fp st h_in
        have h_in_pre : (fp, st) ∈ pre.sq.toList := by grind
        exact pre.queue_wellformed fp st h_in_pre }
    let successors := adj curr
    match successors with
    | _ :: _ => processSuccessors INV starts adj view rd fpSt curr h_curr st_dequeued
    | [] =>
      if decide (Terminate rd curr) then
        st_dequeued
      else
        { st_dequeued with
            counterexample := fpSt :: st_dequeued.counterexample,
            termination := true }


/-- Run the model checker with imperative-style code.
    Returns a pair of unit and the final search context.
    Note: The `starts` parameter is set to init_states extracted from the initial execution.
    The `adj` parameter is partially applied with `rd`. -/
def runModelCheckerx (rd : ρ) (view : σ → σₕ)
  : Option σₕ × Option (SearchContext σ κ σₕ (extractValidStates initVeilMultiExecM rd default |>.filterMap id) (adjMap nextVeilMultiExecM allLabels rd) view) := Id.run do
  -- Extract all valid initial states
  let init_states := extractValidStates initVeilMultiExecM rd default |>.filterMap id
  for st in init_states do
    if !(decide (INV rd st)) then
      return (some (view st), none)
      -- panic! "Initial state does not satisfy the invariant."

  let adj := adjMap nextVeilMultiExecM allLabels rd
  let initSearchContext : SearchContext σ κ σₕ init_states adj view := {
    seen := insertListIntoHashSet (init_states.map view) HashSet.emptyWithCapacity,
    sq := insertListIntofQueue (init_states.map (fun s => (view s, s))),
    log := Std.HashMap.emptyWithCapacity,
    counterexample := [],
    termination := false,
    queue_sound := by
      intros x h_in
      have h_in_init : x ∈ init_states := by
        unfold insertListIntofQueue at h_in
        simp at h_in
        grind
      exact Reachable.base h_in_init
    visited_sound := by
      intros h_view_inj x h_in
      have h_in_init : x ∈ init_states := by
        unfold insertListIntoHashSet at h_in
        have h_in_list : view x ∈ init_states.map view := by
          apply mem_list_of_mem_foldl_insert
          exact h_in
        rw [List.mem_map] at h_in_list
        obtain ⟨s, h_s_in, h_eq_view⟩ := h_in_list
        have h_eq_st : s = x := h_view_inj h_eq_view
        rw [←h_eq_st]
        exact h_s_in
      exact Reachable.base h_in_init
    queue_sub_visited := by
      intros x h_in
      unfold insertListIntofQueue at h_in
      unfold insertListIntoHashSet
      simp at h_in
      have h_view_in_list : view x ∈ List.map view init_states := by
        apply List.mem_map.mpr
        refine ⟨x, h_in, rfl⟩
      have : view x ∈ List.foldl (fun acc x => acc.insert x)
                HashSet.emptyWithCapacity (List.map view init_states) :=
        mem_foldl_insert_of_mem (l := List.map view init_states)
                                (a := view x)
                                h_view_in_list
      grind
    queue_wellformed := by
      intros fp st h_in
      unfold insertListIntofQueue at h_in
      simp at h_in
      obtain ⟨h_fp_eq, h_st_eq⟩ := h_in
      grind
  }

  -- BFS loop
  let mut current_cfg := initSearchContext
  while !current_cfg.termination do
    current_cfg := bfsStep INV Terminate init_states adj view rd current_cfg
  return (none, some current_cfg)


def recoverTrace [Hashable σ] [Repr κ] (rd : ρ) (traces : List (Trace UInt64 κ))
  : Trace σ κ := Id.run do
  if traces.isEmpty then
    return { start := default, steps := [] }
  /- Actually, we can assert that there is only one trace returned by `collectTrace.`
  Because when encounter counterexample, the model checker will terminate at once.-/
  let trace := traces[0]!
  let findByHash (succs : List (Option σ)) (targetHash : UInt64) (fallback : σ) : σ :=
    succs.filterMap id |>.find? (fun s => hash s == targetHash) |>.getD fallback
  -- Recover initial state
  let initSuccs := extractValidStates initVeilMultiExecM rd default
  let start := findByHash initSuccs trace.start default
  -- Recover trace steps
  let mut curSt := start
  let mut steps : List (Step σ κ) := []
  for step in trace.steps do
    let succs := extractValidStates (nextVeilMultiExecM step.label) rd curSt
    let nextSt := findByHash succs step.next curSt
    curSt := nextSt
    steps := steps.append [{ label := step.label, next := nextSt }]
  return { start := start, steps := steps }
