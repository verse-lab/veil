import Std.Data.HashSet

/-- Functional Queue, from https://vfoley.xyz/functional-queues. -/
structure fQueue (α : Type) where
  front : List α
  back : List α
deriving Inhabited, Repr

namespace fQueue
def empty {α} : fQueue α := ⟨[], []⟩

def norm {α} (q : fQueue α) : fQueue α :=
  match q.front with
  | []    => ⟨q.back.reverse, []⟩
  | _::_  => q

def enqueue {α} (q : fQueue α) (x : α) : fQueue α :=
  ⟨q.front, x :: q.back⟩            -- O(1)

def dequeue? {α} (q : fQueue α) : Option (α × fQueue α) :=
  match (norm q).front with
  | []        => none
  | x :: xs   => some (x, ⟨xs, (norm q).back⟩)

def toList {α} (q : fQueue α) : List α :=
  q.front ++ q.back.reverse
end fQueue

/--
The State defintion of the model checker:

- α is the original type of the state, i.e., State used in veil's syntax.
- β is the type of the state that we used to store, e.g., StateConcrete.
- log is the list of transitions that have been seen.
- counterexample is the list of states that have been seen and are not valid.
-/
structure SearchContext (α β κ : Type) [BEq β] [Hashable β] where
  seen : Std.HashSet β
  sq   : fQueue (α × β)
  /- We use a `HashMap σ_post (σ_pre × κ)` to store the log of transitions, which
  will make it easier to reconstruct counterexample trace. -/
  log : Std.HashMap β (β × κ)
  counterexample : List β
deriving Inhabited

/--
A step in the trace of execution, which contains the label and the next state.
-/
structure Step (σᵣ κ: Type) where
  label : κ
  next  : σᵣ
deriving Repr, Inhabited

/--
Trace of execution is modeled as a series of steps starting from an initial state,
which is used for showing counterexamples in the frontend.
-/
structure Trace (σᵣ κ : Type) where
  start : σᵣ
  steps : List (Step σᵣ κ)
deriving Repr, Inhabited

instance [Repr β] [Repr κ] : Repr (List (β × β × κ)) where
  reprPrec xs _ :=
    match xs with
    | [] => "[]"
    | (a, b, c) :: rest =>
      let headStr := s!"\n  index:{0}{repr a} \n──[ {repr c} ]──>\n  index:{1}{repr b}"
      let tailStrs :=
        (List.zip (List.range rest.length) rest).map (fun (i, (a, b, c)) =>
          s!"\n──[ {repr c} ]──>\n  index:{i + 2}{repr b}"
        )
      s!"[{headStr}{String.join tailStrs}]"


instance [BEq β] [Hashable β] [Repr κ] [Repr α] [Repr β] : Repr (SearchContext α β κ) where
  reprPrec ctx _ :=
    "{ seen := " ++ repr ctx.seen.toList ++
    ", sq := " ++ repr ctx.sq ++
    ", log := " ++ repr ctx.log ++
    ", counterexample := " ++ repr ctx.counterexample ++ " }"


def SearchContext.empty {α β} [BEq β] [Hashable β] : SearchContext α β κ :=
  { seen := {},
    sq := fQueue.empty,
    log := Std.HashMap.emptyWithCapacity,
    counterexample := [] }


namespace CheckerM

/-- Enqueue state to queue -/
def enqueueState (s : α) (sigₛ : β) [BEq β] [Hashable β]
  : StateT (SearchContext α β κ) Id Unit :=
  modify (fun cs => { cs with sq := fQueue.enqueue cs.sq (s, sigₛ) })

/-- Dequeue state from queue -/
def dequeueState [BEq β] [Hashable β]
  : StateT (SearchContext α β κ) Id (Option (α × β)) := do
  let cs ← get
  match fQueue.dequeue? cs.sq with
  | some ((s, sigₛ), q_tail) =>
    StateT.set { cs with sq := q_tail }
    return some (s, sigₛ)
  | none => return none

/- Check if state has been seen -/
def wasSeen (s : β) [BEq β]
[Hashable β]
  : StateT (SearchContext α β κ) Id Bool := do
  let cs ← get
  return cs.seen.contains s

/-- Add state to seen list -/
def addToSeen (s : β) [BEq β] [Hashable β]
  : StateT (SearchContext α β κ) Id Unit :=
  modify (fun cs =>
    { cs with seen := cs.seen.insert s })

/-- Add transition to log -/
def addTransitionToLog {α β} [BEq β] [Hashable β]
  (s : β) (s' : β) (lab : κ)
  : StateT (SearchContext α β κ) Id Unit :=
  modify (fun cs =>
    { cs with log := cs.log.insert s' (s, lab) })

/-- Add counterexample -/
def addCounterExample (cex : β) [BEq β] [Hashable β]
  : StateT (SearchContext α β κ) Id Unit :=
  modify (fun cs =>
    { cs with counterexample := cex :: cs.counterexample })

end CheckerM

/-
## Functional correctness of the functional queue
`fQueue` is a functional queue implementation with proofs.
`toList` is the list representation of the queue.
`norm` is the normalization function of the queue.
`enqueue` is the enqueue function of the queue.
`dequeue?` is the dequeue function of the queue.

Properties:
- `norm_toList`: `toList (norm q) = toList q`
  : After normalization, the list representation of the queue is the same as the original queue

- `norm_idem`: `norm (norm q) = norm q`
  : Normalization is idempotent

- `norm_eq_self_of_front_ne_nil`: `norm q = q` if `q.front ≠ []`
  : If the front of the queue is non-empty, then the normalized queue is the same as the original queue

- `toList_empty`: `toList (empty : fQueue α) = []`
  : The list representation of the empty queue is empty

- `dequeue?_empty`: `dequeue? (empty : fQueue α) = none`
  : The dequeue function of the empty queue is none

- `toList_enqueue`: `toList (enqueue q x) = toList q ++ [x]`
  : The list representation of the queue after enqueueing an element is the list representation of the queue before enqueueing plus the element

- `dequeue?_spec`: `dequeue? q = some (x, q') ↔ toList q = x :: toList q'`
  : The dequeue function of the queue returns the element at the front of the queue and the queue after dequeueing the element

- `dequeue?_eq_none_iff_toList_nil`: `dequeue? q = none ↔ toList q = []`
  : The dequeue function of the queue returns none
    _if and only if_ the list representation of the queue is empty

- `dequeue?_cons_view`: `toList q = x :: xs → ∃ q', dequeue? q = some (x, q') ∧ toList q' = xs`
  : If the list representation of the queue is a non-empty list,
    then the dequeue function of the queue returns the element at
    the front of the queue and the queue after dequeueing the element
-/
@[simp]
theorem norm_toList {α} (q : fQueue α) :
    fQueue.toList (fQueue.norm q) = fQueue.toList q := by
  cases q with
  | mk f b =>
    cases f with
    | nil =>
      simp [fQueue.norm, fQueue.toList]
    | cons x xs =>
      simp [fQueue.norm, fQueue.toList]

@[simp]
theorem norm_idem {α} (q : fQueue α) :
    fQueue.norm (fQueue.norm q) = fQueue.norm q := by
  cases q with
  | mk f b =>
    cases f with
    | nil =>
      cases b with
      | nil =>
        simp [fQueue.norm]
      | cons y ys =>
        simp [fQueue.norm]
        cases ys.reverse with
        | nil => simp
        | cons _ _ => simp
    | cons _ _ =>
      simp [fQueue.norm]

theorem norm_eq_self_of_front_ne_nil {α} {q : fQueue α} (h : q.front ≠ []) :
    fQueue.norm q = q := by
  cases q with
  | mk f b =>
    cases f with
    | nil => cases h rfl
    | cons _ _ => simp [fQueue.norm]


@[simp]
theorem toList_empty {α : Type} : fQueue.toList (fQueue.empty : fQueue α) = ([] : List α) := by
  simp [fQueue.empty, fQueue.toList]

@[simp]
theorem dequeue?_empty {α : Type} : fQueue.dequeue? (fQueue.empty : fQueue α) = none := by
  simp [fQueue.empty, fQueue.dequeue?, fQueue.norm]


@[simp]
theorem toList_enqueue {α : Type} (q : fQueue α) (x : α) :
    fQueue.toList (fQueue.enqueue q x) = fQueue.toList q ++ [x] := by
  simp [fQueue.toList, fQueue.enqueue, List.reverse_cons, List.append_assoc]


theorem dequeue?_spec {α : Type} (q : fQueue α) :
    match fQueue.dequeue? q with
    | none => fQueue.toList q = []
    | some (x, q') => fQueue.toList q = x :: fQueue.toList q' := by
  unfold fQueue.dequeue?
  cases h : fQueue.norm q with
  | mk f' b' =>
    cases f' with
    | nil =>
      simp only [fQueue.toList]
      have norm_eq : fQueue.norm q = ⟨[], b'⟩ := h
      cases q with
      | mk qf qb =>
        cases qf with
        | nil =>
          simp [fQueue.norm] at h
          cases qb with
          | nil => simp
          | cons _ _ => simp at h
        | cons _ _ =>
          simp [fQueue.norm] at h
    | cons x xs =>
      simp only [fQueue.toList]
      have norm_eq : fQueue.toList (fQueue.norm q) = fQueue.toList q := norm_toList q
      have norm_toList_eq : fQueue.toList (fQueue.norm q) = x :: (xs ++ b'.reverse) := by
        simp [fQueue.toList, h]
      rw [norm_eq] at norm_toList_eq
      exact norm_toList_eq


theorem dequeue?_eq_none_iff_toList_nil {α} (q : fQueue α) :
    fQueue.dequeue? q = none ↔ fQueue.toList q = [] := by
  constructor
  · intro h
    have spec := dequeue?_spec q
    simp [h] at spec
    exact spec
  · intro hnil
    unfold fQueue.dequeue?
    cases h : fQueue.norm q with
    | mk f' b' =>
      cases f' with
      | nil => simp
      | cons x xs =>
        have : fQueue.toList (fQueue.norm q) ≠ [] := by
          simp [fQueue.toList, h]
        have eq_toList := norm_toList q
        rw [eq_toList] at this
        contradiction

/-- if `toList q = x :: xs`，then `dequeue? q = some (x, q')` and `toList q' = xs`。 -/
theorem dequeue?_cons_view {α : Type} {q : fQueue α} {x : α} {xs : List α}
    (h : fQueue.toList q = x :: xs) :
    ∃ q', fQueue.dequeue? q = some (x, q') ∧ fQueue.toList q' = xs := by
  cases h' : fQueue.dequeue? q with
  | none =>
    have spec := dequeue?_spec q
    simp [h'] at spec
    rw [h] at spec
    simp at spec
  | some p =>
    rcases p with ⟨y, q'⟩
    have spec := dequeue?_spec q
    simp [h'] at spec
    rw [h] at spec
    injection spec with xy_eq xs_eq
    simp [xy_eq.symm, xs_eq]


theorem fQueue_dequeue_mem {α : Type} [Inhabited α]
    (sq : fQueue α) (st : α) (sq' : fQueue α)
    (h_dequeue : fQueue.dequeue? sq = some (st, sq'))
    : st ∈ fQueue.toList sq := by
  unfold fQueue.dequeue? at h_dequeue
  cases h_norm : fQueue.norm sq with
  | mk f' b' =>
    simp only [h_norm] at h_dequeue
    cases f' with
    | nil =>
      simp only at h_dequeue
      contradiction
    | cons x xs =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h_dequeue
      obtain ⟨h_st_eq, _⟩ := h_dequeue
      rw [← h_st_eq]
      unfold fQueue.toList
      unfold fQueue.norm at h_norm
      cases sq with
      | mk front back =>
        cases front with
        | nil =>
          simp only [fQueue.mk.injEq] at h_norm
          obtain ⟨h_back_eq, _⟩ := h_norm
          have x_mem_back_rev : x ∈ back.reverse := by
            rw [h_back_eq]
            simp
          simp [x_mem_back_rev]
        | cons y ys =>
          simp only [fQueue.mk.injEq] at h_norm
          obtain ⟨h_front_eq, _⟩ := h_norm
          have x_eq_y : x = y := by
            injection h_front_eq with h_eq _
            exact h_eq.symm
          rw [x_eq_y]
          simp [List.mem_append]
