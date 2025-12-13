import Std.Data.HashSet

namespace Veil

/-- Functional Queue, from https://vfoley.xyz/functional-queues. -/
structure fQueue (α : Type) where
  front : List α
  back : List α
deriving Inhabited, Repr

namespace fQueue
def empty {α} : fQueue α := ⟨[], []⟩

@[grind]
def norm {α} (q : fQueue α) : fQueue α :=
  match q.front with
  | []    => ⟨q.back.reverse, []⟩
  | _::_  => q

@[grind]
def enqueue {α} (q : fQueue α) (x : α) : fQueue α :=
  ⟨q.front, x :: q.back⟩ -- O(1)

@[grind]
def dequeue? {α} (q : fQueue α) : Option (α × fQueue α) :=
  match (norm q).front with
  | []        => none
  | x :: xs   => some (x, ⟨xs, (norm q).back⟩)

@[grind]
def toList {α} (q : fQueue α) : List α :=
  q.front ++ q.back.reverse

@[grind]
def ofList {α} (xs : List α) : fQueue α :=
  xs.foldl fQueue.enqueue fQueue.empty

-- instance : EmptyCollection (fQueue α) where
--   emptyCollection := fQueue.empty

-- instance : Std.Stream (fQueue α) α where
--   next? q := q.dequeue?

-- instance : Functor fQueue where
--   map f q := ⟨q.front.map f, q.back.map f⟩

-- instance : Insert α (fQueue α) where
--   insert x xs:= enqueue xs x

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

@[simp, grind]
theorem norm_toList {α} (q : fQueue α) :
    fQueue.toList (fQueue.norm q) = fQueue.toList q := by
  cases q with
  | mk f b =>
    cases f with
    | nil => simp [fQueue.norm, fQueue.toList]
    | cons x xs => simp [fQueue.norm, fQueue.toList]

@[simp, grind]
theorem norm_idem {α} (q : fQueue α) :
    fQueue.norm (fQueue.norm q) = fQueue.norm q := by
  cases q with
  | mk f b =>
    cases f with
    | nil =>
      cases b with
      | nil => simp only [norm, List.reverse_nil]
      | cons y ys =>
        simp only [norm, List.reverse_cons, List.reverse_nil]
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

@[simp, grind =]
theorem toList_empty {α : Type} : fQueue.toList (fQueue.empty : fQueue α) = ([] : List α) := by
  simp [fQueue.empty, fQueue.toList]

@[simp, grind]
theorem dequeue?_empty {α : Type} : fQueue.dequeue? (fQueue.empty : fQueue α) = none := by
  simp [fQueue.empty, fQueue.dequeue?, fQueue.norm]


@[simp, grind]
theorem toList_enqueue {α : Type} (q : fQueue α) (x : α) :
    fQueue.toList (fQueue.enqueue q x) = fQueue.toList q ++ [x] := by
  simp [fQueue.toList, fQueue.enqueue, List.reverse_cons, List.append_assoc]


@[grind]
theorem front_imples_in_queue {α : Type} {q : fQueue α} {x : α}
    (h_front : x ∈ q.front) :
    x ∈ fQueue.toList q := by
  unfold fQueue.toList
  simp only [List.mem_append, List.mem_reverse]
  left
  exact h_front

@[grind]
theorem back_imples_in_queue {α : Type} {q : fQueue α} {x : α}
    (h_back : x ∈ q.back) :
    x ∈ fQueue.toList q := by
  unfold fQueue.toList
  simp only [List.mem_append, List.mem_reverse]
  right
  have h_back_rev : x ∈ q.back.reverse.reverse := by
    rw [List.reverse_reverse]
    exact h_back
  simp at h_back_rev
  exact h_back_rev


@[simp, grind]
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
          simp only [norm, mk.injEq, List.reverse_eq_nil_iff, List.nil_eq] at h
          cases qb with
          | nil => simp
          | cons _ _ => simp at h
        | cons _ _ =>
          simp [fQueue.norm] at h
    | cons x xs =>
      simp only [fQueue.toList]
      have norm_eq : fQueue.toList (fQueue.norm q) = fQueue.toList q := norm_toList q
      have norm_toList_eq : fQueue.toList (fQueue.norm q) = x :: (xs ++ b'.reverse) := by simp [fQueue.toList, h]
      rw [norm_eq] at norm_toList_eq
      exact norm_toList_eq


@[simp, grind =]
theorem dequeue?_eq_none_iff_toList_nil {α} (q : fQueue α) :
    fQueue.dequeue? q = none ↔ fQueue.toList q = [] := by
  constructor
  · intro h
    have spec := dequeue?_spec q
    simp only [h] at spec
    exact spec
  · intro hnil
    unfold fQueue.dequeue?
    cases h : fQueue.norm q with
    | mk f' b' =>
      cases f' with
      | nil => simp
      | cons x xs =>
        have : fQueue.toList (fQueue.norm q) ≠ [] := by simp [fQueue.toList, h]
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
    simp only [h'] at spec
    rw [h] at spec
    simp at spec
  | some p =>
    rcases p with ⟨y, q'⟩
    have spec := dequeue?_spec q
    simp only [h'] at spec
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
          grind
        | cons y ys =>
          simp only [fQueue.mk.injEq] at h_norm
          obtain ⟨h_front_eq, _⟩ := h_norm
          have x_eq_y : x = y := by grind
          rw [x_eq_y]
          simp [List.mem_append]


@[simp, grind =]
theorem foldl_enqueue_toList {α : Type} (L : List α) (q : fQueue α) :
    (L.foldl fQueue.enqueue q).toList = q.toList ++ L := by
  induction L generalizing q with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons]
    rw [ih (q.enqueue x)]
    grind


open Std
theorem mem_foldl_insert_aux
    {β : Type}
    [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β]
    (s : HashSet β) :
    ∀ {l : List β} {a : β},
      a ∈ List.foldl (fun acc x => acc.insert x) s l →
      a ∈ s ∨ a ∈ l
  | [], a, h => by
      simpa [List.foldl] using h
  | x :: xs, a, h => by
      have h' :
        a ∈ List.foldl (fun acc x => acc.insert x) (s.insert x) xs := by
        simpa [List.foldl] using h
      have ih' :
        a ∈ s.insert x ∨ a ∈ xs :=
        mem_foldl_insert_aux (s := s.insert x) (l := xs) (a := a) h'
      cases ih' with
      | inl h_in_s_insert =>
          -- `a ∈ s.insert x` ⇒ `a = x ∨ a ∈ s`
          have : a = x ∨ a ∈ s := by
            rw [Std.HashSet.mem_insert] at h_in_s_insert
            grind
          cases this with
          | inl h_eq =>
              right
              grind
          | inr h_in_s =>
              left
              exact h_in_s
      | inr h_in_xs =>
          right
          exact List.mem_cons_of_mem _ h_in_xs


theorem mem_foldl_insert_of_mem_aux [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β]
    (s : Std.HashSet β) :
    ∀ (l : List β) {a : β},
      (a ∈ s ∨ a ∈ l) →
      a ∈ List.foldl (fun acc x => acc.insert x) s l
  | [], a, h => by
      cases h with
      | inl hs =>
          simpa [List.foldl] using hs
      | inr hl =>
          cases hl
  | y :: ys, a, h => by
      have h' : a ∈ (s.insert y) ∨ a ∈ ys := by
        cases h with
        | inl hs =>
            left
            have : a = y ∨ a ∈ s := Or.inr hs
            grind
        | inr hl =>
            have : a = y ∨ a ∈ ys := by
              simpa [List.mem_cons] using hl
            cases this with
            | inl h_eq =>
                left
                have : a = y ∨ a ∈ s := Or.inl h_eq
                grind
            | inr h_in_ys =>
                right
                exact h_in_ys
      have h_res :
          a ∈ List.foldl (fun acc x => acc.insert x) (s.insert y) ys :=
        mem_foldl_insert_of_mem_aux (s := s.insert y) ys h'
      simpa [List.foldl] using h_res


theorem mem_foldl_insert_of_mem [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β]
    {l : List β} {a : β}
    (h : a ∈ l) :
    a ∈ List.foldl (fun acc x => acc.insert x)
          (Std.HashSet.emptyWithCapacity : Std.HashSet β) l := by
  have h' : a ∈ (Std.HashSet.emptyWithCapacity : Std.HashSet β) ∨ a ∈ l :=
    Or.inr h
  exact mem_foldl_insert_of_mem_aux
            (s := Std.HashSet.emptyWithCapacity) l h'


theorem mem_list_of_mem_foldl_insert {β : Type} [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β]
  {l : List β} {a : β}
  (h : a ∈ List.foldl (fun acc x => acc.insert x) Std.HashSet.emptyWithCapacity l)
  : a ∈ l := by
  have h' : a ∈ (HashSet.emptyWithCapacity : HashSet β) ∨ a ∈ l :=
    mem_foldl_insert_aux (s := HashSet.emptyWithCapacity) (l := l) (a := a) h
  cases h' with
  | inl h_in_empty => grind
  | inr h_in_l => exact h_in_l

end fQueue

end Veil
