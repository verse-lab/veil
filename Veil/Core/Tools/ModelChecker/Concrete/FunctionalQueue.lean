import Std.Data.HashSet

namespace Veil

/-- Functional Queue, from https://vfoley.xyz/functional-queues. -/
structure fQueue (α : Type) where
  front : List α
  back : List α
deriving Inhabited, Repr

namespace fQueue

instance : Membership α (fQueue α) where
  mem q x := x ∈ q.front ∨ x ∈ q.back

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
def isEmpty {α} (q : fQueue α) : Bool :=
  q.front.isEmpty && q.back.isEmpty

@[grind]
def size {α} (q : fQueue α) : Nat :=
  q.front.length + q.back.length

@[grind]
def toArray {α} (q : fQueue α) : Array α :=
  q.front.toArray ++ q.back.toArray.reverse

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

@[simp, grind =]
theorem norm_toList {α} (q : fQueue α) :
    fQueue.toList (fQueue.norm q) = fQueue.toList q := by
  cases q; rename_i f b; cases f <;> simp [norm, toList]

@[simp, grind =]
theorem norm_idem {α} (q : fQueue α) :
    fQueue.norm (fQueue.norm q) = fQueue.norm q := by
  cases q; rename_i f b; cases f <;> simp only [norm]
  cases b.reverse <;> simp

theorem norm_eq_self_of_front_ne_nil {α} {q : fQueue α} (h : q.front ≠ []) :
    fQueue.norm q = q := by
  cases q; rename_i f b; cases f with
  | nil => simp_all
  | cons => simp [norm]

@[simp, grind =]
theorem toList_empty {α : Type} : fQueue.toList (fQueue.empty : fQueue α) = ([] : List α) := by
  simp [fQueue.empty, fQueue.toList]

@[simp, grind =]
theorem dequeue?_empty {α : Type} : fQueue.dequeue? (fQueue.empty : fQueue α) = none := by
  simp [fQueue.empty, fQueue.dequeue?, fQueue.norm]


@[simp, grind =]
theorem toList_enqueue {α : Type} (q : fQueue α) (x : α) :
    fQueue.toList (fQueue.enqueue q x) = fQueue.toList q ++ [x] := by
  simp [fQueue.toList, fQueue.enqueue, List.reverse_cons, List.append_assoc]


@[grind .]
theorem front_imples_in_queue {α : Type} {q : fQueue α} {x : α}
    (h_front : x ∈ q.front) :
    x ∈ fQueue.toList q := by
  simp only [toList, List.mem_append, List.mem_reverse]; left; exact h_front

@[grind .]
theorem back_imples_in_queue {α : Type} {q : fQueue α} {x : α}
    (h_back : x ∈ q.back) :
    x ∈ fQueue.toList q := by
  simp only [toList, List.mem_append, List.mem_reverse]; right; exact h_back


@[simp, grind! .]
theorem dequeue?_spec {α : Type} (q : fQueue α) :
    match fQueue.dequeue? q with
    | none => fQueue.toList q = []
    | some (x, q') => fQueue.toList q = x :: fQueue.toList q' := by
  unfold dequeue?
  cases h : norm q with
  | mk f' b' =>
    cases f' with
    | nil =>
      cases q; rename_i qf qb; cases qf with
      | nil => simp only [norm, mk.injEq] at h; cases qb <;> simp_all [toList]
      | cons => simp [norm] at h
    | cons x xs =>
      have := norm_toList q
      simp only [toList] at this ⊢
      simp [h] at this; exact this.symm


@[simp, grind =]
theorem dequeue?_eq_none_iff_toList_nil {α} (q : fQueue α) :
    fQueue.dequeue? q = none ↔ fQueue.toList q = [] := by
  constructor
  · intro h; have := dequeue?_spec q; simp_all
  · intro hnil
    unfold dequeue?
    cases h : norm q; rename_i f' b'; cases f' with
    | nil => simp
    | cons => have := norm_toList q; simp_all [toList]

/-- if `toList q = x :: xs`，then `dequeue? q = some (x, q')` and `toList q' = xs`。 -/
theorem dequeue?_cons_view {α : Type} {q : fQueue α} {x : α} {xs : List α}
    (h : fQueue.toList q = x :: xs) :
    ∃ q', fQueue.dequeue? q = some (x, q') ∧ fQueue.toList q' = xs := by
  have spec := dequeue?_spec q
  cases h' : dequeue? q with
  | none => simp_all
  | some p => exact ⟨p.2, by simp_all⟩


theorem fQueue_dequeue_mem {α : Type} [Inhabited α]
    (sq : fQueue α) (st : α) (sq' : fQueue α)
    (h_dequeue : fQueue.dequeue? sq = some (st, sq'))
    : st ∈ fQueue.toList sq := by
  have spec := dequeue?_spec sq
  simp only [h_dequeue] at spec
  simp [spec]


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
  | [], _, h => by simpa using h
  | x :: xs, a, h => by
      simp only [List.foldl] at h
      have ih := mem_foldl_insert_aux (s.insert x) h
      simp only [HashSet.mem_insert, List.mem_cons] at ih ⊢
      grind


theorem mem_foldl_insert_of_mem_aux [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β]
    (s : Std.HashSet β) :
    ∀ (l : List β) {a : β},
      (a ∈ s ∨ a ∈ l) →
      a ∈ List.foldl (fun acc x => acc.insert x) s l
  | [], _, h => by grind
  | y :: ys, a, h => by
      simp only [List.foldl]
      apply mem_foldl_insert_of_mem_aux
      simp only [Std.HashSet.mem_insert, List.mem_cons] at h ⊢
      grind


theorem mem_foldl_insert_of_mem [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β]
    {l : List β} {a : β} (h : a ∈ l) :
    a ∈ List.foldl (fun acc x => acc.insert x)
          (Std.HashSet.emptyWithCapacity : Std.HashSet β) l :=
  mem_foldl_insert_of_mem_aux _ l (Or.inr h)


theorem mem_list_of_mem_foldl_insert {β : Type} [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β]
    {l : List β} {a : β}
    (h : a ∈ List.foldl (fun acc x => acc.insert x) Std.HashSet.emptyWithCapacity l) : a ∈ l := by
  have := mem_foldl_insert_aux HashSet.emptyWithCapacity h
  grind

end fQueue

end Veil
