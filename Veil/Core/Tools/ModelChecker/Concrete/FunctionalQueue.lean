import Std.Data.HashSet

namespace Veil

/-- Functional Queue, from https://vfoley.xyz/functional-queues. -/
structure fQueue (α : Type) where
  front : Array α
  back : Array α
deriving Inhabited, Repr

namespace fQueue

instance : Membership α (fQueue α) where
  mem q x := x ∈ q.front.toList ∨ x ∈ q.back.toList

def empty {α} : fQueue α := ⟨#[], #[]⟩

@[grind]
def norm {α} (q : fQueue α) : fQueue α :=
  if q.front.isEmpty then ⟨q.back, #[]⟩ else q

@[grind]
def enqueue {α} (q : fQueue α) (x : α) : fQueue α :=
  ⟨q.front, q.back.push x⟩ -- O(1)

@[grind]
def dequeue? {α} (q : fQueue α) : Option (α × fQueue α) :=
  let nq := norm q
  if h : nq.front.size > 0 then
    some (nq.front[0], ⟨nq.front.extract 1 nq.front.size, nq.back⟩)
  else
    none

@[grind]
def toList {α} (q : fQueue α) : List α :=
  q.front.toList ++ q.back.toList

@[grind]
def isEmpty {α} (q : fQueue α) : Bool :=
  q.front.isEmpty && q.back.isEmpty

@[grind]
def size {α} (q : fQueue α) : Nat :=
  q.front.size + q.back.size  -- O(1)

@[grind]
def toArray {α} (q : fQueue α) : Array α :=
  q.front ++ q.back

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
  simp only [norm, toList]
  split <;> simp_all [Array.isEmpty_iff]

@[simp, grind =]
theorem norm_idem {α} (q : fQueue α) :
    fQueue.norm (fQueue.norm q) = fQueue.norm q := by
  simp only [norm]
  split <;> simp_all [Array.isEmpty_iff]

theorem norm_eq_self_of_front_not_empty {α} {q : fQueue α} (h : ¬q.front.isEmpty) :
    fQueue.norm q = q := by simp [norm, h]

@[simp, grind =]
theorem toList_empty {α : Type} : fQueue.toList (fQueue.empty : fQueue α) = ([] : List α) := rfl

@[simp, grind =]
theorem dequeue?_empty {α : Type} : fQueue.dequeue? (fQueue.empty : fQueue α) = none := rfl

@[simp, grind =]
theorem toList_enqueue {α : Type} (q : fQueue α) (x : α) :
    fQueue.toList (fQueue.enqueue q x) = fQueue.toList q ++ [x] := by
  simp [toList, enqueue]

@[grind .]
theorem front_implies_in_queue {α : Type} {q : fQueue α} {x : α}
    (h_front : x ∈ q.front.toList) : x ∈ fQueue.toList q :=
  List.mem_append.mpr (Or.inl h_front)

@[grind .]
theorem back_implies_in_queue {α : Type} {q : fQueue α} {x : α}
    (h_back : x ∈ q.back.toList) : x ∈ fQueue.toList q :=
  List.mem_append.mpr (Or.inr h_back)


private theorem array_toList_eq_head_cons_extract {α : Type} (arr : Array α) (h : arr.size > 0) :
    arr.toList = arr[0] :: (arr.extract 1 arr.size).toList := by
  have hlen : arr.toList.length > 0 := by simp [h]
  obtain ⟨x, xs, harr⟩ := List.exists_cons_of_length_pos hlen
  simp only [Array.toList_extract, harr]
  congr 1
  · have heq : arr.toList[0]'hlen = arr[0] := by simp only [Array.getElem_toList]
    simp only [harr, List.getElem_cons_zero] at heq; exact heq
  · have hxslen : xs.length = arr.size - 1 := by
      have := congrArg List.length harr; simp at this; omega
    simp only [List.extract, harr, List.drop_one, List.tail_cons]
    rw [List.take_of_length_le]; omega

@[simp, grind! .]
theorem dequeue?_spec {α : Type} (q : fQueue α) :
    match fQueue.dequeue? q with
    | none => fQueue.toList q = []
    | some (x, q') => fQueue.toList q = x :: fQueue.toList q' := by
  unfold dequeue?
  simp only [norm]
  by_cases hf : q.front.isEmpty = true
  · -- front is empty
    simp only [hf, ↓reduceIte]
    simp only [Array.isEmpty_iff] at hf
    by_cases hb : q.back.size > 0
    · -- back is non-empty
      simp only [hb, ↓reduceDIte, toList, Array.toList_empty, hf, List.nil_append, List.append_nil]
      rw [array_toList_eq_head_cons_extract q.back hb]
    · -- back is also empty
      simp only [Nat.not_lt, Nat.le_zero_eq, Array.size_eq_zero_iff] at hb
      simp only [hb, Array.size_empty, gt_iff_lt, Nat.not_lt_zero, ↓reduceDIte, toList,
        hf, List.nil_append, Array.toList_empty]
  · -- front is not empty
    simp only [hf, Bool.false_eq_true, ↓reduceIte]
    have hsize : q.front.size > 0 := by
      simp only [Array.isEmpty_iff, ← Array.size_eq_zero_iff] at hf
      omega
    simp only [hsize, ↓reduceDIte, toList]
    rw [array_toList_eq_head_cons_extract q.front hsize]
    simp only [List.cons_append]


@[simp, grind =]
theorem dequeue?_eq_none_iff_toList_nil {α} (q : fQueue α) :
    fQueue.dequeue? q = none ↔ fQueue.toList q = [] := by
  constructor
  · intro h; have := dequeue?_spec q; simp_all
  · intro hnil
    simp only [dequeue?, norm, toList, List.append_eq_nil_iff] at hnil ⊢
    split <;> simp_all

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
    (h_dequeue : fQueue.dequeue? sq = some (st, sq')) : st ∈ fQueue.toList sq := by
  have := dequeue?_spec sq; simp_all

@[simp, grind =]
theorem foldl_enqueue_toList {α : Type} (L : List α) (q : fQueue α) :
    (L.foldl fQueue.enqueue q).toList = q.toList ++ L := by
  induction L generalizing q with
  | nil => simp
  | cons x xs ih => simp [ih, toList_enqueue]


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
