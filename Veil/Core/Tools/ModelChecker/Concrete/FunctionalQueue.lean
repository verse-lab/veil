import Std.Data.HashSet

namespace Veil

/-- Functional Queue, from https://vfoley.xyz/functional-queues. -/
structure fQueue (α : Type) where
  front : List α
  back : List α
  sz : Nat := 0
  h_sz : sz = front.length + back.length := by decide
deriving Repr

namespace fQueue

instance : Membership α (fQueue α) where
  mem q x := x ∈ q.front ∨ x ∈ q.back

def empty {α} : fQueue α := ⟨[], [], 0, rfl⟩

@[grind]
def norm {α} (q : fQueue α) : fQueue α :=
  match hf : q.front with
  | []    => ⟨q.back.reverse, [], q.sz, by simp [q.h_sz, hf, List.length_reverse]⟩
  | _::_  => q

@[simp]
theorem norm_sz {α} (q : fQueue α) : (norm q).sz = q.sz := by
  unfold norm
  split <;> rfl

@[grind]
def enqueue {α} (q : fQueue α) (x : α) : fQueue α :=
  ⟨q.front, x :: q.back, q.sz + 1, by simp [q.h_sz, List.length_cons]; omega⟩ -- O(1)

@[grind]
def dequeue? {α} (q : fQueue α) : Option (α × fQueue α) :=
  let nq := norm q
  match hf : nq.front with
  | []        => none
  | x :: xs   => some (x, ⟨xs, nq.back, q.sz - 1, by
      have h1 := nq.h_sz
      have h2 : nq.sz = q.sz := norm_sz q
      simp only [hf, List.length_cons] at h1
      omega⟩)

@[grind]
def toList {α} (q : fQueue α) : List α :=
  q.front ++ q.back.reverse

@[grind]
def isEmpty {α} (q : fQueue α) : Bool :=
  q.front.isEmpty && q.back.isEmpty

@[grind]
def size {α} (q : fQueue α) : Nat := q.sz

@[grind]
def toArray {α} (q : fQueue α) : Array α :=
  q.front.toArray ++ q.back.toArray.reverse

@[grind]
def ofList {α} (xs : List α) : fQueue α :=
  xs.foldl fQueue.enqueue fQueue.empty

-- ## Functional correctness of the functional queue

@[simp, grind =]
theorem norm_toList {α} (q : fQueue α) :
    fQueue.toList (fQueue.norm q) = fQueue.toList q := by
  cases q with | mk f b _ => cases f <;> simp [norm, toList]

@[simp, grind =]
theorem norm_idem {α} (q : fQueue α) :
    fQueue.norm (fQueue.norm q) = fQueue.norm q := by grind

theorem norm_eq_self_of_front_ne_nil {α} {q : fQueue α} (h : q.front ≠ []) :
    fQueue.norm q = q := by grind

@[simp, grind =]
theorem toList_empty {α : Type} : fQueue.toList (fQueue.empty : fQueue α) = ([] : List α) := by
  simp [fQueue.empty, fQueue.toList]

@[simp, grind =]
theorem dequeue?_empty {α : Type} : fQueue.dequeue? (fQueue.empty : fQueue α) = none := by
  simp [fQueue.empty, fQueue.dequeue?, fQueue.norm]


@[simp, grind =]
theorem toList_enqueue {α : Type} (q : fQueue α) (x : α) :
    fQueue.toList (fQueue.enqueue q x) = fQueue.toList q ++ [x] := by
  simp only [toList, enqueue, List.reverse_cons, List.append_assoc]


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
    | some (x, q') => fQueue.toList q = x :: fQueue.toList q' := by grind

@[simp, grind =]
theorem dequeue?_eq_none_iff_toList_nil {α} (q : fQueue α) :
    fQueue.dequeue? q = none ↔ fQueue.toList q = [] := by grind

/-- if `toList q = x :: xs`，then `dequeue? q = some (x, q')` and `toList q' = xs`。 -/
theorem dequeue?_cons_view {α : Type} {q : fQueue α} {x : α} {xs : List α}
    (h : fQueue.toList q = x :: xs) :
    ∃ q', fQueue.dequeue? q = some (x, q') ∧ fQueue.toList q' = xs := by grind


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


/-- If dequeue? returns some, the element is in the original queue -/
@[grind →]
theorem mem_of_mem_dequeue_tail {α : Type} (q q' : fQueue α) (x y : α)
    (h_dequeue : fQueue.dequeue? q = some (x, q'))
    (h_mem : y ∈ q') :
    y ∈ q := by
  have spec := dequeue?_spec q
  rw [h_dequeue] at spec
  -- spec: toList q = x :: toList q'
  unfold Membership.mem instMembership at h_mem ⊢
  cases h_mem with
  | inl h_front =>
    -- y ∈ q'.front
    -- Need to show: y ∈ q.front ∨ y ∈ q.back
    unfold toList at spec
    have : y ∈ q.front ++ q.back.reverse := by
      rw [spec]
      simp [h_front]
    simp [List.mem_append, List.mem_reverse] at this
    exact this
  | inr h_back =>
    -- y ∈ q'.back
    unfold toList at spec
    have : y ∈ q.front ++ q.back.reverse := by
      rw [spec]
      simp [List.mem_append, List.mem_reverse, h_back]
    simp [List.mem_append, List.mem_reverse] at this
    exact this



/-- An element is in the queue after enqueuing it -/
theorem mem_enqueue {α : Type} (q : fQueue α) (x : α) :
    x ∈ fQueue.toList (fQueue.enqueue q x) := by
  rw [toList_enqueue]
  simp

@[grind →]
theorem mem_of_dequeue {α : Type} (q q' : fQueue α) (x : α)
    (h_dequeue : fQueue.dequeue? q = some (x, q')) :
    x ∈ q := by
  have spec := dequeue?_spec q
  rw [h_dequeue] at spec
  unfold Membership.mem instMembership
  unfold toList at spec
  have h_mem : x ∈ q.front ++ q.back.reverse := by
    grind
  simp only at h_mem
  unfold Membership.mem
  grind

/-- isEmpty returns true iff both front and back are empty -/
@[grind =]
theorem isEmpty_iff_empty_lists {α : Type} (q : fQueue α) :
    q.isEmpty = true ↔ q.front = [] ∧ q.back = [] := by
  unfold isEmpty
  simp only [Bool.and_eq_true]
  grind

/-- If isEmpty is true, then dequeue? returns none -/
@[grind =]
theorem dequeue?_none_of_isEmpty {α : Type} (q : fQueue α)
    (h : q.isEmpty = true) :
    q.dequeue? = none := by
  have ⟨h_front, h_back⟩ := isEmpty_iff_empty_lists q |>.mp h
  unfold dequeue? norm
  grind



@[grind =]
theorem isEmpty_of_dequeue?_none {α : Type} (q : fQueue α) (h : q.dequeue? = none) :
    q.isEmpty = true := by
  have h_toList := dequeue?_eq_none_iff_toList_nil q |>.mp h
  unfold toList at h_toList
  have h_front : q.front = [] := by grind
  unfold fQueue.isEmpty
  rw [h_front]
  simp only [List.isEmpty_nil, Bool.true_and]
  have h_back_nil : q.back = [] := by
    rw [h_front] at h_toList
    simp only [List.nil_append] at h_toList
    simp at h_toList
    exact h_toList
  rw [h_back_nil]
  simp only [List.isEmpty_nil]



/-- Enqueue preserves the head element: if dequeue? returns some (head, tail),
    then after enqueuing a new element, dequeue? still returns the same head -/
theorem dequeue?_enqueue {α : Type} (q : fQueue α) (x : α) (head : α) (tail : fQueue α)
  (h_dequeue : q.dequeue? = some (head, tail))
  : ∃ tail', (q.enqueue x).dequeue? = some (head, tail') := by
  have h_spec := dequeue?_spec q
  rw [h_dequeue] at h_spec
  simp only at h_spec
  have h_enqueue_toList : (q.enqueue x).toList = q.toList ++ [x] := toList_enqueue q x
  rw [h_spec] at h_enqueue_toList
  simp only [List.cons_append] at h_enqueue_toList
  have ⟨tail', h_dequeue', h_toList'⟩ := dequeue?_cons_view h_enqueue_toList
  exact ⟨tail', h_dequeue'⟩


/-- Corollary: If a queue is non-empty, enqueue preserves the head element.
    More precisely, if q.dequeue? = some (head, tail), then
    (q.enqueue x).dequeue? = some (head, tail') for some tail' -/
theorem enqueue_preserves_head {α : Type} (q : fQueue α) (x : α) (head : α)
  (h_nonempty : ∃ tail, q.dequeue? = some (head, tail))
  : ∃ tail', (q.enqueue x).dequeue? = some (head, tail') := by
  obtain ⟨tail, h⟩ := h_nonempty
  exact dequeue?_enqueue q x head tail h


/-- If an element is in a list, it is in the queue constructed from that list -/
theorem mem_ofList {α : Type} (L : List α) (x : α) (h : x ∈ L)
  : x ∈ fQueue.ofList L := by
  unfold fQueue.ofList
  have h_toList : (List.foldl fQueue.enqueue fQueue.empty L).toList = fQueue.empty.toList ++ L :=
    fQueue.foldl_enqueue_toList L fQueue.empty
  rw [fQueue.toList_empty] at h_toList
  simp only [List.nil_append] at h_toList
  rw [← h_toList] at h
  unfold fQueue.toList at h
  unfold Membership.mem instMembership
  simp only [List.mem_append, List.mem_reverse] at h
  exact h

end fQueue


end Veil
