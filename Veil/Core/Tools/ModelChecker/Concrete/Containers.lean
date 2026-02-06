import Std
import Mathlib.Tactic.DeriveFintype


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
  ⟨xs, [], xs.length, rfl⟩

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

/-- isEmpty returns true iff both front and back are empty -/
@[grind =]
theorem not_mem_iff_isEmpty {α : Type} (q : fQueue α) :
    q.isEmpty = true ↔ ∀ a : α, a ∉ q := by
  simp [isEmpty_iff_empty_lists, fQueue.instMembership, List.eq_nil_iff_forall_not_mem]
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
theorem mem_ofList {α : Type} (L : List α) (x : α) :
  x ∈ L ↔ x ∈ fQueue.ofList L := by
  unfold fQueue.ofList ; simp [fQueue.instMembership] at *

end fQueue



namespace Std.HashSet

@[grind ←]
theorem mem_of_mem_insert'' {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
  (s : Std.HashSet α) (x y : α) (h : x ∈ s) : x ∈ s.insert y := by
  simp
  apply Or.inr
  exact h

theorem mem_insert_self' {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
  (s : Std.HashSet α) (x : α) : x ∈ s.insert x := by
  cases s
  unfold Membership.mem HashSet.insert
  apply HashMap.mem_insertIfNew_self

@[grind ←]
theorem mem_union {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
  (s₁ s₂ : Std.HashSet α) (x : α) :
  x ∈ s₁.union s₂ ↔ x ∈ s₁ ∨ x ∈ s₂ := by
  apply Iff.intro
  · intro h_union
    -- Forward direction: x ∈ s₁ ∪ s₂ → x ∈ s₁ ∨ x ∈ s₂
    simp only [Membership.mem] at h_union ⊢
    have h_union_contains : (s₁.union s₂).contains x = (s₁.contains x || s₂.contains x) := by
      rw [Std.HashSet.union_eq, Std.HashSet.contains_union]
    have h_contains_eq : (s₁.union s₂).contains x = (s₁.union s₂).inner.inner.contains x := rfl
    rw [← h_contains_eq] at h_union
    rw [h_union_contains] at h_union
    simp only [Bool.or_eq_true] at h_union
    cases h_union with
    | inl h_s1 => left; simp only [Std.HashSet.contains] at h_s1; exact h_s1
    | inr h_s2 => right; simp only [Std.HashSet.contains] at h_s2; exact h_s2
  · intro h_cases
    -- Backward direction: x ∈ s₁ ∨ x ∈ s₂ → x ∈ s₁ ∪ s₂
    cases h_cases with
    | inl h_in_s1 => exact Std.HashSet.mem_union_of_left h_in_s1
    | inr h_in_s2 => exact Std.HashSet.mem_union_of_right h_in_s2

@[grind ←]
theorem mem_list_of_mem_insertMany {β : Type} [BEq β] [Hashable β] [LawfulBEq β]
    {l : List β} {a : β}
    (h : a ∈ Std.HashSet.insertMany Std.HashSet.emptyWithCapacity l) : a ∈ l := by
  rw [Std.HashSet.mem_insertMany_list] at h
  simp only [Std.HashSet.not_mem_emptyWithCapacity, false_or] at h
  grind

theorem mem_insertMany_of_mem_list [BEq β] [Hashable β] [LawfulBEq β]
    {l : List β} {a : β} (h : a ∈ l) :
    a ∈ Std.HashSet.insertMany (Std.HashSet.emptyWithCapacity : Std.HashSet β) l := by
  rw [Std.HashSet.mem_insertMany_list]
  simp only [Std.HashSet.not_mem_emptyWithCapacity, false_or]
  grind

end Std.HashSet


namespace Std.HashMap

/- If `m[k]? = some v` after `foldl insert` on a list, then either `m` originally had `k -> v`,
    or `(k, v)` was inserted from the list. -/
theorem getElem?_foldl_insert {α β σₕ : Type}
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (l : List α) (acc : Std.HashMap σₕ β) (k : σₕ) (v : β)
  (f_key : α → σₕ) (f_val : α → β)
  (h_lookup : (l.foldl (fun acc a => acc.insert (f_key a) (f_val a)) acc)[k]? = some v) :
  acc[k]? = some v ∨ (k, v) ∈ l.map (fun a => (f_key a, f_val a)) := by
  induction l generalizing acc with
  | nil =>
    simp at h_lookup
    left; exact h_lookup
  | cons head tail ih =>
    simp only [List.foldl] at h_lookup
    have h_tail := ih (acc.insert (f_key head) (f_val head)) h_lookup
    cases h_tail with
    | inl h_in_modified =>
      by_cases h_eq : k = f_key head
      · have h_get : (acc.insert (f_key head) (f_val head))[k]? = some (f_val head) := by rw [h_eq]; exact Std.HashMap.getElem?_insert_self
        rw [h_get] at h_in_modified
        cases h_in_modified
        right
        simp only [List.map_cons, List.mem_cons]
        left
        rw [h_eq]
      · have h_get : (acc.insert (f_key head) (f_val head))[k]? = acc[k]? := by
          rw [Std.HashMap.getElem?_insert];grind
        rw [h_get] at h_in_modified
        left; exact h_in_modified
    | inr h_in_tail =>
      right
      simp only [List.map_cons, List.mem_cons]
      right
      exact h_in_tail


/- Insert operation preserves existing keys: if a key has a value before insert, it still has some value after insert. -/
@[grind .]
theorem getElem?_isSome_of_insert {β σₕ : Type}
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (m : Std.HashMap σₕ β) (k k' : σₕ) (v' : β)
  (h : m[k]?.isSome) :
  (m.insert k' v')[k]?.isSome := by
  by_cases h_eq : k = k'
  · rw [h_eq, Std.HashMap.getElem?_insert_self]; simp
  · rw [Std.HashMap.getElem?_insert]; split
    · rename_i h_beq
      have : k' = k := LawfulBEq.eq_of_beq h_beq
      have : k = k' := this.symm
      contradiction
    · exact h

theorem isSome_preserved_by_foldl_insert {α β σₕ : Type}
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (l : List α) (acc : Std.HashMap σₕ β) (k : σₕ)
  (f_key : α → σₕ) (f_val : α → β)
  (h : acc[k]?.isSome) :
  (l.foldl (fun acc a => acc.insert (f_key a) (f_val a)) acc)[k]?.isSome := by
  induction l generalizing acc with
  | nil => simp;grind
  | cons head tail ih =>
    simp only [List.foldl]
    apply ih
    exact HashMap.getElem?_isSome_of_insert acc k (f_key head) (f_val head) h


/- If an element `a` is in the list, then after `foldl insert`, the key `f_key a` is in the resulting HashMap. -/
theorem mem_of_foldl_insert {α β σₕ : Type}
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (l : List α) (acc : Std.HashMap σₕ β) (a : α)
  (f_key : α → σₕ) (f_val : α → β)
  (h_mem : a ∈ l) :
  ∃ v, (l.foldl (fun acc a => acc.insert (f_key a) (f_val a)) acc)[f_key a]? = some v := by
  induction l generalizing acc with
  | nil => simp at h_mem
  | cons head tail ih =>
    simp only [List.mem_cons] at h_mem
    cases h_mem with
    | inl h_eq =>
      -- a = head
      rw [h_eq]; clear h_eq
      simp only [List.foldl]
      have h_inserted : (acc.insert (f_key head) (f_val head))[f_key head]? = some (f_val head) :=
        Std.HashMap.getElem?_insert_self
      have h_isSome : (acc.insert (f_key head) (f_val head))[f_key head]?.isSome := by
        rw [h_inserted]; simp
      have h_persists := HashMap.isSome_preserved_by_foldl_insert tail (acc.insert (f_key head) (f_val head)) (f_key head) f_key f_val h_isSome
      simp only [Option.isSome_iff_exists] at h_persists
      exact h_persists
    | inr h_in_tail =>
      simp only [List.foldl]
      exact ih (acc.insert (f_key head) (f_val head)) h_in_tail



theorem getElem?_insertIfNew_of_contains {σₕ β : Type}
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (m : Std.HashMap σₕ β) (k k' : σₕ) (v v' : β)
  (h_in : m[k]? = some v) :
  (m.insertIfNew k' v')[k]? = some v := by
  rw [Std.HashMap.getElem?_insertIfNew]
  split
  · next h_cond =>
    have ⟨h_eq, h_not_in⟩ := h_cond
    have h_k'_eq_k : k' = k := LawfulBEq.eq_of_beq h_eq
    subst h_k'_eq_k
    simp only [Std.HashMap.mem_iff_contains] at h_not_in
    grind
  · exact h_in


theorem getElem?_insertIfNew_of_not_contains_same_key {σₕ β : Type}
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (m : Std.HashMap σₕ β) (k : σₕ) (v : β)
  (h_not_in : k ∉ m) :
  (m.insertIfNew k v)[k]? = some v := by
  rw [Std.HashMap.getElem?_insertIfNew]
  split
  · next h_cond => rfl
  · next h_cond =>
    push_neg at h_cond
    have h_beq_refl : (k == k) = true := by simp
    have h := h_cond h_beq_refl
    simp only [Std.HashMap.mem_iff_contains] at h_not_in
    contradiction


theorem getElem?_insertIfNew_of_ne {σₕ β : Type}
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (m : Std.HashMap σₕ β) (k k' : σₕ) (v' : β)
  (h_ne : k ≠ k') :
  (m.insertIfNew k' v')[k]? = m[k]? := by
  rw [Std.HashMap.getElem?_insertIfNew]
  split
  · next h_cond =>
    have ⟨h_eq, _⟩ := h_cond
    have h_k'_eq_k : k' = k := LawfulBEq.eq_of_beq h_eq
    exact absurd h_k'_eq_k.symm h_ne
  · rfl


theorem getElem?_fold_insertIfNew_preserves_m2 {σₕ β : Type}
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (m1 m2 : Std.HashMap σₕ β) (k : σₕ) (v : β)
  (h_in_m2 : m2[k]? = some v) :
  (m1.fold (init := m2) fun acc k' v' => acc.insertIfNew k' v')[k]? = some v := by
  rw [Std.HashMap.fold_eq_foldl_toList]
  generalize h_l : m1.toList = l
  clear h_l
  induction l generalizing m2 with
  | nil =>
    simp only [List.foldl]
    exact h_in_m2
  | cons hd tl ih =>
    simp only [List.foldl]
    apply ih
    apply getElem?_insertIfNew_of_contains
    exact h_in_m2


theorem foldl_insertIfNew_preserves {σₕ β : Type}
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (l : List (σₕ × β)) (acc : Std.HashMap σₕ β) (k : σₕ) (v : β)
  (h_in_acc : acc[k]? = some v) :
  (l.foldl (fun acc (kv : σₕ × β) => acc.insertIfNew kv.1 kv.2) acc)[k]? = some v := by
  induction l generalizing acc with
  | nil => simp only [List.foldl]; exact h_in_acc
  | cons hd tl ih =>
    simp only [List.foldl]
    apply ih
    apply getElem?_insertIfNew_of_contains
    exact h_in_acc


theorem getElem?_fold_insertIfNew_from_m1 {σₕ β : Type}
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (m1 m2 : Std.HashMap σₕ β) (k : σₕ) (v : β)
  (h_in_m1 : m1[k]? = some v)
  (h_not_in_m2 : k ∉ m2) :
  (m1.fold (init := m2) fun acc k' v' => acc.insertIfNew k' v')[k]? = some v := by
  rw [Std.HashMap.fold_eq_foldl_toList] -- [cite: 266]
  have h_mem : (k, v) ∈ m1.toList := by
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] -- [cite: 252]
    exact h_in_m1
  have h_nodup : m1.toList.map Prod.fst |> List.Nodup := by
    rw [Std.HashMap.map_fst_toList_eq_keys] --
    exact Std.HashMap.nodup_keys --
  generalize h_l : m1.toList = l
  rw [h_l] at h_mem h_nodup
  clear h_l
  induction l generalizing m2 with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.foldl, List.mem_cons, List.map_cons, List.nodup_cons] at h_mem h_nodup ⊢
    obtain ⟨h_key_not_in_tail, h_tail_unique⟩ := h_nodup
    by_cases h_eq : hd.1 = k
    · have h_val : hd.2 = v := by
        cases h_mem with
        | inl h_head => grind
        | inr h_tail => grind
      subst h_eq
      subst h_val
      apply foldl_insertIfNew_preserves
      apply getElem?_insertIfNew_of_not_contains_same_key
      exact h_not_in_m2
    · apply ih
      · cases h_mem
        · rename_i h_head
          grind
        · grind
      · exact h_tail_unique
      · grind


/-- Helper: trace back the source of a lookup result from List.foldl insertIfNew.
    If we get a result, it came from either acc (preserved) or the list (inserted). -/
theorem List.foldl_insertIfNew_source {σₕ β : Type}
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (l : List (σₕ × β)) (acc : Std.HashMap σₕ β) (k : σₕ) (v : β)
  (h_lookup : (l.foldl (fun acc (kv : σₕ × β) => acc.insertIfNew kv.1 kv.2) acc)[k]? = some v) :
  acc[k]? = some v ∨ ((k, v) ∈ l ∧ k ∉ acc) := by
  induction l generalizing acc with
  | nil =>
    simp only [List.foldl] at h_lookup
    left; exact h_lookup
  | cons hd tl ih =>
    simp only [List.foldl] at h_lookup
    have h_step := ih (acc.insertIfNew hd.1 hd.2) h_lookup
    cases h_step with
    | inl h_in_step =>
      rw [Std.HashMap.getElem?_insertIfNew] at h_in_step
      split at h_in_step
      · next h_cond =>
          have ⟨h_beq, h_not_in⟩ := h_cond
          have h_hd1_eq_k : hd.1 = k := LawfulBEq.eq_of_beq h_beq
          right
          constructor
          · simp only [List.mem_cons]
            left; rw [← h_hd1_eq_k]
            cases h_in_step
            rfl
          · grind
      · left; exact h_in_step
    | inr h_from_tl =>
      have ⟨h_in_tl, h_not_in_step⟩ := h_from_tl
      right
      constructor
      · simp only [List.mem_cons]
        right; exact h_in_tl
      · simp only [Std.HashMap.mem_iff_contains] at h_not_in_step ⊢
        simp only [Std.HashMap.contains_insertIfNew] at h_not_in_step
        push_neg at h_not_in_step
        grind

/-- Trace back the source of a lookup result from HashMap.fold insertIfNew.
    If we get a result, it came from either m2 (preserved) or m1 (inserted when key not in m2). -/
theorem getElem?_fold_insertIfNew_source {σₕ β : Type}
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
  (m1 m2 : Std.HashMap σₕ β) (k : σₕ) (v : β)
  (h_lookup : (m1.fold (init := m2) fun acc k' v' => acc.insertIfNew k' v')[k]? = some v) :
  m2[k]? = some v ∨ (m1[k]? = some v ∧ k ∉ m2) := by
  rw [Std.HashMap.fold_eq_foldl_toList] at h_lookup
  have h_source := List.foldl_insertIfNew_source m1.toList m2 k v h_lookup
  cases h_source with
  | inl h_from_m2 => left; exact h_from_m2
  | inr h_from_list =>
    right
    have ⟨h_in_list, h_not_in_m2⟩ := h_from_list
    constructor
    · rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at h_in_list
      exact h_in_list
    · exact h_not_in_m2

/-- If a key-value pair is in a HashMap, it's in the toArray representation. -/
theorem mem_toArray_of_getElem? {α β : Type}
  [BEq α] [Hashable α] [LawfulBEq α]
  (m : Std.HashMap α β) (k : α) (v : β)
  (h : m[k]? = some v) :
  (k, v) ∈ m.toArray := by
  simp [Array.mem_def] at *
  grind

/-- If a key-value pair is in the toArray representation, it's in the HashMap. -/
theorem getElem?_of_mem_toArray {α β : Type}
  [BEq α] [Hashable α] [LawfulBEq α]
  (m : Std.HashMap α β) (k : α) (v : β)
  (h : (k, v) ∈ m.toArray) :
  m[k]? = some v := by
  simp [Array.mem_def] at *
  grind

end Std.HashMap


namespace Array

/-- Elements in Array.extract are from the original array. -/
theorem mem_of_mem_extract {α : Type} (arr : Array α) (i j : Nat) (x : α)
  (h : x ∈ arr.extract i j) : x ∈ arr := by
  rw [Array.mem_def] at h ⊢
  rw [Array.toList_extract] at h
  exact List.mem_of_mem_drop (List.mem_of_mem_take h)

theorem mem_flatten_of_partition {α : Type}
  (arr : Array α)
  (ranges : List (Nat × Nat))
  (x : α) (h_mem : x ∈ arr)
  (h_cover : ∀ i, i < arr.size → ∃ lr ∈ ranges, lr.1 ≤ i ∧ i < lr.2)
  (h_valid : ∀ lr ∈ ranges, lr.1 ≤ lr.2 ∧ lr.2 ≤ arr.size) :
  x ∈ (ranges.map fun lr => (arr.extract lr.1 lr.2)).toArray.flatten := by
  rcases Array.mem_iff_getElem.mp h_mem with ⟨i, h_i_lt, rfl⟩
  rcases h_cover i h_i_lt with ⟨lr, h_lr_in, h_l_le, h_i_lt_r⟩
  rw [Array.mem_flatten]
  let subArr := (arr.extract lr.1 lr.2)
  exists subArr
  constructor
  . rw [List.mem_toArray, List.mem_map]; exists lr
  . dsimp [subArr]
    rw [Array.mem_iff_getElem]
    have h_idx_valid : i - lr.1 < (arr.extract lr.1 lr.2).size := by
      rw [Array.size_extract]
      have h_le_size : lr.2 ≤ arr.size := (h_valid lr h_lr_in).2
      rw [Nat.min_eq_left h_le_size]
      apply Nat.sub_lt_sub_right h_l_le h_i_lt_r
    grind

/-- Similar to mem_flatten_of_partition but with a map applied to each element.
    If `x` is in `arr`, then `f x` is in the flatten of mapped extracted subarrays. -/
theorem mem_flatten_of_partition_map {α β : Type}
  (arr : Array α)
  (ranges : List (Nat × Nat))
  (x : α) (h_mem : x ∈ arr)
  (h_cover : ∀ i, i < arr.size → ∃ lr ∈ ranges, lr.1 ≤ i ∧ i < lr.2)
  (h_valid : ∀ lr ∈ ranges, lr.1 ≤ lr.2 ∧ lr.2 ≤ arr.size)
  (f : α → β) :
  f x ∈ (ranges.map fun lr => (arr.extract lr.1 lr.2).map f).toArray.flatten := by
  rcases Array.mem_iff_getElem.mp h_mem with ⟨i, h_i_lt, rfl⟩
  rcases h_cover i h_i_lt with ⟨lr, h_lr_in, h_l_le, h_i_lt_r⟩
  rw [Array.mem_flatten]
  let subArr := (arr.extract lr.1 lr.2).map f
  exists subArr
  constructor
  · rw [List.mem_toArray, List.mem_map]; exists lr
  · dsimp [subArr]
    rw [Array.mem_map]
    exists arr[i]
    constructor
    · rw [Array.mem_iff_getElem]
      have h_idx_valid : i - lr.1 < (arr.extract lr.1 lr.2).size := by
        rw [Array.size_extract]
        have h_le_size : lr.2 ≤ arr.size := (h_valid lr h_lr_in).2
        rw [Nat.min_eq_left h_le_size]
        apply Nat.sub_lt_sub_right h_l_le h_i_lt_r
      exists i - lr.1, h_idx_valid
      simp only [Array.getElem_extract]
      congr 1
      omega
    · rfl

end Array
