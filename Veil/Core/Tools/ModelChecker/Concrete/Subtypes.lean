import Veil.Frontend.DSL.State.Types

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


open Veil IteratedProd

def IteratedProd.ofListM {m : Type → Type} [Monad m]
  {α : Type} {β : α → Type} (f : (a : α) → m (β a))
  : (as : List α) → m (IteratedProd (as.map β))
  | []      => pure ()
  | a :: as => do
    let b ← f a
    let bs ← ofListM f as
    pure (b, bs)

/-- Version of `ofListM` that provides membership proof to the callback function.
    This is useful when the callback needs to prove properties about list elements.
    We use this function to inject _proof_ in concurrent search algorithm. -/
def IteratedProd.ofListMWithMem {m : Type → Type} [Monad m]
  {α : Type} {β : α → Type} (as : List α) (f : (a : α) → a ∈ as → m (β a))
  : m (IteratedProd (as.map β)) :=
  match as with
  | [] => pure ()
  | a :: as' => do
    let b ← f a List.mem_cons_self
    let bs ← ofListMWithMem as' (fun a' h => f a' (List.mem_cons_of_mem a h))
    pure (b, bs)


def IteratedProd.mapM [Monad m] {ts : List α} {T₁ T₂ : α → Type}
  (f : ∀ {a : α}, T₁ a → m (T₂ a))
  (elements : IteratedProd (ts.map T₁)) : m (IteratedProd (ts.map T₂)) := do
  match ts, elements with
  | [], _ => pure ()
  | _ :: _, (lis, elements) =>
    let head ← f lis
    let tail ← IteratedProd.mapM f elements
    pure (head, tail)

def IteratedProd.foldl {ts : List α} {T₁ : α → Type}
  (init : β)
  (prod : ∀ {a : α}, β → T₁ a → β)
  (elements : IteratedProd (ts.map T₁)) : β :=
  match ts, elements with
  | [], _ => init
  | _ :: _, (lis, elements) =>
    let res := prod init lis
    IteratedProd.foldl res prod elements


/-More complex, because we hope we can get the .property explicitly.
We hope to prove that after `foldl` or sth on different subtype element,
the result satisfy certain property.-/
theorem IteratedProd.foldl_add_init {ts : List α} {T : α → Type}
  (f : ∀ {a : α}, T a → Nat)
  (elements : IteratedProd (ts.map T))
  (init : Nat) :
  IteratedProd.foldl (init := init) (fun acc r => acc + f r) elements =
  init + IteratedProd.foldl (init := 0) (fun acc r => acc + f r) elements := by
  induction ts generalizing init with
  | nil =>
    cases elements
    simp [foldl]
  | cons head tail ih =>
    obtain ⟨h, t⟩ := elements
    simp [foldl]
    rw [ih t (init + f h)]
    rw [ih t (f h)]
    omega


-- Specialized version for subtypes with proofs about array sums
theorem IteratedProd.foldl_subtype_sum (worklist : Array Nat) (ranges : List (Nat × Nat))
  (elements : IteratedProd (ranges.map fun lr =>
    { x : Nat // x = (worklist.toSubarray lr.1 lr.2).toArray.sum })) :
  IteratedProd.foldl (init := 0) (fun acc r => acc + r.1) elements =
  (ranges.map fun lr => (worklist.toSubarray lr.1 lr.2).toArray.sum).sum := by
  induction ranges with
  | nil =>
    cases elements
    simp [foldl, List.sum]
  | cons head tail ih =>
    obtain ⟨h, t⟩ := elements
    simp only [List.map_cons, List.sum_cons, foldl]
    rw [foldl_add_init]
    rw [ih t]
    have : h.1 = (worklist.toSubarray head.1 head.2).toArray.sum := h.2
    rw [this]
    omega


-- Helper lemma: folding with a larger init gives a larger result
theorem IteratedProd.foldl_union_monotone [BEq σ] [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ]
  (trans : σ → List σₕ) (tail : List (List σ))
  (init1 init2 : Std.HashSet σₕ)
  (t : IteratedProd (tail.map fun r => { x : Std.HashSet σₕ // ∀s ∈ r, ∀s' ∈ trans s, s' ∈ x })) :
  (∀ x, x ∈ init1 → x ∈ init2) →
  (∀ x, x ∈ IteratedProd.foldl (init := init1) (fun acc r => acc.union r.val) t →
        x ∈ IteratedProd.foldl (init := init2) (fun acc r => acc.union r.val) t) := by
  intro h_sub x h_in
  induction tail generalizing init1 init2 with
  | nil =>
    cases t
    simp [IteratedProd.foldl] at h_in ⊢
    exact h_sub x h_in
  | cons head tail' ih_inner =>
    obtain ⟨h, t'⟩ := t
    simp only [IteratedProd.foldl] at h_in ⊢
    apply ih_inner (init1.union h.val) (init2.union h.val) t'
    · intro y hy
      rw [Std.HashSet.mem_union] at hy ⊢
      cases hy with
      | inl hy_init1 =>
        left
        exact h_sub y hy_init1
      | inr hy_h =>
        right
        exact hy_h
    · exact h_in

-- Helper lemma: if an element is in the init, it remains after folding with union
theorem IteratedProd.foldl_union_preserves_mem [BEq σ] [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ]
  (trans : σ → List σₕ) (tail : List (List σ)) (v : σₕ) (init : Std.HashSet σₕ)
  (t : IteratedProd (tail.map fun r => { x : Std.HashSet σₕ // ∀s ∈ r, ∀s' ∈ trans s, s' ∈ x })) :
  v ∈ init →
  v ∈ (IteratedProd.foldl (init := init) (fun acc r => acc.union r.val) t) := by
  intro h_in_init
  induction tail generalizing init with
  | nil =>
    cases t
    simp [IteratedProd.foldl]
    exact h_in_init
  | cons head tail' ih_inner =>
    obtain ⟨h, t'⟩ := t
    simp only [IteratedProd.foldl]
    apply ih_inner
    rw [Std.HashSet.mem_union]
    left
    exact h_in_init

theorem IteratedProd.foldl_subtype_mem {σ σₕ : Type} [BEq σ]
  [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ]
  (domain : List (List σ)) (trans : σ → List σₕ)
  (elements : IteratedProd (domain.map fun l =>
    { x : Std.HashSet σₕ // ∀s ∈ l, ∀s' ∈ trans s, s' ∈ x })) :
  ∀u, (u ∈ domain.flatMap id) → ∀v, v ∈ trans u →
    v ∈ (IteratedProd.foldl (init := (∅ : Std.HashSet σₕ)) (fun acc r => acc.union r.val) elements) := by
  intro u hu v hv
  induction domain with
  | nil =>
    simp [List.flatMap] at hu
  | cons head tail ih =>
    obtain ⟨h, t⟩ := elements
    rw [List.flatMap_cons, List.mem_append] at hu
    cases hu with
    | inl hu_head =>
      have hv_in_h : v ∈ h.val := h.property u hu_head v hv
      simp only [IteratedProd.foldl]
      have v_in_init : v ∈ (∅ : Std.HashSet σₕ).union h.val := by
        rw [Std.HashSet.mem_union]
        right
        exact hv_in_h
      exact IteratedProd.foldl_union_preserves_mem trans tail v ((∅ : Std.HashSet σₕ).union h.val) t v_in_init
    | inr hu_tail =>
      simp only [IteratedProd.foldl]
      have ih_result : v ∈ IteratedProd.foldl (init := (∅ : Std.HashSet σₕ)) (fun acc (r : { x : Std.HashSet σₕ // ∀s ∈ _, ∀s' ∈ trans s, s' ∈ x }) => acc.union r.val) t :=
        ih t hu_tail
      -- Use monotonicity to lift from init=∅ to init=∅.union h.val
      apply IteratedProd.foldl_union_monotone trans tail (∅ : Std.HashSet σₕ) ((∅ : Std.HashSet σₕ).union h.val) t
      · intro x hx
        rw [Std.HashSet.mem_union]
        left
        exact hx
      · exact ih_result
