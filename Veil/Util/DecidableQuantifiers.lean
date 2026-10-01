module

@[expose] public section

/-!
# Bounded quantifiers decided by specialized loops

The core `Decidable` instances for bounded quantifiers (`Nat.decidableForallFin`,
`Nat.decidableExistsFin`, `Nat.decidableBallLT`, ...) are compiled once, for an arbitrary
predicate: a call site passes the predicate's instance as a closure, which the loop then calls for
every candidate. The model checker decides such quantifiers in invariants and in action guards
for every state, so this costs a closure allocation per quantifier and an indirect call per
candidate.

The compiler does not specialize them away: it neither specializes instances nor inlines them
before specialization. The instances below are `@[macro_inline]` instead, which is expanded before
compilation proper (as core does for `Decidable (p ∧ q)`). The call site then sees the
`@[specialize]` loop `allLT.go` / `anyLT.go` applied to the predicate, and compiles the predicate
into its own copy of the loop. Their priority is `high` so that they take precedence over the core
instances; both visit the candidates from `0` upward and stop at the first one that decides the
result.

The loops do what core's `Nat.allLTTR` / `Nat.anyLTTR` do, but are exposed: `decide` (e.g. in the
`FinEncodable` deriving handler) must unfold them in other modules.
-/

namespace Veil

/-- `true` iff `f i h` holds for every `i < n`, checking `i = 0, 1, …` and stopping at the first
`false`. -/
@[inline] def allLT (n : Nat) (f : (i : Nat) → i < n → Bool) : Bool :=
  go 0 n (Nat.zero_add n)
where
  @[specialize] go (i : Nat) : (k : Nat) → i + k = n → Bool
    | 0, _ => true
    | k + 1, h => f i (by omega) && go (i + 1) k (by omega)

/-- `true` iff `f i h` holds for some `i < n`, checking `i = 0, 1, …` and stopping at the first
`true`. -/
@[inline] def anyLT (n : Nat) (f : (i : Nat) → i < n → Bool) : Bool :=
  go 0 n (Nat.zero_add n)
where
  @[specialize] go (i : Nat) : (k : Nat) → i + k = n → Bool
    | 0, _ => false
    | k + 1, h => f i (by omega) || go (i + 1) k (by omega)

private theorem allLT_go_eq_true {n : Nat} {f : (i : Nat) → i < n → Bool} :
    ∀ k i (h : i + k = n), allLT.go n f i k h = true ↔ ∀ j (hj : j < n), i ≤ j → f j hj = true := by
  intro k ; induction k <;> (intro i h; simp only [allLT.go]; grind)

theorem allLT_eq_true {n : Nat} {f : (i : Nat) → i < n → Bool} :
    allLT n f = true ↔ ∀ i (h : i < n), f i h = true := by
  simp only [allLT, allLT_go_eq_true, Nat.zero_le, forall_const]

private theorem anyLT_go_eq_true {n : Nat} {f : (i : Nat) → i < n → Bool} :
    ∀ k i (h : i + k = n), anyLT.go n f i k h = true ↔ ∃ j, ∃ hj : j < n, i ≤ j ∧ f j hj = true := by
  intro k ; induction k <;> (intro i h; simp only [anyLT.go]; grind)

theorem anyLT_eq_true {n : Nat} {f : (i : Nat) → i < n → Bool} :
    anyLT n f = true ↔ ∃ i, ∃ h : i < n, f i h = true := by
  simp only [anyLT, anyLT_go_eq_true, Nat.zero_le, true_and]

@[macro_inline] instance (priority := high) decidableForallFin {n : Nat} (P : Fin n → Prop)
    [DecidablePred P] : Decidable (∀ i, P i) :=
  decidable_of_iff (allLT n (fun i h => decide (P ⟨i, h⟩)) = true) <| by
    simp only [allLT_eq_true, decide_eq_true_eq]
    exact ⟨fun h i => h i.1 i.2, fun h i hi => h ⟨i, hi⟩⟩

@[macro_inline] instance (priority := high) decidableExistsFin {n : Nat} (P : Fin n → Prop)
    [DecidablePred P] : Decidable (∃ i, P i) :=
  decidable_of_iff (anyLT n (fun i h => decide (P ⟨i, h⟩)) = true) <| by
    simp only [anyLT_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨i, h, hp⟩ => ⟨⟨i, h⟩, hp⟩, fun ⟨i, hp⟩ => ⟨i.1, i.2, hp⟩⟩

@[macro_inline] instance (priority := high) decidableBallLT (n : Nat) (P : ∀ k, k < n → Prop)
    [∀ k h, Decidable (P k h)] : Decidable (∀ k h, P k h) :=
  decidable_of_iff (allLT n (fun k h => decide (P k h)) = true) <| by
    simp only [allLT_eq_true, decide_eq_true_eq]

@[macro_inline] instance (priority := high) decidableBallLE (n : Nat) (P : ∀ k, k ≤ n → Prop)
    [∀ k h, Decidable (P k h)] : Decidable (∀ k h, P k h) :=
  decidable_of_iff (allLT (n + 1) (fun k h => decide (P k (Nat.le_of_lt_succ h))) = true) <| by
    simp only [allLT_eq_true, decide_eq_true_eq]
    exact ⟨fun w k h => w k (Nat.lt_succ_of_le h), fun w k _ => w k _⟩

@[macro_inline] instance (priority := high) decidableExistsLT {p : Nat → Prop} [DecidablePred p]
    (n : Nat) : Decidable (∃ m, m < n ∧ p m) :=
  decidable_of_iff (anyLT n (fun m _ => decide (p m)) = true) <| by
    simp only [anyLT_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨m, h, hp⟩ => ⟨m, h, hp⟩, fun ⟨m, h, hp⟩ => ⟨m, h, hp⟩⟩

@[macro_inline] instance (priority := high) decidableExistsLE {p : Nat → Prop} [DecidablePred p]
    (n : Nat) : Decidable (∃ m, m ≤ n ∧ p m) :=
  decidable_of_iff (anyLT (n + 1) (fun m _ => decide (p m)) = true) <| by
    simp only [anyLT_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨m, h, hp⟩ => ⟨m, Nat.le_of_lt_succ h, hp⟩,
      fun ⟨m, h, hp⟩ => ⟨m, Nat.lt_succ_of_le h, hp⟩⟩

end Veil
