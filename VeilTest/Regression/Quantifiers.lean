module

public import Veil.Frontend.DSL.Infra.Quantifiers

-- Several cases deliberately check that a simproc leaves the goal unchanged.
set_option linter.unusedSimpArgs false

-- The implication's domain contains a loose bvar until the Bool binder is opened.
-- NOTE: Use named theorems for match-containing types to avoid a Lean
-- language-server error about an unknown `_example.match_1` constant; see https://github.com/leanprover/lean4/issues/12985.
theorem forallDependentMatch (P : Bool → Prop)
    (h : ∀ b : Bool, (match b with | true => True | false => False) → P b) :
    ∀ b : Bool, (match b with | true => True | false => False) → P b := by
  simp -failIfUnchanged only [Veil.HO_forall_push_left]
  exact h

-- A higher-order binder depending on the preceding binder must not move left.
example (P : (n : Nat) → (Fin n → Bool) → Prop)
    (h : ∀ n f, P n f) : ∀ n f, P n f := by
  simp -failIfUnchanged only [Veil.HO_forall_push_left]
  guard_target = ∀ n f, P n f
  exact h

-- Structures are also classified as higher-order, including dependent ones.
example (P : (n : Nat) → Fin n → Prop)
    (h : ∀ n i, P n i) : ∀ n i, P n i := by
  simp -failIfUnchanged only [Veil.HO_forall_push_left]
  guard_target = ∀ n i, P n i
  exact h

-- Dependency inside another binder must also prevent reordering.
example (P : (n : Nat) → ((i : Fin n) → Fin i.val) → Prop)
    (h : ∀ n f, P n f) : ∀ n f, P n f := by
  simp -failIfUnchanged only [Veil.HO_forall_push_left]
  guard_target = ∀ n f, P n f
  exact h

-- Independent function and structure binders still move left.
example (P : Bool → (Nat → Bool) → Prop) :
    (∀ b f, P b f) = (∀ f b, P b f) := by
  simp only [Veil.HO_forall_push_left]

example (P : Bool → (Nat × Bool) → Prop) :
    (∀ b p, P b p) = (∀ p b, P b p) := by
  simp only [Veil.HO_forall_push_left]

-- Two higher-order binders must keep their order, avoiding a rewrite loop.
example (P : (Nat → Bool) → (Nat → Bool) → Prop)
    (h : ∀ f g, P f g) : ∀ f g, P f g := by
  simp -failIfUnchanged only [Veil.HO_forall_push_left]
  guard_target = ∀ f g, P f g
  exact h

-- The analogous existential simproc already opens binders and checks dependency.
example (P : (n : Nat) → (Fin n → Bool) → Prop)
    (h : ∃ n f, P n f) : ∃ n f, P n f := by
  simp -failIfUnchanged only [Veil.HO_exists_push_left]
  guard_target = ∃ n f, P n f
  exact h

example (P : Bool → (Nat → Bool) → Prop) :
    (∃ b f, P b f) = (∃ f b, P b f) := by
  simp only [Veil.HO_exists_push_left]

-- A later higher-order binder must enable guarded existential simplification.
example (P : Bool → (Nat → Bool) → Prop) :
    (∀ b f, ∃ _ : Nat, P b f) = (∀ b f, P b f) := by
  simp only [↓ Veil.existsQuantifierSimpGuarded]

open Lean Meta Elab Tactic in
example (P : Bool → Nat → (Nat → Bool) → Prop)
    (h : ∀ b n f, P b n f) : ∀ b n f, P b n f := by
  run_tac do
    unless (← Veil.hasHOQuantification (← getMainTarget)) do
      throwError "missed higher-order quantification inside a forall telescope"
  exact h

open Lean Meta Elab Tactic in
example (P : (n : Nat) → (Fin n → Bool) → Prop)
    (h : ∀ n f, P n f) : ∀ n f, P n f := by
  run_tac do
    unless (← Veil.hasHOQuantification (← getMainTarget)) do
      throwError "missed dependent higher-order quantification"
  exact h

open Lean Meta Elab Tactic in
theorem noHOQuantificationDependentMatch (P : Bool → Prop)
    (h : ∀ b : Bool, (match b with | true => True | false => False) → P b) :
    ∀ b : Bool, (match b with | true => True | false => False) → P b := by
  run_tac do
    if (← Veil.hasHOQuantification (← getMainTarget)) then
      throwError "unexpected higher-order quantification"
  simp -failIfUnchanged only [↓ Veil.existsQuantifierSimpGuarded]
  exact h
