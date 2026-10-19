import Veil.Frontend.DSL.Infra.Quantifiers

/-!
Proof checks for the normalization designs investigated in issue #123.

Run with `lake env lean Benchmarks/SMTTranslation/HoistingEquivalences.lean`.
These examples exercise the dependency and nonemptiness conditions that a
replacement for existential-quantifier hoisting must preserve.
-/

namespace Issue123

-- An ordinary outer state record makes the HO guard run, despite there being
-- no quantifier inside the proposition that requires lifting.
open Lean Meta Elab Tactic in
example : ∀ st : Nat × Nat, st.1 = st.1 := by
  run_tac do
    unless (← Veil.hasHOQuantification (← getMainTarget)) do
      throwError "expected the outer state record to trigger the guard"
  intro st
  run_tac do
    if (← Veil.hasHOQuantification (← getMainTarget)) then
      throwError "the guard should stop triggering after introducing the state"
  rfl

-- The trace-wide conjunction never requires combining all witness scopes.
theorem independent_steps {α β : Type} (P : α → Prop) (Q : β → Prop) :
    ((∃ x, P x) ∧ (∃ y, Q y)) ↔ ∃ x y, P x ∧ Q y := by
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨x, y, hx, hy⟩
  · rintro ⟨x, y, hx, hy⟩
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩

-- Local hypothesis extraction works even for potentially empty types.
theorem local_step_refutation {α β : Type} (P : α → Prop) (Q : β → Prop)
    (refute : ∀ x y, P x → Q y → False) :
    ¬ ((∃ x, P x) ∧ (∃ y, Q y)) := by
  rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  exact refute x y hx hy

-- Alternative action branches can reuse one witness when their types match.
-- This needs no Nonempty instance, unlike separate witnesses for each branch.
theorem share_alternative_witness {α : Type} (P Q : α → Prop) :
    ((∃ x, P x) ∨ (∃ x, Q x)) ↔ ∃ x, P x ∨ Q x := by
  constructor
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · exact ⟨x, Or.inl hx⟩
    · exact ⟨x, Or.inr hx⟩
  · rintro ⟨x, hx | hx⟩
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr ⟨x, hx⟩

-- Hoisting an unselected branch's witness is invalid for empty function types.
theorem inactive_branch_needs_nonempty :
    ¬ ((True ∨ (∃ _f : Unit → Empty, True)) ↔
      (∃ _f : Unit → Empty, True ∨ True)) := by
  intro h
  obtain ⟨f, _⟩ := h.mp (Or.inl True.intro)
  exact Empty.elim (f ())

-- Hoisting through a forall is invalid, even when witness type is inhabited.
theorem may_not_cross_universal :
    (∀ n : Bool, ∃ f : Unit → Bool, f () = n) ∧
    ¬ (∃ f : Unit → Bool, ∀ n : Bool, f () = n) := by
  constructor
  · intro n
    exact ⟨fun _ => n, rfl⟩
  · rintro ⟨f, hf⟩
    have impossible : false = true := (hf false).symm.trans (hf true)
    cases impossible

end Issue123
