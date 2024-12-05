import Lean

/- ## Various miscellaneous declarations -/
/-- A `Decidable` binary relation. -/
abbrev DecidableBinaryRel {α β : Sort u} (r : α → β → Prop) :=
  (a : α) → (b : β) → Decidable (r a b)

/-- A `Decidable` ternary relation. -/
abbrev DecidableTernaryRel {α β γ : Sort u} (r : α → β → γ → Prop) :=
  (a : α) → (b : β) → (c : γ) → Decidable (r a b c)

/-- Simplifiers to prepare a goal for SMT. See `SMT/Preparation.lean` -/
register_simp_attr smtSimp
/-- We specifically identify lemmas for quantifier elimination, since we run
  these in a loop and `smtSimp` is too large/expensive a set to run in a loop.
  See `SMT/Preparation.lean` -/
register_simp_attr quantifierElim
