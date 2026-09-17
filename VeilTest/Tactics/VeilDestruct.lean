import Veil.Frontend.DSL.Tactic

structure Theory (α : Type) where
  a : α
  b : α


example (α : Type) (t : Theory α) (n : Nat) : 1 + n = n + 1 := by
  veil_destruct
  have _ := t.a
  have _ := t.b
  omega

example (α : Type) (t : Theory α) (n : Nat) : 1 + n = n + 1 := by
  veil_cases_type* Theory
  have _ := t.a
  have _ := t.b
  omega

example (α : Type) (t keep : Theory α) (n : Nat) : 1 + n = n + 1 := by
  veil_cases_type* Theory without [keep]
  have _ := t.a
  have _ := t.b
  have _ := keep
  have _ : Theory α := keep
  omega
