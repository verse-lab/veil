import Veil.Frontend.DSL.Tactic

structure Theory (α : Type) where
  a : α
  b : α

set_option linter.unusedTactic false

example (α : Type) (t : Theory α) (n : Nat) : 1 + n = n + 1 := by
  veil_destruct
  #check t.a
  #check t.b
  ac_rfl

example (α : Type) (t : Theory α) (n : Nat) : 1 + n = n + 1 := by
  veil_cases_type* Theory
  #check t.a
  #check t.b
  ac_rfl
