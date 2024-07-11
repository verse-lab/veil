import LeanSts.SMT.Main

-- set_option smt.solver.finitemodelfind true

set_option trace.sauto true
set_option sauto.smt.solver "cvc5"

theorem model1 {a : Type} (rel : a → a → Prop) (s1 s2 : a) :
  rel s1 s2 → ¬ ¬ rel s1 s2 := by
  sauto (timeout := 100)
