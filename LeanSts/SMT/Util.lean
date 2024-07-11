import LeanSts.SMT.Main

-- set_option smt.solver.finitemodelfind true

set_option trace.smt true
set_option trace.smt.solve true
set_option trace.smt.reconstruct.proof true

set_option trace.sauto true
set_option sauto.smt.solver "z3"

theorem model1 {a : Type} (rel : a → a → Prop) (s1 s2 : a) :
  rel s1 s2 → rel s2 s1 := by
  sauto (timeout := 1)
