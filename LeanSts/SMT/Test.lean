import LeanSts.SMT.Main

set_option trace.smt true
set_option trace.smt.solve true
set_option trace.smt.reconstruct.proof true

set_option trace.sauto true
set_option sauto.smt.solver "z3"

theorem model1 {a : Type} (rel : a → a → Prop) (f : a → Int) (s1 s2 : a) :
  rel s1 s2 → rel s2 s1 ∨ f s1 = f s2 := by
  sauto

-- TRY:
-- (check-sat-using (then macro-finder smt))
