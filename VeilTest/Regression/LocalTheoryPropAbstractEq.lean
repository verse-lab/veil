import Veil

set_option linter.unusedVariables false

veil module LocalTheoryPropAbstractEq

type node
immutable relation leader : node → Bool
immutable relation edge : node → node → Bool
immutable individual x : node

#gen_state

theory ghost relation theoryPlain (n : node) := leader n
theory ghost relation theoryNested := theoryPlain x
theory ghost relation theoryTwice := theoryNested ∧ theoryPlain x

assumption [assumePlain] theoryPlain x
assumption [assumeNested] theoryTwice ∧ theoryNested
assumption [assumeDecidable] if edge x x then theoryTwice else theoryNested

/--
info: LocalTheoryPropAbstractEq.theoryPlain.local_abstract_eq {ρ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] [ρ_sub : IsSubReaderOf (Theory node) ρ] (n : node)
  (th : ρ := by veil_exact_theory) : theoryPlain n th = theoryPlain n (readFrom th)
-/
#guard_msgs in
#check theoryPlain.local_abstract_eq

/--
info: LocalTheoryPropAbstractEq.theoryNested.local_abstract_eq {ρ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] [ρ_sub : IsSubReaderOf (Theory node) ρ] (th : ρ := by veil_exact_theory) :
  theoryNested th = theoryNested (readFrom th)
-/
#guard_msgs in
#check theoryNested.local_abstract_eq

/--
info: LocalTheoryPropAbstractEq.theoryTwice.local_abstract_eq {ρ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] [ρ_sub : IsSubReaderOf (Theory node) ρ] (th : ρ := by veil_exact_theory) :
  theoryTwice th = theoryTwice (readFrom th)
-/
#guard_msgs in
#check theoryTwice.local_abstract_eq

/--
info: LocalTheoryPropAbstractEq.assumePlain.local_abstract_eq {ρ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] [ρ_sub : IsSubReaderOf (Theory node) ρ] (th : ρ := by veil_exact_theory) :
  assumePlain th = assumePlain (readFrom th)
-/
#guard_msgs in
#check assumePlain.local_abstract_eq

/--
info: LocalTheoryPropAbstractEq.assumeNested.local_abstract_eq {ρ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] [ρ_sub : IsSubReaderOf (Theory node) ρ] (th : ρ := by veil_exact_theory) :
  assumeNested th = assumeNested (readFrom th)
-/
#guard_msgs in
#check assumeNested.local_abstract_eq

/--
info: LocalTheoryPropAbstractEq.assumeDecidable.local_abstract_eq {ρ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] [ρ_sub : IsSubReaderOf (Theory node) ρ] (th : ρ := by veil_exact_theory) :
  assumeDecidable th = assumeDecidable (readFrom th)
-/
#guard_msgs in
#check assumeDecidable.local_abstract_eq

after_init {
  pure ()
}

action keep {
  pure ()
}

invariant true

#gen_spec

/--
info: LocalTheoryPropAbstractEq.Assumptions.local_abstract_eq (ρ node : Type) [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] [ρ_sub : IsSubReaderOf (Theory node) ρ] (rd : ρ) :
  Assumptions ρ node rd = Assumptions (Theory node) node (readFrom rd)
-/
#guard_msgs in
#check Assumptions.local_abstract_eq

end LocalTheoryPropAbstractEq
