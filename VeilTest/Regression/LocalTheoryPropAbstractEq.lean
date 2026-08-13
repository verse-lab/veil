import Veil

set_option linter.unusedVariables false

veil module LocalTheoryPropAbstractEq

type node
immutable relation leader : node → Bool
immutable relation edge : node → node → Bool
immutable individual x : node
relation touched : node → Bool

#gen_state

theory ghost relation theoryPlain (n : node) := leader n
theory ghost relation theoryNested := theoryPlain x
theory ghost relation theoryTwice := theoryNested ∧ theoryPlain x
theory ghost relation theoryDecidableForall := if (∀ m, edge x m) then theoryTwice else theoryNested

ghost relation stateUsesTheory := theoryDecidableForall ∧ touched x

assumption [assumePlain] theoryPlain x
assumption [assumeNested] theoryTwice ∧ theoryNested
assumption [assumeDecidable] if edge x x then theoryTwice else theoryNested
assumption [assumeDecidableForall] if (∀ m, edge x m) then theoryTwice else theoryNested

invariant [stateTheoryGhost] stateUsesTheory

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
info: LocalTheoryPropAbstractEq.theoryDecidableForall.local_abstract_eq {ρ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] [ρ_sub : IsSubReaderOf (Theory node) ρ]
  [(edge : node → node → Bool) → (x : node) → Decidable (∀ (m : node), edge x m = true)]
  (th : ρ := by veil_exact_theory) : theoryDecidableForall th = theoryDecidableForall (readFrom th)
-/
#guard_msgs in
#check theoryDecidableForall.local_abstract_eq

/--
info: LocalTheoryPropAbstractEq.stateUsesTheory.local_abstract_eq {ρ σ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] {χ : State.Label → Type}
  [χ_rep :
    (__veil_f : State.Label) →
      FieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)]
  [χ_rep_lawful :
    ∀ (__veil_f : State.Label),
      LawfulFieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)
        (χ_rep __veil_f)]
  [σ_sub : IsSubStateOf (State χ) σ] [ρ_sub : IsSubReaderOf (Theory node) ρ]
  [(edge : node → node → Bool) → (x : node) → Decidable (∀ (m : node), edge x m = true)]
  (th : ρ := by veil_exact_theory) (st : σ := by veil_exact_state) :
  stateUsesTheory th st =
    stateUsesTheory (readFrom th)
      (State.casesOn (getFrom st) fun touched_conc =>
        let touched := FieldRepresentation.get touched_conc;
        { touched := touched })
-/
#guard_msgs in
#check stateUsesTheory.local_abstract_eq

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

/--
info: LocalTheoryPropAbstractEq.assumeDecidableForall.local_abstract_eq {ρ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] [ρ_sub : IsSubReaderOf (Theory node) ρ]
  [(edge : node → node → Bool) → (x : node) → Decidable (∀ (m : node), edge x m = true)]
  (th : ρ := by veil_exact_theory) : assumeDecidableForall th = assumeDecidableForall (readFrom th)
-/
#guard_msgs in
#check assumeDecidableForall.local_abstract_eq

/--
info: LocalTheoryPropAbstractEq.stateTheoryGhost.local_abstract_eq {ρ σ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] {χ : State.Label → Type}
  [χ_rep :
    (__veil_f : State.Label) →
      FieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)]
  [χ_rep_lawful :
    ∀ (__veil_f : State.Label),
      LawfulFieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)
        (χ_rep __veil_f)]
  [σ_sub : IsSubStateOf (State χ) σ] [ρ_sub : IsSubReaderOf (Theory node) ρ]
  [(edge : node → node → Bool) → (x : node) → Decidable (∀ (m : node), edge x m = true)]
  (th : ρ := by veil_exact_theory) (st : σ := by veil_exact_state) :
  stateTheoryGhost th st =
    stateTheoryGhost (readFrom th)
      (State.casesOn (getFrom st) fun touched_conc =>
        let touched := FieldRepresentation.get touched_conc;
        { touched := touched })
-/
#guard_msgs in
#check stateTheoryGhost.local_abstract_eq

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
  [node_inhabited : Inhabited node] [ρ_sub : IsSubReaderOf (Theory node) ρ]
  [theoryDecidableForall_dec_0 : (edge : node → node → Bool) → (x : node) → Decidable (∀ (m : node), edge x m = true)]
  (rd : ρ) : Assumptions ρ node rd = Assumptions (Theory node) node (readFrom rd)
-/
#guard_msgs in
#check Assumptions.local_abstract_eq

end LocalTheoryPropAbstractEq
