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
  (th : ρ := by veil_exact_theory) : (veil_term% theoryPlain) n th = (veil_term% theoryPlain) n (readFrom th)
-/
#guard_msgs in
#check theoryPlain.local_abstract_eq

/--
info: LocalTheoryPropAbstractEq.theoryNested.local_abstract_eq {ρ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] [ρ_sub : IsSubReaderOf (Theory node) ρ] (th : ρ := by veil_exact_theory) :
  (veil_term% theoryNested) th = (veil_term% theoryNested) (readFrom th)
-/
#guard_msgs in
#check theoryNested.local_abstract_eq

/--
info: LocalTheoryPropAbstractEq.theoryTwice.local_abstract_eq {ρ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] [ρ_sub : IsSubReaderOf (Theory node) ρ] (th : ρ := by veil_exact_theory) :
  (veil_term% theoryTwice) th = (veil_term% theoryTwice) (readFrom th)
-/
#guard_msgs in
#check theoryTwice.local_abstract_eq

/--
info: LocalTheoryPropAbstractEq.theoryDecidableForall.local_abstract_eq {ρ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] [ρ_sub : IsSubReaderOf (Theory node) ρ]
  [(edge : node → node → Bool) → (x : node) → Decidable (∀ (m : node), edge x m = true)]
  (th : ρ := by veil_exact_theory) :
  (veil_term% theoryDecidableForall) th = (veil_term% theoryDecidableForall) (readFrom th)
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
  (veil_term% stateUsesTheory) th st =
    (veil_term% stateUsesTheory) (readFrom th)
      (State.casesOn (getFrom st) fun touched_conc =>
        let touched := FieldRepresentation.get touched_conc;
        { touched := touched })
-/
#guard_msgs in
#check stateUsesTheory.local_abstract_eq

/--
info: LocalTheoryPropAbstractEq.assumePlain.local_abstract_eq {ρ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] [ρ_sub : IsSubReaderOf (Theory node) ρ] (th : ρ := by veil_exact_theory) :
  (veil_term% assumePlain) th = (veil_term% assumePlain) (readFrom th)
-/
#guard_msgs in
#check assumePlain.local_abstract_eq

/--
info: LocalTheoryPropAbstractEq.assumeNested.local_abstract_eq {ρ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] [ρ_sub : IsSubReaderOf (Theory node) ρ] (th : ρ := by veil_exact_theory) :
  (veil_term% assumeNested) th = (veil_term% assumeNested) (readFrom th)
-/
#guard_msgs in
#check assumeNested.local_abstract_eq

/--
info: LocalTheoryPropAbstractEq.assumeDecidable.local_abstract_eq {ρ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] [ρ_sub : IsSubReaderOf (Theory node) ρ] (th : ρ := by veil_exact_theory) :
  (veil_term% assumeDecidable) th = (veil_term% assumeDecidable) (readFrom th)
-/
#guard_msgs in
#check assumeDecidable.local_abstract_eq

/--
info: LocalTheoryPropAbstractEq.assumeDecidableForall.local_abstract_eq {ρ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] [ρ_sub : IsSubReaderOf (Theory node) ρ]
  [(edge : node → node → Bool) → (x : node) → Decidable (∀ (m : node), edge x m = true)]
  (th : ρ := by veil_exact_theory) :
  (veil_term% assumeDecidableForall) th = (veil_term% assumeDecidableForall) (readFrom th)
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
  (veil_term% stateTheoryGhost) th st =
    (veil_term% stateTheoryGhost) (readFrom th)
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
  [assumeDecidableForall_dec_0 : (edge : node → node → Bool) → (x : node) → Decidable (∀ (m : node), edge x m = true)]
  (rd : ρ) : veil_term% Assumptions = (veil_term% Assumptions) (readFrom rd)
-/
#guard_msgs in
#check Assumptions.local_abstract_eq

end LocalTheoryPropAbstractEq
