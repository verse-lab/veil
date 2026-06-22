import Veil

set_option linter.unusedVariables false

veil module LocalRPropAbstractEq

type node
relation r : node → node → Bool
individual x : node

#gen_state

ghost relation ghostPlain (n : node) := r n x
ghost relation ghostNested := ghostPlain x
ghost relation ghostTwice := ghostNested ∧ ghostPlain x
ghost relation ghostThrice := ghostTwice ∧ ghostNested

invariant [usesGhost] ghostPlain x ∧ ghostNested
safety [safeGhost] ghostNested → ghostPlain x
invariant [usesGhostDeep] ghostThrice ∧ ghostTwice
safety [safeGhostDeep] ghostThrice → ghostTwice

/--
info: LocalRPropAbstractEq.ghostPlain.local_abstract_eq {ρ σ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] {χ : State.Label → Type}
  [χ_rep :
    (__veil_f : State.Label) →
      FieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)]
  [χ_rep_lawful :
    ∀ (__veil_f : State.Label),
      LawfulFieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)
        (χ_rep __veil_f)]
  [σ_sub : IsSubStateOf (State χ) σ] [ρ_sub : IsSubReaderOf (Theory node) ρ] (n : node) (th : ρ := by veil_exact_theory)
  (st : σ := by veil_exact_state) :
  (veil_term% ghostPlain) n th st =
    (veil_term% ghostPlain) n (readFrom th)
      (State.casesOn (getFrom st) fun r_conc x_conc =>
        let r := FieldRepresentation.get r_conc;
        let x := FieldRepresentation.get x_conc;
        { r := r, x := x })
-/
#guard_msgs in
#check ghostPlain.local_abstract_eq

/--
info: LocalRPropAbstractEq.ghostNested.local_abstract_eq {ρ σ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] {χ : State.Label → Type}
  [χ_rep :
    (__veil_f : State.Label) →
      FieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)]
  [χ_rep_lawful :
    ∀ (__veil_f : State.Label),
      LawfulFieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)
        (χ_rep __veil_f)]
  [σ_sub : IsSubStateOf (State χ) σ] [ρ_sub : IsSubReaderOf (Theory node) ρ] (th : ρ := by veil_exact_theory)
  (st : σ := by veil_exact_state) :
  (veil_term% ghostNested) th st =
    (veil_term% ghostNested) (readFrom th)
      (State.casesOn (getFrom st) fun r_conc x_conc =>
        let r := FieldRepresentation.get r_conc;
        let x := FieldRepresentation.get x_conc;
        { r := r, x := x })
-/
#guard_msgs in
#check ghostNested.local_abstract_eq

/--
info: LocalRPropAbstractEq.usesGhost.local_abstract_eq {ρ σ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] {χ : State.Label → Type}
  [χ_rep :
    (__veil_f : State.Label) →
      FieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)]
  [χ_rep_lawful :
    ∀ (__veil_f : State.Label),
      LawfulFieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)
        (χ_rep __veil_f)]
  [σ_sub : IsSubStateOf (State χ) σ] [ρ_sub : IsSubReaderOf (Theory node) ρ] (th : ρ := by veil_exact_theory)
  (st : σ := by veil_exact_state) :
  (veil_term% usesGhost) th st =
    (veil_term% usesGhost) (readFrom th)
      (State.casesOn (getFrom st) fun r_conc x_conc =>
        let r := FieldRepresentation.get r_conc;
        let x := FieldRepresentation.get x_conc;
        { r := r, x := x })
-/
#guard_msgs in
#check usesGhost.local_abstract_eq

/--
info: LocalRPropAbstractEq.safeGhost.local_abstract_eq {ρ σ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] {χ : State.Label → Type}
  [χ_rep :
    (__veil_f : State.Label) →
      FieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)]
  [χ_rep_lawful :
    ∀ (__veil_f : State.Label),
      LawfulFieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)
        (χ_rep __veil_f)]
  [σ_sub : IsSubStateOf (State χ) σ] [ρ_sub : IsSubReaderOf (Theory node) ρ] (th : ρ := by veil_exact_theory)
  (st : σ := by veil_exact_state) :
  (veil_term% safeGhost) th st =
    (veil_term% safeGhost) (readFrom th)
      (State.casesOn (getFrom st) fun r_conc x_conc =>
        let r := FieldRepresentation.get r_conc;
        let x := FieldRepresentation.get x_conc;
        { r := r, x := x })
-/
#guard_msgs in
#check safeGhost.local_abstract_eq

/--
info: LocalRPropAbstractEq.ghostTwice.local_abstract_eq {ρ σ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] {χ : State.Label → Type}
  [χ_rep :
    (__veil_f : State.Label) →
      FieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)]
  [χ_rep_lawful :
    ∀ (__veil_f : State.Label),
      LawfulFieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)
        (χ_rep __veil_f)]
  [σ_sub : IsSubStateOf (State χ) σ] [ρ_sub : IsSubReaderOf (Theory node) ρ] (th : ρ := by veil_exact_theory)
  (st : σ := by veil_exact_state) :
  (veil_term% ghostTwice) th st =
    (veil_term% ghostTwice) (readFrom th)
      (State.casesOn (getFrom st) fun r_conc x_conc =>
        let r := FieldRepresentation.get r_conc;
        let x := FieldRepresentation.get x_conc;
        { r := r, x := x })
-/
#guard_msgs in
#check ghostTwice.local_abstract_eq

/--
info: LocalRPropAbstractEq.ghostThrice.local_abstract_eq {ρ σ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] {χ : State.Label → Type}
  [χ_rep :
    (__veil_f : State.Label) →
      FieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)]
  [χ_rep_lawful :
    ∀ (__veil_f : State.Label),
      LawfulFieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)
        (χ_rep __veil_f)]
  [σ_sub : IsSubStateOf (State χ) σ] [ρ_sub : IsSubReaderOf (Theory node) ρ] (th : ρ := by veil_exact_theory)
  (st : σ := by veil_exact_state) :
  (veil_term% ghostThrice) th st =
    (veil_term% ghostThrice) (readFrom th)
      (State.casesOn (getFrom st) fun r_conc x_conc =>
        let r := FieldRepresentation.get r_conc;
        let x := FieldRepresentation.get x_conc;
        { r := r, x := x })
-/
#guard_msgs in
#check ghostThrice.local_abstract_eq

/--
info: LocalRPropAbstractEq.usesGhostDeep.local_abstract_eq {ρ σ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] {χ : State.Label → Type}
  [χ_rep :
    (__veil_f : State.Label) →
      FieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)]
  [χ_rep_lawful :
    ∀ (__veil_f : State.Label),
      LawfulFieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)
        (χ_rep __veil_f)]
  [σ_sub : IsSubStateOf (State χ) σ] [ρ_sub : IsSubReaderOf (Theory node) ρ] (th : ρ := by veil_exact_theory)
  (st : σ := by veil_exact_state) :
  (veil_term% usesGhostDeep) th st =
    (veil_term% usesGhostDeep) (readFrom th)
      (State.casesOn (getFrom st) fun r_conc x_conc =>
        let r := FieldRepresentation.get r_conc;
        let x := FieldRepresentation.get x_conc;
        { r := r, x := x })
-/
#guard_msgs in
#check usesGhostDeep.local_abstract_eq

/--
info: LocalRPropAbstractEq.safeGhostDeep.local_abstract_eq {ρ σ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] {χ : State.Label → Type}
  [χ_rep :
    (__veil_f : State.Label) →
      FieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)]
  [χ_rep_lawful :
    ∀ (__veil_f : State.Label),
      LawfulFieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)
        (χ_rep __veil_f)]
  [σ_sub : IsSubStateOf (State χ) σ] [ρ_sub : IsSubReaderOf (Theory node) ρ] (th : ρ := by veil_exact_theory)
  (st : σ := by veil_exact_state) :
  (veil_term% safeGhostDeep) th st =
    (veil_term% safeGhostDeep) (readFrom th)
      (State.casesOn (getFrom st) fun r_conc x_conc =>
        let r := FieldRepresentation.get r_conc;
        let x := FieldRepresentation.get x_conc;
        { r := r, x := x })
-/
#guard_msgs in
#check safeGhostDeep.local_abstract_eq

end LocalRPropAbstractEq
