import Veil

set_option linter.unusedVariables false

veil module AssertionDecidableFieldRep

type node
relation r : node → node → Bool
individual x : node

#gen_state

-- Regression: extracted Decidable instances for assertions must line up with
-- the concrete field representation used by the elaborated assertion body.
invariant [decidableForallFieldRep] (if (∀ m, r x m) then x = x else x ≠ x)

/--
info: AssertionDecidableFieldRep.decidableForallFieldRep.local_abstract_eq {ρ σ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] {χ : State.Label → Type}
  [χ_rep :
    (__veil_f : State.Label) →
      FieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)]
  [χ_rep_lawful :
    ∀ (__veil_f : State.Label),
      LawfulFieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)
        (χ_rep __veil_f)]
  [σ_sub : IsSubStateOf (State χ) σ] [ρ_sub : IsSubReaderOf (Theory node) ρ]
  [(r_conc : χ State.Label.r) →
      (x_conc : χ State.Label.x) →
        Decidable (∀ (m : node), FieldRepresentation.get r_conc (id (FieldRepresentation.get x_conc)) m = true)]
  (th : ρ := by veil_exact_theory) (st : σ := by veil_exact_state) :
  (veil_term% decidableForallFieldRep) th st =
    (veil_term% decidableForallFieldRep) (readFrom th)
      (State.casesOn (getFrom st) fun r_conc x_conc =>
        let r := FieldRepresentation.get r_conc;
        let x := FieldRepresentation.get x_conc;
        { r := r, x := x })
-/
#guard_msgs in
#check decidableForallFieldRep.local_abstract_eq

end AssertionDecidableFieldRep

veil module AssertionAutoParamPrettyPrint

veil_set_option useLocalRPropTC false

#gen_state

invariant [pretty] true

/--
info: AssertionAutoParamPrettyPrint.pretty {ρ σ : Type} {χ : State.Label → Type}
  [χ_rep : (__veil_f : State.Label) → FieldRepresentation __veil_f.toDomain __veil_f.toCodomain (χ __veil_f)]
  [χ_rep_lawful :
    ∀ (__veil_f : State.Label),
      LawfulFieldRepresentation __veil_f.toDomain __veil_f.toCodomain (χ __veil_f) (χ_rep __veil_f)]
  [σ_sub : IsSubStateOf (State χ) σ] [ρ_sub : IsSubReaderOf Theory ρ] (th : ρ := by veil_exact_theory)
  (st : σ := by veil_exact_state) : Prop
-/
#guard_msgs in
#check pretty

end AssertionAutoParamPrettyPrint

veil module GhostExprDefinitionRegression

veil_set_option useLocalRPropTC false

type node
relation r : node → node → Bool
individual x : node

#gen_state

-- Regression: ghost definitions should use the same elaborated `Expr` path as
-- assertions, so extracted `Decidable` instances see the concrete field
-- representation used in the body.
ghost relation ghostDecidableForall := if (∀ m, r x m) then true else false

ghost relation prettyRel := true

ghost function prettyFn : Nat := 1

/--
info: GhostExprDefinitionRegression.prettyRel {ρ σ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] {χ : State.Label → Type}
  [χ_rep :
    (__veil_f : State.Label) →
      FieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)]
  [χ_rep_lawful :
    ∀ (__veil_f : State.Label),
      LawfulFieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)
        (χ_rep __veil_f)]
  [σ_sub : IsSubStateOf (State χ) σ] [ρ_sub : IsSubReaderOf (Theory node) ρ] (th : ρ := by veil_exact_theory)
  (st : σ := by veil_exact_state) : Prop
-/
#guard_msgs in
#check prettyRel

/--
info: GhostExprDefinitionRegression.prettyFn {ρ σ node : Type} [node_dec_eq : DecidableEq node]
  [node_inhabited : Inhabited node] {χ : State.Label → Type}
  [χ_rep :
    (__veil_f : State.Label) →
      FieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)]
  [χ_rep_lawful :
    ∀ (__veil_f : State.Label),
      LawfulFieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f) (χ __veil_f)
        (χ_rep __veil_f)]
  [σ_sub : IsSubStateOf (State χ) σ] [ρ_sub : IsSubReaderOf (Theory node) ρ] (th : ρ := by veil_exact_theory)
  (st : σ := by veil_exact_state) : ℕ
-/
#guard_msgs in
#check prettyFn

end GhostExprDefinitionRegression
