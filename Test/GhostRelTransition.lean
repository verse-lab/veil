import Veil

veil module GhostRelTransition

type node
instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

relation leader : node -> Bool
relation pending : node -> node -> Bool

#gen_state

after_init {
  leader N := false
  pending M N := false
}

ghost relation isNext (n : node) (next : node) :=
  ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)

action send (n next : node) {
  require isNext n next
  pending n next := true
}

safety [single_leader] leader N ∧ leader M → N = M

#gen_spec

#guard_msgs(drop warning) in
theorem send_single_leader_tr (ρ : Type) (σ : Type) (node : Type) [node_dec_eq : DecidableEq.{1} node]
    [node_inhabited : Inhabited.{1} node] [tot : TotalOrder node] [btwn : Between node] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f)
          (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f)
          (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory node) ρ]
    [send_dec_0 :
      (n next : node) →
        Decidable
          (∀ (Z : node),
            And (@Eq.{1} node n next → False) (And (@Ne.{1} node Z n) (@Ne.{1} node Z next) → btwn.1 n next Z))] :
    ∀ (n : node) (next : node),
      Veil.Transition.meetsSpecificationIfSuccessfulAssuming
        (@send.ext.tr ρ σ node node_dec_eq node_inhabited tot btwn χ χ_rep χ_rep_lawful σ_sub ρ_sub send_dec_0 n next)
        (@Assumptions ρ node node_dec_eq node_inhabited tot btwn ρ_sub)
        (@Invariants ρ σ node node_dec_eq node_inhabited tot btwn χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@single_leader ρ σ node node_dec_eq node_inhabited tot btwn χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_solve_tr

end GhostRelTransition
