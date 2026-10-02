module

public import Veil

/-! `unveil` goes through the local WP predicate, in which the branches of each
conditional of the action are shared behind a `letEq (decide c)` barrier (see
`wpCompactIte`).  That form is meant for the SMT pipeline; an interactive proof
wants the conditionals back, so `unveil` undoes the barriers with
`letEq_decide_eq_ite`: a conditional the goal depends on becomes a top-level
`if` again, and one the goal does not depend on disappears.

Without this, the `smtSimp` cleanup turned every barrier into a `Bool`
quantifier and the final `simp` split each quantifier into a conjunction of
implications, duplicating the goal once per barrier.

Here `step` has two sequential conditionals and `r_only_k` depends only on the
first one. -/
veil module UnveilSequentialIte

type node

immutable individual k : node
relation r : node → Bool
individual a : Bool
individual c : Bool

#gen_state

after_init {
  r N := false
  a := false
  c := false
}

action step (n : node) {
  if n = k then
    r n := true
  if a then
    c := true
}

invariant [r_only_k] ∀ N, r N → N = k

#gen_spec

example (ρ : Type) (σ : Type) (node : Type) [node_dec_eq : DecidableEq.{1} node]
    [node_inhabited : Inhabited.{1} node] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f)
          (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f)
          (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory node) ρ] :
    ∀ (n : node),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@step.ext ρ σ node node_dec_eq node_inhabited χ χ_rep χ_rep_lawful σ_sub ρ_sub n)
        (@Assumptions ρ node node_dec_eq node_inhabited ρ_sub)
        (@Invariants ρ σ node node_dec_eq node_inhabited χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@r_only_k ρ σ node node_dec_eq node_inhabited χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  -- The goal is a case split on `n = k` alone; the `a` conditional is gone.
  split_ifs with hk
  · intro N hN
    by_cases hnN : n = N
    · exact hnN.symm.trans hk
    · exact hinv N (hN hnN)
  · exact hinv

end UnveilSequentialIte
