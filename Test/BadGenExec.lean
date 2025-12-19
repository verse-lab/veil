import Veil

-- https://github.com/aman-goel/ivybench/blob/5db7eccb5c3bc2dd14dfb58eddb859b036d699f5/ex/ivy/ring.ivy

-- set_option trace.veil.desugar true

veil module Ring

type node
-- type foo

-- inductive Action (node : Type) where
--   | send (n next : node)
--   | recv (sender n next : node)
-- deriving Inhabited, Ord, Lean.ToJson, Hashable, BEq, Repr

instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

relation leader : node -> Bool
relation pending : node -> node -> Bool

set_option trace.veil.desugar true

#time #gen_state

after_init {
  -- log := []
  leader N := false
  pending M N := false
}

-- transition skip {
--   leader' = leader
-- }

action send (n next : node) {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  -- log := log ++ [Action.send n next]
  pending n next := true
}

action recv (sender n next : node) {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  require pending sender n
  -- log := log ++ [Action.recv sender n next]
  -- message may or may not be removed
  -- this models that multiple messages might be in flight
  let b ← pick Bool
  pending sender n := b  -- FIXME: `pending sender n := *` has bad execution performance
  if (sender = n) then
    leader n := true
  else
    -- pass message to next node
    if (le n sender) then
      pending sender next := true
}

-- action nondet_log  {
--   log := *
-- }


safety [single_leader] leader N ∧ leader M → N = M
invariant [leader_greatest] leader L → le N L
-- invariant [inv_1] pending S D ∧ btw S N D → le N S
invariant [inv_2] pending L L → le N L

#gen_spec

#check_invariants


theorem recv_single_leader' (ρ : Type) (σ : Type) (node : Type) [node_dec_eq : DecidableEq.{1} node]
    [node_inhabited : Inhabited.{1} node] [tot : TotalOrder node] [btwn : Between node]
    (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain node __veil_f)
          (State.Label.toCodomain node __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain node __veil_f)
          (State.Label.toCodomain node __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory node) ρ]
    [recv_dec_0 :
      (n next : node) →
        Decidable
          (∀ (Z : node),
            And (@Eq.{1} node n next → False)
              (And (@Ne.{1} node Z n) (@Ne.{1} node Z next) → btwn.1 n next Z))]
    [recv_dec_1 : (sender n : node) → Decidable (tot.1 n sender)] :
    ∀ (sender : node) (n : node) (next : node),
      Veil.Transition.meetsSpecificationIfSuccessfulAssuming
        (@recv.ext.tr ρ σ node node_dec_eq node_inhabited tot btwn χ χ_rep χ_rep_lawful σ_sub ρ_sub
          recv_dec_0 recv_dec_1 sender n next)
        (@Assumptions ρ node node_dec_eq node_inhabited tot btwn ρ_sub)
        (@Invariants ρ σ node node_dec_eq node_inhabited tot btwn χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@single_leader ρ σ node node_dec_eq node_inhabited tot btwn χ χ_rep χ_rep_lawful σ_sub
          ρ_sub) :=
  by
  -- unfold Veil.Transition.meetsSpecificationIfSuccessfulAssuming Veil.Transition.meetsSpecificationIfSuccessful Veil.Transition.triple recv.ext.tr
  veil_intros
  veil_neutralize_decidable_inst
  veil_intro_ho -- what does this do?
  unhygienic intros
  veil_destruct only [And, Exists]
  simp only [ifSimp] at *
  veil_destruct only [And, Exists]
  unfold single_leader
  unhygienic split_ifs at *
  {
    veil_concretize_state
    -- veil_concretize_fields
    -- Qiyuan: how to make this work???

    veil_simp only [fieldRepresentationSetSimpPre] at *
    open Classical in veil_simp only [(χ_rep_lawful .leader).get_set_idempotent' (by infer_instance_for_iterated_prod),
          (χ_rep_lawful .pending).get_set_idempotent' (by infer_instance_for_iterated_prod)]  at *
    open Classical in veil_simp only [fieldRepresentationSetSimpPost, State.Label.toDomain, State.Label.toCodomain]  at *

    generalize hLeaderGet: ((χ_rep _).get) st.leader = __veil_leader at *;  dsimp [State.Label.toDomain, State.Label.toCodomain] at __veil_leader
    generalize hLeaderSet: ((χ_rep _).set) _ st.leader = __veil_leader' at *; -- I think we need this


    generalize hPendingGet: ((χ_rep _).get) st.pending = __veil_pending at *;  dsimp [State.Label.toDomain, State.Label.toCodomain] at __veil_pending
    generalize hPendingSet: ((χ_rep _).set) _ st.pending = __veil_pending' at *;

    -- There must be a better way to do this
    simp_all only [← hLeaderSet] -- this is to simplify using `a_1_1_1.right_1.left.left : st'.leader = __veil_leader'`
    simp_all only [← hPendingSet] -- this is to simplify using `a_1_1_1.right_1.left.right : st'.pending = __veil_pending'`

    veil_simp only [fieldRepresentationSetSimpPre] at *
    open Classical in veil_simp only [(χ_rep_lawful .leader).get_set_idempotent' (by infer_instance_for_iterated_prod),
        (χ_rep_lawful .pending).get_set_idempotent' (by infer_instance_for_iterated_prod)]  at *
    open Classical in veil_simp only [fieldRepresentationSetSimpPost, State.Label.toDomain, State.Label.toCodomain]  at *
    simp_all

    sorry

  }
  sorry
  sorry

#time #model_check { node := Fin 5 } { }

end Ring
