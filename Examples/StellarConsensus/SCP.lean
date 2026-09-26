module

public import Veil
public import Examples.StellarConsensus.SCPTheory

open scoped FBA

-- adapted from [SCP.ivy](https://github.com/stellar/scp-proofs/blob/3e0428acc78e598a227a866b99fe0b3ad4582914/SCP.ivy)

/-
  NOTE: For now we do not prove liveness property in Veil, so we only
  adapt the proof for `intertwined_safe`.
-/

/-- This type class bundles the properties abstracted from the concrete model
    of SCP, which will be used in the subsequent verification.
    In the Ivy spec, they appear as `trusted` properties (assumptions). -/
public class SCP.Background (node : outParam Type) (nset : outParam Type) where
  well_behaved : node → Prop
  intertwined : node → Prop
  intact : node → Prop
  member : node → nset → Prop
  is_quorum : nset → Prop
  blocks_slices : nset → node → Prop

  axiom_0 : ∀ (n : node), intact n → intertwined n
  axiom_1 : ∀ (n : node), intertwined n → well_behaved n
  qi_intertwined : ∀ (q1 q2 : nset),
    (∃ (n1 : node), intertwined n1 ∧ is_quorum q1 ∧ member n1 q1) ∧
    (∃ (n2 : node), intertwined n2 ∧ is_quorum q2 ∧ member n2 q2) →
    ∃ (n3 : node), well_behaved n3 ∧ member n3 q1 ∧ member n3 q2

/-- Given a concrete system model `FBA.System`, fix the intertwined set `S` and
    the intact set `I ⊆ S` to consider, all abstracted properties can be satisfied. -/
@[reducible] def one_such_Background (node : Type) [fba : FBA.System node]
    (I : FBA.NodeSet node) (_hI : FBA.intact (inst := fba) I)
    (S : FBA.NodeSet node) (hS : FBA.intertwined (inst := fba) S)
    (hIS : I ⊆ S) : SCP.Background node (FBA.NodeSet node) where
  well_behaved n := n ∈ fba.W
  intertwined n := n ∈ S
  intact n := n ∈ I
  member n s := n ∈ s
  is_quorum := FBA.quorum (inst := fba)
  blocks_slices := FBA.blocks_slices (inst := fba)

  axiom_0 := by assumption
  axiom_1 := by
    intro n
    apply FBA.intertwined_node_is_well_behaved
    assumption
  qi_intertwined := by
    simp
    intro q1 q2
    have hinter := hS.q_inter q1 q2
    repeat rw [FBA.set_ne_empty_iff_exists_mem] at hinter
    simp at hinter
    intro n hin hq1 hinq1 n' hin' hq2 hinq2
    specialize hinter
      (FBA.quorum_after_proj (inst := { W := fba.W, slices := fba.slices, slices_ne := fba.slices_ne }) _ _ hq1)
      (FBA.quorum_after_proj (inst := { W := fba.W, slices := fba.slices, slices_ne := fba.slices_ne }) _ _ hq2)
      _ hinq1 hin _ hinq2 hin'
    rcases hinter with ⟨nn, h11, h22⟩
    exists nn
    apply And.intro
    · apply FBA.intertwined_node_is_well_behaved <;> assumption
    · assumption

veil module SCP

type value
type node
type nset
type ballot

/- NOTE: In `SCP.ivy`, `ballot` is modelled as an unbounded sequence,
   but neither `next` nor `prev` appears in the protocol or any invariant.
   So here we model `ballot` as simply a `TotalOrderWithMinimum`. -/
instantiate tot : TotalOrderWithMinimum ballot
instantiate bg : Background node nset

open Background

-- Parts for the protocol.
relation voted_prepared (N : node) (B : ballot) (V : value)
relation accepted_prepared (N : node) (B : ballot) (V : value)
relation confirmed_prepared (N : node) (B : ballot) (V : value)
relation voted_committed (N : node) (B : ballot) (V : value)
relation accepted_committed (N : node) (B : ballot) (V : value)
relation confirmed_committed (N : node) (B : ballot) (V : value)
relation nomination_output (N : node) (V : value)
relation started (N : node) (B : ballot)
relation left_ballot (N : node) (B : ballot)

relation received_vote_prepare (N1 : node) (N2 : node) (B : ballot) (V : value)
relation received_accept_prepare (N1 : node) (N2 : node) (B : ballot) (V : value)
relation received_vote_commit (N1 : node) (N2 : node) (B : ballot) (V : value)
relation received_accept_commit (N1 : node) (N2 : node) (B : ballot) (V : value)

#gen_state

-- NOTE: the following seem to be unnecessary for proving the safety.
/-
assumption [qi_intact]
  ∀ (q1 q2 : nset),
    (∃ (n1 : node), intact n1 ∧ is_quorum q1 ∧ member n1 q1) ∧
    (∃ (n2 : node), intact n2 ∧ is_quorum q2 ∧ member n2 q2) →
    ∃ (n3 : node), intact n3 ∧ member n3 q1 ∧ member n3 q2

assumption [slice_blocks_ne]
  ∀ (s : nset), (∃ (n : node), intact n ∧ blocks_slices s n) → ∃ (n2 : node), member n2 s ∧ intact n2

assumption [intact_is_quorum]
  ∃ (q : nset), (∀ (n : node), member n q ↔ intact n) ∧ is_quorum q
-/

after_init {
  voted_prepared N B V := false
  accepted_prepared N B V := false
  confirmed_prepared N B V := false
  voted_committed N B V := false
  accepted_committed N B V := false
  confirmed_committed N B V := false
  nomination_output N X := false
  left_ballot N B := false
  started N B := false
  received_vote_prepare N1 N2 B V := false
  received_vote_commit N1 N2 B V := false
  received_accept_prepare N1 N2 B V := false
  received_accept_commit N1 N2 B V := false
}

action nomination_update (n : node) (v : value) {
  nomination_output n V := V == v
}

action change_ballot (n : node) (b : ballot) {
  require ¬ left_ballot n b ∧ ¬ started n b
  left_ballot n B := decide $ tot.lt B b
  started n b := true
  let bmax : ballot ← pick
  let vmax : value ← pick
  require
    ((∀ B V, tot.lt B b → ¬ confirmed_prepared n B V) ∧ nomination_output n vmax) ∨
      (tot.lt bmax b ∧ confirmed_prepared n bmax vmax ∧
        (∀ B V, tot.lt B b ∧ confirmed_prepared n B V → tot.le B bmax))
  voted_prepared n b vmax := true
}

action receive_vote_prepare (na nb : node) (b : ballot) (v : value) {
  require voted_prepared nb b v
  received_vote_prepare na nb b v := true
  if (∃ Q, is_quorum Q ∧ member na Q ∧
      (∀ N, member N Q → (received_vote_prepare na N b v ∨ received_accept_prepare na N b v)))
    ∧ (∀ B V, ¬ (accepted_committed na B V ∧ tot.lt B b ∧ V ≠ v))
    ∧ (∀ V, ¬ accepted_prepared na b V) then
    accepted_prepared na b v := true
}

action receive_accept_prepare (na nb : node) (b : ballot) (v : value) {
  require accepted_prepared nb b v
  received_accept_prepare na nb b v := true
  if (∃ Q, is_quorum Q ∧ member na Q ∧
      (∀ N, member N Q → received_accept_prepare na N b v)) then
    confirmed_prepared na b v := true
    if ¬ left_ballot na b then
      voted_committed na b v := true
  if ((∃ Q, is_quorum Q ∧ member na Q ∧
        (∀ N, member N Q → (received_vote_prepare na N b v ∨ received_accept_prepare na N b v)))
      ∨ (∃ S, blocks_slices S na ∧ (∀ N, member N S → received_accept_prepare na N b v)))
    ∧ (∀ B V, ¬ (accepted_committed na B V ∧ tot.lt B b ∧ V ≠ v))
    ∧ (∀ V, ¬ accepted_prepared na b V) then
    accepted_prepared na b v := true
}

action receive_vote_commit (na nb : node) (b : ballot) (v : value) {
  require voted_committed nb b v
  received_vote_commit na nb b v := true
  if (∃ Q, is_quorum Q ∧ member na Q ∧
      (∀ N, member N Q → (received_vote_commit na N b v ∨ received_accept_commit na N b v)))
    ∧ (∀ B V, ¬ (accepted_prepared na B V ∧ tot.lt b B ∧ V ≠ v))
    ∧ (∀ V, ¬ accepted_committed na b V)
    ∧ confirmed_prepared na b v then
    accepted_committed na b v := true
}

action receive_accept_commit (na nb : node) (b : ballot) (v : value) {
  require accepted_committed nb b v
  received_accept_commit na nb b v := true
  if (∃ Q, is_quorum Q ∧ member na Q ∧
      (∀ N, member N Q → received_accept_commit na N b v)) then
    confirmed_committed na b v := true
  if ((∃ Q, is_quorum Q ∧ member na Q ∧
        (∀ N, member N Q → (received_vote_commit na N b v ∨ received_accept_commit na N b v)))
      ∨ (∃ S, blocks_slices S na ∧ (∀ N, member N S → received_accept_commit na N b v)))
    ∧ (∀ B V, ¬ (accepted_prepared na B V ∧ tot.lt b B ∧ V ≠ v))
    ∧ (∀ V, ¬ accepted_committed na b V)
    ∧ confirmed_prepared na b v then
    accepted_committed na b v := true
}

transition byzantine_step {
  (∀ N B X, well_behaved N → voted_prepared N B X = voted_prepared' N B X) ∧
  (∀ N B X, well_behaved N → accepted_prepared N B X = accepted_prepared' N B X) ∧
  (∀ N B X, well_behaved N → voted_committed N B X = voted_committed' N B X) ∧
  (∀ N B X, well_behaved N → accepted_committed N B X = accepted_committed' N B X) ∧
  (∀ N B X, well_behaved N → confirmed_prepared N B X = confirmed_prepared' N B X) ∧
  (∀ N B X, well_behaved N → confirmed_committed N B X = confirmed_committed' N B X) ∧
  (∀ N X, well_behaved N → nomination_output N X = nomination_output' N X) ∧
  (∀ N B, well_behaved N → started N B = started' N B) ∧
  (∀ N B, well_behaved N → left_ballot N B = left_ballot' N B) ∧
  (∀ N1 N2 B X, well_behaved N1 → received_vote_prepare N1 N2 B X = received_vote_prepare' N1 N2 B X) ∧
  (∀ N1 N2 B X, well_behaved N1 → received_accept_prepare N1 N2 B X = received_accept_prepare' N1 N2 B X) ∧
  (∀ N1 N2 B X, well_behaved N1 → received_vote_commit N1 N2 B X = received_vote_commit' N1 N2 B X) ∧
  (∀ N1 N2 B X, well_behaved N1 → received_accept_commit N1 N2 B X = received_accept_commit' N1 N2 B X)
}

-- The main safety property.
safety [intertwined_safe]
  ∀ (n1 n2 : node) (b1 b2 : ballot) (v1 v2 : value),
    intertwined n1 ∧ intertwined n2 ∧ confirmed_committed n1 b1 v1 ∧ confirmed_committed n2 b2 v2 → v1 = v2

-- Auxiliary invariants.
invariant ∀ N B V, well_behaved N ∧ accepted_committed N B V → confirmed_prepared N B V

invariant ∀ N B1 B2 V1 V2,
  well_behaved N ∧ accepted_prepared N B2 V2 ∧ (tot.lt B1 B2 ∧ V1 ≠ V2) →
    ¬ accepted_committed N B1 V1

invariant (∃ N, intertwined N ∧ confirmed_committed N B V) →
  ∃ Q, is_quorum Q ∧ (∃ N, intertwined N ∧ member N Q) ∧
    (∀ N, well_behaved N ∧ member N Q → accepted_committed N B V)

invariant (∃ N, intertwined N ∧ confirmed_prepared N B V) →
  ∃ Q, is_quorum Q ∧ (∃ N, intertwined N ∧ member N Q) ∧
    (∀ N, well_behaved N ∧ member N Q → accepted_prepared N B V)

invariant ∀ N N2 B V, well_behaved N ∧ received_accept_commit N N2 B V ∧ well_behaved N2 →
  accepted_committed N2 B V

invariant ∀ N N2 B V, well_behaved N ∧ received_accept_prepare N N2 B V ∧ well_behaved N2 →
  accepted_prepared N2 B V

invariant ∀ N B V1 V2,
  well_behaved N ∧ accepted_prepared N B V1 ∧ accepted_prepared N B V2 → V1 = V2

#gen_spec

@[veil]
theorem receive_accept_commit_intertwined_safe (ρ : Type) (σ : Type) (value : Type)
    [value_dec_eq : DecidableEq.{1} value] [value_inhabited : Inhabited.{1} value] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (nset : Type)
    [nset_dec_eq : DecidableEq.{1} nset] [nset_inhabited : Inhabited.{1} nset] (ballot : Type)
    [ballot_dec_eq : DecidableEq.{1} ballot] [ballot_inhabited : Inhabited.{1} ballot]
    [tot : TotalOrderWithMinimum ballot] [bg : Background node nset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain value node nset ballot __veil_f)
          (State.Label.toCodomain value node nset ballot __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain value node nset ballot __veil_f)
          (State.Label.toCodomain value node nset ballot __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory value node nset ballot) ρ]
    [receive_accept_commit_dec_0 :
      delta% @SCP.receive_accept_commit._veil_dec_type_0 node ballot value χ nset bg χ_rep tot]
    [receive_accept_commit_dec_1 :
      delta% @SCP.receive_accept_commit._veil_dec_type_1 node ballot value χ nset bg χ_rep] :
    ∀ (na : node) (nb : node) (b : ballot) (v : value),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@receive_accept_commit.ext ρ σ value value_dec_eq value_inhabited node node_dec_eq node_inhabited nset
          nset_dec_eq nset_inhabited ballot ballot_dec_eq ballot_inhabited tot bg χ χ_rep χ_rep_lawful σ_sub ρ_sub
          receive_accept_commit_dec_0 receive_accept_commit_dec_1 na nb b v)
        (@Assumptions ρ value value_dec_eq value_inhabited node node_dec_eq node_inhabited nset nset_dec_eq
          nset_inhabited ballot ballot_dec_eq ballot_inhabited tot bg ρ_sub)
        (@Invariants ρ σ value value_dec_eq value_inhabited node node_dec_eq node_inhabited nset nset_dec_eq
          nset_inhabited ballot ballot_dec_eq ballot_inhabited tot bg χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@intertwined_safe ρ σ value value_dec_eq value_inhabited node node_dec_eq node_inhabited nset nset_dec_eq
          nset_inhabited ballot ballot_dec_eq ballot_inhabited tot bg χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  classical
  rcases hinv with ⟨hsafe, hcommitted_prepared, hno_conflict, hconfirmed_quorum,
    hprepared_quorum, hreceived, _, hprepared_unique⟩
  have intersect {Q1 Q2 : nset} (hq1 : is_quorum Q1)
      (hm1 : ∃ n, intertwined n ∧ member n Q1) (hq2 : is_quorum Q2)
      (hm2 : ∃ n, intertwined n ∧ member n Q2) :
      ∃ n, well_behaved n ∧ member n Q1 ∧ member n Q2 := by
    obtain ⟨n1, hn1, hm1⟩ := hm1
    obtain ⟨n2, hn2, hm2⟩ := hm2
    exact bg.qi_intertwined Q1 Q2 ⟨⟨n1, hn1, hq1, hm1⟩, ⟨n2, hn2, hq2, hm2⟩⟩
  have prepared_quorum (B : ballot) (V : value) (Q : nset)
      (hm : ∃ n, intertwined n ∧ member n Q)
      (hc : ∀ n, well_behaved n → member n Q → st.accepted_committed n B V = true) :
      ∃ P, is_quorum P ∧ (∃ n, intertwined n ∧ member n P) ∧
        ∀ n, well_behaved n → member n P → st.accepted_prepared n B V = true := by
    obtain ⟨n, hn, hm⟩ := hm
    exact hprepared_quorum B V n hn
      (hcommitted_prepared n B V (bg.axiom_1 n hn) (hc n (bg.axiom_1 n hn) hm))
  have quorum_agreement (B1 B2 : ballot) (V1 V2 : value) (Q1 Q2 : nset)
      (hq1 : is_quorum Q1) (hm1 : ∃ n, intertwined n ∧ member n Q1)
      (hc1 : ∀ n, well_behaved n → member n Q1 → st.accepted_committed n B1 V1 = true)
      (hq2 : is_quorum Q2) (hm2 : ∃ n, intertwined n ∧ member n Q2)
      (hc2 : ∀ n, well_behaved n → member n Q2 → st.accepted_committed n B2 V2 = true) :
      V1 = V2 := by
    obtain ⟨P1, hp1, hpm1, hprep1⟩ := prepared_quorum B1 V1 Q1 hm1 hc1
    obtain ⟨P2, hp2, hpm2, hprep2⟩ := prepared_quorum B2 V2 Q2 hm2 hc2
    by_cases hb : B1 = B2
    · subst B2
      obtain ⟨n, hn, hn1, hn2⟩ := intersect hp1 hpm1 hp2 hpm2
      exact hprepared_unique n B1 V1 V2 hn (hprep1 n hn hn1) (hprep2 n hn hn2)
    · by_contra hv
      rcases tot.le_total B1 B2 with hle | hle
      · obtain ⟨n, hn, hn1, hn2⟩ := intersect hq1 hm1 hp2 hpm2
        have hfalse := hno_conflict n B1 B2 V1 V2 hn (hprep2 n hn hn2)
          ((tot.le_lt B1 B2).mpr ⟨hle, hb⟩) hv
        rw [hc1 n hn hn1] at hfalse
        contradiction
      · obtain ⟨n, hn, hn2, hn1⟩ := intersect hq2 hm2 hp1 hpm1
        have hfalse := hno_conflict n B2 B1 V2 V1 hn (hprep1 n hn hn1)
          ((tot.le_lt B2 B1).mpr ⟨hle, Ne.symm hb⟩) (Ne.symm hv)
        rw [hc2 n hn hn2] at hfalse
        contradiction
  intro haccepted
  split_ifs with hconfirm
  · obtain ⟨Q, hq, hmember, hmessages⟩ := hconfirm
    have confirmed_quorum (n : node) (B : ballot) (V : value) (hn : intertwined n)
        (hc : (na = n → b = B → ¬v = V) → st.confirmed_committed n B V = true) :
        ∃ Q, is_quorum Q ∧ (∃ n, intertwined n ∧ member n Q) ∧
          ∀ n, well_behaved n → member n Q → st.accepted_committed n B V = true := by
      by_cases hnew : na = n ∧ b = B ∧ v = V
      · rcases hnew with ⟨rfl, rfl, rfl⟩
        refine ⟨Q, hq, ⟨na, hn, hmember⟩, ?_⟩
        intro N hN hm
        by_cases hnb : nb = N
        · simpa [hnb] using haccepted
        · exact hreceived na N b v (bg.axiom_1 na hn) (hmessages N hm hnb) hN
      · exact hconfirmed_quorum B V n hn (hc (by
          intro ha hb hv
          exact hnew ⟨ha, hb, hv⟩))
    intro n1 n2 b1 b2 v1 v2 hn1 hn2 hc1 hc2
    obtain ⟨Q1, hq1, hm1, hcomm1⟩ := confirmed_quorum n1 b1 v1 hn1 hc1
    obtain ⟨Q2, hq2, hm2, hcomm2⟩ := confirmed_quorum n2 b2 v2 hn2 hc2
    exact quorum_agreement b1 b2 v1 v2 Q1 Q2 hq1 hm1 hcomm1 hq2 hm2 hcomm2
  · exact hsafe

#time #check_invariants

end SCP
