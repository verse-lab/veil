import Veil
import Examples.StellarConsensus.SCPTheory

-- adapted from [SCP.ivy](https://github.com/stellar/scp-proofs/blob/3e0428acc78e598a227a866b99fe0b3ad4582914/SCP.ivy)

/-
  NOTE: For now we do not prove liveness property in Veil, so we only
  adapt the proof for `intertwined_safe`.
-/

/-- This type class bundles the properties abstracted from the concrete model
    of SCP, which will be used in the subsequent verification.
    In the Ivy spec, they appear as `trusted` properties (assumptions). -/
class SCP.Background (node : outParam Type) (nset : outParam Type) where
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
def one_such_Background (node : Type) [fba : FBA.System node]
    (I : Set node) (hI : FBA.intact (inst := fba) I)
    (S : Set node) (hS : FBA.intertwined (inst := fba) S)
    (hIS : I ⊆ S) : SCP.Background node (Set node) where
  well_behaved n := n ∈ fba.W
  intertwined n := n ∈ S
  intact n := n ∈ I
  member n s := n ∈ s
  is_quorum := FBA.quorum (inst := fba)
  blocks_slices := FBA.blocks_slices (inst := fba)

  axiom_0 := by assumption
  axiom_1 := by intro n ; apply FBA.intertwined_node_is_well_behaved ; assumption
  qi_intertwined := by
    simp ; intro q1 q2
    have hinter := hS.q_inter q1 q2
    repeat rw [Set.ne_empty_iff_exists_mem] at hinter
    simp at hinter
    intro n hin hq1 hinq1 n' hin' hq2 hinq2
    specialize hinter
      (FBA.quorum_after_proj (inst := { W := fba.W, slices := fba.slices, slices_ne := fba.slices_ne }) _ _ hq1)
      (FBA.quorum_after_proj (inst := { W := fba.W, slices := fba.slices, slices_ne := fba.slices_ne }) _ _ hq2)
      _ hinq1 hin _ hinq2 hin'
    rcases hinter with ⟨nn, h11, h22⟩ ; exists nn ; apply And.intro
    next => apply FBA.intertwined_node_is_well_behaved <;> assumption
    next => assumption

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

open TotalOrderWithMinimum Background

-- parts for the protocol
relation voted_prepared : node → ballot → value → Prop
relation accepted_prepared : node → ballot → value → Prop
relation confirmed_prepared : node → ballot → value → Prop
relation voted_committed : node → ballot → value → Prop
relation accepted_committed : node → ballot → value → Prop
relation confirmed_committed : node → ballot → value → Prop
relation nomination_output : node → value → Prop
relation started : node → ballot → Prop
relation left_ballot : node → ballot → Prop

relation received_vote_prepare : node → node → ballot → value → Prop
relation received_accept_prepare : node → node → ballot → value → Prop
relation received_vote_commit : node → node → ballot → value → Prop
relation received_accept_commit : node → node → ballot → value → Prop

#gen_state

-- NOTE: the following seem to be unnecessary for proving the safety
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
  voted_prepared N B V := False;
  accepted_prepared N B V := False;
  confirmed_prepared N B V := False;
  voted_committed N B V := False;
  accepted_committed N B V := False;
  confirmed_committed N B V := False;
  nomination_output N X := False;
  left_ballot N B := False;
  started N B := False;
  received_vote_prepare N1 N2 B V := False;
  received_vote_commit N1 N2 B V := False;
  received_accept_prepare N1 N2 B V := False;
  received_accept_commit N1 N2 B V := False;
}

action nomination_update (n : node) (v : value) = {
  nomination_output n V := V = v;
}

action change_ballot (n : node) (b : ballot) = {
  require ¬ left_ballot n b ∧ ¬ started n b
  left_ballot n B := lt B b
  started n b := True
  let bmax : ballot ← pick
  let vmax : value ← pick
  require
    ((∀ B V, lt B b → ¬ confirmed_prepared n B V) ∧ nomination_output n vmax) ∨
    (lt bmax b ∧ confirmed_prepared n bmax vmax ∧
      (∀ B V, lt B b ∧ confirmed_prepared n B V → le B bmax))
  voted_prepared n b vmax := True;
}

action receive_vote_prepare (na nb : node) (b : ballot) (v : value) = {
  require voted_prepared nb b v
  received_vote_prepare na nb b v := True
  if (∃ Q, is_quorum Q ∧ member na Q ∧
      (∀ N, member N Q → (received_vote_prepare na N b v ∨ received_accept_prepare na N b v)))
    ∧ (∀ B V, ¬ (accepted_committed na B V ∧ lt B b ∧ V ≠ v))
    ∧ (∀ V, ¬ accepted_prepared na b V) then
    accepted_prepared na b v := True
}

action receive_accept_prepare (na nb : node) (b : ballot) (v : value) = {
  require accepted_prepared nb b v
  received_accept_prepare na nb b v := True
  if (∃ Q, is_quorum Q ∧ member na Q ∧
      (∀ N, member N Q → received_accept_prepare na N b v)) then
    confirmed_prepared na b v := True
    if ¬ left_ballot na b then
      voted_committed na b v := True
  if ((∃ Q, is_quorum Q ∧ member na Q ∧
        (∀ N, member N Q → (received_vote_prepare na N b v ∨ received_accept_prepare na N b v)))
      ∨ (∃ S, blocks_slices S na ∧ (∀ N, member N S → received_accept_prepare na N b v)))
    ∧ (∀ B V, ¬ (accepted_committed na B V ∧ lt B b ∧ V ≠ v))
    ∧ (∀ V, ¬ accepted_prepared na b V) then
    accepted_prepared na b v := True
}

action receive_vote_commit (na nb : node) (b : ballot) (v : value) = {
  require voted_committed nb b v
  received_vote_commit na nb b v := True
  if (∃ Q, is_quorum Q ∧ member na Q ∧
      (∀ N, member N Q → (received_vote_commit na N b v ∨ received_accept_commit na N b v)))
    ∧ (∀ B V, ¬ (accepted_prepared na B V ∧ lt b B ∧ V ≠ v))
    ∧ (∀ V, ¬ accepted_committed na b V)
    ∧ confirmed_prepared na b v then
    accepted_committed na b v := True
}

action receive_accept_commit (na nb : node) (b : ballot) (v : value) = {
  require accepted_committed nb b v
  received_accept_commit na nb b v := True
  if (∃ Q, is_quorum Q ∧ member na Q ∧
      (∀ N, member N Q → received_accept_commit na N b v)) then
    confirmed_committed na b v := True
  if ((∃ Q, is_quorum Q ∧ member na Q ∧
        (∀ N, member N Q → (received_vote_commit na N b v ∨ received_accept_commit na N b v)))
      ∨ (∃ S, blocks_slices S na ∧ (∀ N, member N S → received_accept_commit na N b v)))
    ∧ (∀ B V, ¬ (accepted_prepared na B V ∧ lt b B ∧ V ≠ v))
    ∧ (∀ V, ¬ accepted_committed na b V)
    ∧ confirmed_prepared na b v then
    accepted_committed na b v := True
}

internal transition byzantine_step = {
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

-- the main safety
safety [intertwined_safe]
  ∀ (n1 n2 : node) (b1 b2 : ballot) (v1 v2 : value),
    intertwined n1 ∧ intertwined n2 ∧ confirmed_committed n1 b1 v1 ∧ confirmed_committed n2 b2 v2 → v1 = v2

-- aux invariants
invariant ∀ N B V, well_behaved N ∧ accepted_committed N B V → confirmed_prepared N B V

invariant ∀ N B1 B2 V1 V2, well_behaved N ∧ accepted_prepared N B2 V2 ∧ (lt B1 B2 ∧ V1 ≠ V2) → ¬ accepted_committed N B1 V1

invariant (∃ N, intertwined N ∧ confirmed_committed N B V) →
  ∃ Q, is_quorum Q ∧ (∃ N, intertwined N ∧ member N Q) ∧ (∀ N, well_behaved N ∧ member N Q → accepted_committed N B V)
invariant (∃ N, intertwined N ∧ confirmed_prepared N B V) →
  ∃ Q, is_quorum Q ∧ (∃ N, intertwined N ∧ member N Q) ∧ (∀ N, well_behaved N ∧ member N Q → accepted_prepared N B V)

invariant ∀ N N2 B V, well_behaved N ∧ received_accept_commit N N2 B V ∧ well_behaved N2 → accepted_committed N2 B V
invariant ∀ N N2 B V, well_behaved N ∧ received_accept_prepare N N2 B V ∧ well_behaved N2 → accepted_prepared N2 B V

invariant ∀ N B V1 V2, well_behaved N ∧ accepted_prepared N B V1 ∧ accepted_prepared N B V2 → V1 = V2

#gen_spec

#time #check_invariants

end SCP
