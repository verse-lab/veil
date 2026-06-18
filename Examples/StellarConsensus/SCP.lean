import Veil
import Examples.StellarConsensus.SCPTheory

-- adapted from [SCP.ivy](https://github.com/stellar/scp-proofs/blob/3e0428acc78e598a227a866b99fe0b3ad4582914/SCP.ivy)


/-- This type class bundles the properties abstracted from the concrete model
    of SCP, which will be used in the subsequent verification.
    In the Ivy spec, they appear as `trusted` properties (assumptions). -/
class SCP.FBQS_Safety (node : outParam Type) (nset : outParam Type) where
  well_behaved : node → Prop
  intertwined : node → Prop
  intact : node → Prop
  member : node → nset → Prop
  is_quorum : nset → Prop
  slice_blocking : nset → node → Prop

  -- Basic properties of node sets
  axiom_0 : ∀ (n : node), intact n → intertwined n
  axiom_1 : ∀ (n : node), intertwined n → well_behaved n
  -- Needed for safety
  qi_intertwined : ∀ (q1 q2 : nset),
    (∃ (n1 : node), intertwined n1 ∧ is_quorum q1 ∧ member n1 q1) ∧
    (∃ (n2 : node), intertwined n2 ∧ is_quorum q2 ∧ member n2 q2) →
    ∃ (n3 : node), well_behaved n3 ∧ member n3 q1 ∧ member n3 q2

class SCP.FBQS (node : outParam Type) (nset : outParam Type) extends SCP.FBQS_Safety node nset where
  -- Needed for liveness (we keep these separate for decidability)
  qi_intact : ∀ (q1 q2 : nset),
    (∃ (n1 : node), intact n1 ∧ is_quorum q1 ∧ member n1 q1) ∧
    (∃ (n2 : node), intact n2 ∧ is_quorum q2 ∧ member n2 q2) →
    ∃ (n3 : node), intact n3 ∧ member n3 q1 ∧ member n3 q2
  slice_blocks_ne : ∀ (s : nset),
    (∃ (n : node), intact n ∧ slice_blocking s n) →
    ∃ (n2 : node), member n2 s ∧ intact n2
  intact_is_quorum :
    ∃ (q : nset), (∀ (n : node), member n q ↔ intact n) ∧ is_quorum q

/-- Given a concrete system model `FBA.System`, fix the intertwined set `S` and
    the intact set `I ⊆ S` to consider, all abstracted properties can be satisfied. -/
def one_such_FBQS (node : Type) [fba : FBA.System node]
    (I : Set node) (hI : FBA.intact (inst := fba) I)
    (S : Set node) (hS : FBA.intertwined (inst := fba) S)
    (hIS : I ⊆ S) : SCP.FBQS node (Set node) where
  well_behaved n := n ∈ fba.W
  intertwined n := n ∈ S
  intact n := n ∈ I
  member n s := n ∈ s
  is_quorum := FBA.quorum (inst := fba)
  slice_blocking := FBA.slice_blocking (inst := fba)

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
  qi_intact := by
    simp
    intro q1 q2 n1 hn1I hq1 hn1q1 n2 hn2I hq2 hn2q2
    have hinter := hI.q_inter q1 q2
      (FBA.quorum_after_proj (inst := fba) q1 I hq1)
      (FBA.quorum_after_proj (inst := fba) q2 I hq2)
    repeat rw [FBA.set_ne_empty_iff_exists_mem] at hinter
    simp only [Set.mem_inter_iff, forall_exists_index, and_imp] at hinter
    specialize hinter n1 hn1q1 hn1I n2 hn2q2 hn2I
    rcases hinter with ⟨n3, ⟨hn3q1, hn3q2⟩, hn3I⟩
    exact ⟨n3, hn3I, hn3q1, hn3q2⟩
  slice_blocks_ne := by
    intro s hs
    rcases hs with ⟨n, hnI, hblocks⟩
    have h := FBA.slice_blocks_ne (inst := fba) n s I hI hnI hblocks
    rw [FBA.set_ne_empty_iff_exists_mem] at h
    rcases h with ⟨n2, hn2s, hn2I⟩
    exact ⟨n2, hn2s, hn2I⟩
  intact_is_quorum := by
    exact ⟨I, by simp, hI.q_avail⟩

veil module SCP

type value
type node
type nset
type ballot

/- NOTE: In `SCP.ivy`, `ballot` is modelled as an unbounded sequence,
   but neither `next` nor `prev` appears in the protocol or any invariant.
   So here we model `ballot` as simply a `TotalOrderWithMinimum`. -/
instantiate tot : TotalOrderWithMinimum ballot
instantiate bg : FBQS_Safety node nset

open FBQS_Safety

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
      ∨ (∃ S, slice_blocking S na ∧ (∀ N, member N S → received_accept_prepare na N b v)))
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
      ∨ (∃ S, slice_blocking S na ∧ (∀ N, member N S → received_accept_commit na N b v)))
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

#check_invariants

end SCP
