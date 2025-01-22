import Veil.State
import Veil.TransitionSystem
import Veil.Tactic
import Veil.DSL
import Examples.DSL.Std

-- adapted from [SCP.ivy](https://github.com/stellar/scp-proofs/blob/3e0428acc78e598a227a866b99fe0b3ad4582914/SCP.ivy)
-- CHECK only for safety proof?

class UnboundedSequence (t : Type) where
  -- relation: strict total order
  le (x y : t) : Prop
  -- axioms
  le_refl (x : t) : le x x
  le_trans (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total (x y : t) : le x y ∨ le y x

  -- relation: nonstrict total order
  lt (x y : t) : Prop
  le_lt (x y : t) : lt x y ↔ (le x y ∧ x ≠ y)

  -- successor
  next (x y : t) : Prop
  next_def (x y : t) : next x y ↔ (lt x y ∧ ∀ z, lt x z → le y z)

  -- predecessor
  prev (x y : t) : Prop
  prev_def (x y : t) : lt zero x → (prev x y ↔ (lt y x ∧ ∀ z, lt y z → le x z))

  zero : t
  zero_lt (x : t) : le zero x

namespace SCP
open Classical

type value
type node
type nset
type ballot
instantiate tot : UnboundedSequence ballot

open UnboundedSequence

-- immutable parts
immutable relation well_behaved : node → Prop
immutable relation intertwined : node → Prop
immutable relation intact : node → Prop

immutable relation member : node → nset → Prop
immutable relation is_quorum : nset → Prop
immutable relation blocks_slices : nset → node → Prop

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

-- node properties
assumption ∀ (n : node), intact n → intertwined n
assumption ∀ (n : node), intertwined n → well_behaved n

-- quorum properties
assumption [qi_intertwined]
  ∀ (q1 q2 : nset),
    (∃ (n1 : node), intertwined n1 ∧ is_quorum q1 ∧ member n1 q1) ∧
    (∃ (n2 : node), intertwined n2 ∧ is_quorum q2 ∧ member n2 q2) →
    ∃ (n3 : node), well_behaved n3 ∧ member n3 q1 ∧ member n3 q2

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
  let bmax : ballot ← fresh
  let vmax : value ← fresh
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

internal transition byzantine_step = fun st st' =>
  (∀ N B X, st.well_behaved N → st.voted_prepared N B X = st'.voted_prepared N B X) ∧
  (∀ N B X, st.well_behaved N → st.accepted_prepared N B X = st'.accepted_prepared N B X) ∧
  (∀ N B X, st.well_behaved N → st.voted_committed N B X = st'.voted_committed N B X) ∧
  (∀ N B X, st.well_behaved N → st.accepted_committed N B X = st'.accepted_committed N B X) ∧
  (∀ N B X, st.well_behaved N → st.confirmed_prepared N B X = st'.confirmed_prepared N B X) ∧
  (∀ N B X, st.well_behaved N → st.confirmed_committed N B X = st'.confirmed_committed N B X) ∧
  (∀ N X, st.well_behaved N → st.nomination_output N X = st'.nomination_output N X) ∧
  (∀ N B, st.well_behaved N → st.started N B = st'.started N B) ∧
  (∀ N B, st.well_behaved N → st.left_ballot N B = st'.left_ballot N B) ∧
  (∀ N1 N2 B X, st.well_behaved N1 → st.received_vote_prepare N1 N2 B X = st'.received_vote_prepare N1 N2 B X) ∧
  (∀ N1 N2 B X, st.well_behaved N1 → st.received_accept_prepare N1 N2 B X = st'.received_accept_prepare N1 N2 B X) ∧
  (∀ N1 N2 B X, st.well_behaved N1 → st.received_vote_commit N1 N2 B X = st'.received_vote_commit N1 N2 B X) ∧
  (∀ N1 N2 B X, st.well_behaved N1 → st.received_accept_commit N1 N2 B X = st'.received_accept_commit N1 N2 B X) ∧
  -- coherence; guess need to add them; FIXME: can they be added automatically, as they are `immutable`?
  (∀ N, st.well_behaved N = st'.well_behaved N) ∧
  (∀ N, st.intertwined N = st'.intertwined N) ∧
  (∀ N, st.intact N = st'.intact N) ∧
  (∀ N Q, st.member N Q = st'.member N Q) ∧
  (∀ Q, st.is_quorum Q = st'.is_quorum Q) ∧
  (∀ S N, st.blocks_slices S N = st'.blocks_slices S N)

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

set_option maxHeartbeats 8000000
set_option auto.smt.timeout 600

#check_invariants

end SCP
