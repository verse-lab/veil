import LeanSts.DSL

section ReliableBroadcast

/-- Byzantine quorums (2f + 1 nodes) intersect in at least one honest member. -/
class ByzantineQuorum (node : Type) (quorum : outParam Type) :=
  is_byz (a : node) : Prop
  member (a : node) (q : quorum) : Prop
  quorum_intersection :
    ∀ (q1 q2 : quorum), ∃ (a : node), member a q1 ∧ member a q2 ∧ ¬ is_byz a

type quorum
type address
type round
type value

instantiate q : ByzantineQuorum address quorum
open ByzantineQuorum -- so we can write `is_byz` instead of `q.is_byz`

-- TODO: we might want to replace the second condition in `vote` to use this
-- /-- A fraction of nodes (f + 1) with at least one honest member. -/
-- class FractionWithOneHonest (node : Type) (quorum : outParam Type) [ByzantineQuorum node quorum] :=
--   contains (a : node) (q : quorum) : Prop
--   one_honest (q : quorum) : ∃ (a : node), contains a q ∧ ¬ is_byz a

-- instantiate honest_fraction : FractionWithOneHonest address quorum
-- open FractionWithOneHonest

-- Messages over the network
relation initial_msg (originator : address) (dst : address) (r : round) (v : value)
relation echo_msg (src : address) (dst : address) (originator : address) (r : round) (v : value)
relation vote_msg (src : address) (dst : address) (originator : address) (r : round) (v : value)

-- State of the nodes
/- sent(address, round) := has the node initiated round `r`? -/
relation sent (n : address) (r : round)
relation echoed (n : address) (originator : address) (in_round : round) (v : value)
relation voted (n : address) (originator : address) (in_round : round) (v : value)
relation output (n : address) (originator : address) (in_round : round) (v : value)

#gen_state

-- Ghost relations
relation initial_value (n : address) (r : round) (v : value) := ∀ dst, initial_msg n dst r v

after_init {
  initial_msg _ _ _ _ := False;
  echo_msg _ _ _ _ _ := False;
  vote_msg _ _ _ _ _ := False;

  sent _ _ := False;
  echoed _ _ _ _ := False;
  voted _ _ _ _ := False;
  output _ _ _ _ := False
}

action start_round (n : address) (r : round) (v : value) = {
  require ¬ sent n r;
  initial_msg n N r v := True;
  sent n r := True
}

action echo (n : address) (originator : address) (r : round) (v : value) = {
  require initial_msg originator n r v;
  require ¬ echoed n originator r v;
  echoed n originator r v := True;
  echo_msg n DST originator r v := True
}

action vote (n : address) (originator : address) (r : round) (v : value) = {
  -- received a quorum of echo messages OR a vote message from an honest node
  require (∃ (q : quorum), ∀ (src : address), member src q → echo_msg src n originator r v) ∨
          -- in practice, this is triggered when a node receives f + 1 vote messages
          (∃ (src : address), ¬ is_byz src ∧ vote_msg src n originator r v);
  require ¬ voted n originator r v;
  voted n originator r v := True;
  vote_msg n DST originator r v := True
}

action deliver (n : address) (originator : address) (r : round) (v : value) = {
  -- received a quorum of votes
  require (∃ (q : quorum), ∀ (src : address), member src q → vote_msg src n originator r v);
  output n originator r v := True
}

/- If a value is voted for, it is the value that was initially proposed by the originator. -/
safety [vote_integrity]
  ∀ (src dst : address) (r : round) (v : value),
     ¬ is_byz src ∧ ¬ is_byz dst ∧ voted dst src r v → (sent src r ∧ initial_value src r v)

/- If a value is output, it is the value that was initially proposed by the originator. -/
safety [output_integrity]
  ∀ (src dst : address) (r : round) (v : value),
     ¬ is_byz src ∧ ¬ is_byz dst ∧ output dst src r v → (sent src r ∧ initial_value src r v)

/- Also known as "output uniqueness". -/
safety [agreement]
  ∀ (src dst₁ dst₂ : address) (r : round) (v₁ v₂ : value),
    ¬ is_byz dst₁ ∧ is_byz dst₂ ∧ output dst₁ src r v₁ ∧ output dst₂ src r v₂ → v₁ = v₂

#gen_spec ReliableBroadcast

-- set_option trace.sauto.query true
set_option trace.sauto.result true
-- set_option trace.sauto true

prove_inv_init by { simp_all [initSimp, invSimp] }

prove_inv_safe by { simp_all [invSimp, safeSimp] }

set_option maxHeartbeats 1000000
prove_inv_inductive by {
  intro hnext hinv
  sts_induction <;> sdestruct_all <;> try solve_clause
  {
    simplify_all
    sdestruct_hyps
    -- sauto_all?
    sorry
  }
  {
    simplify_all
    sdestruct_hyps
    -- sauto_all?
    sorry
  }
  {
    simplify_all
    sdestruct_hyps
    -- sauto_all?
    sorry
  }
}


sat trace [initial_state] {} by { bmc_sat }

unsat trace [cannot_echo_without_init] {
  echo
} by { bmc }

sat trace [can_echo] {
  start_round
  echo
} by { bmc_sat }

sat trace [can_vote] {
  start_round
  echo
  echo
  echo
  vote
} by { bmc_sat }

sat trace [succesful_delivery] {
  start_round
  echo
  echo
  echo
  vote
  vote
  vote
  deliver
} by { bmc_sat }

end ReliableBroadcast
