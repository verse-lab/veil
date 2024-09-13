import LeanSts.DSL

section ReliableBroadcast

/-
  Reliable Broadcast is a Byzantine fault-tolerant broadcast protocol
  that ensures that all honest nodes deliver the same message, as long
  as the `originator` (the node that initiated the broadcast) is honest.

  It proceeds in three phases:
    - an initial phase, where the originator broadcasts `initial_msg`
    - an echo phase, where nodes broadcast an `echo` of the value they
      received
    - a vote phase, where nodes broadcast a `vote` for the value they've
      seen echoed by a `2f + 1` quorum of nodes; alternatively, a node
      votes if it sees `f + 1` votes for the same value

  The `deliver` action is triggered when a node sees `2f + 1` votes for
  the same value, and outputs that value.

  The protocol has three separate quorum thresholds:
    - `echo4vote` -- `2f + 1` nodes that have echoed the same value to vote
    - `vote4vote` -- `f + 1` nodes that have voted for the same value to vote
    - `vote4output` -- `2f + 1` nodes that have voted for the same value to output
-/

class NodeSet (node : Type) (is_byz : outParam (node → Prop)) (nset : outParam Type) :=
  member (a : node) (s : nset) : Prop
  is_empty (s : nset) : Prop

  greater_than_third (s : nset) : Prop  -- f + 1 nodes
  supermajority (s : nset) : Prop       -- 2f + 1 nodes

  supermajorities_intersect_in_honest :
    ∀ (s1 s2 : nset), ∃ (a : node), member a s1 ∧ member a s2 ∧ ¬ is_byz a
  greater_than_third_one_honest :
    ∀ (s : nset), greater_than_third s → ∃ (a : node), member a s ∧ ¬ is_byz a
  supermajority_greater_than_third :
    ∀ (s : nset), supermajority s → greater_than_third s
  greater_than_third_nonempty :
    ∀ (s : nset), greater_than_third s → ¬ is_empty s

type nodeset
type address
type round
type value

-- FIXME: immutable relation?
variable (is_byz : address → Prop)

instantiate nset : NodeSet address is_byz nodeset
open NodeSet

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

transition byz = fun st st' =>
  (∀ (src dst : address) (r : round) (v : value),
    (¬ is_byz src ∧ (st.initial_msg src dst r v ↔ st'.initial_msg src dst r v)) ∨
    (is_byz src ∧ (st.initial_msg src dst r v → st'.initial_msg src dst r v))) ∧
  (∀ (src dst originator : address) (r : round) (v : value),
    (¬ is_byz src ∧ (st.echo_msg src dst originator r v ↔ st'.echo_msg src dst originator r v)) ∨
    (is_byz src ∧ (st.echo_msg src dst originator r v → st'.echo_msg src dst originator r v))) ∧
  (∀ (src dst originator : address) (r : round) (v : value),
    (¬ is_byz src ∧ (st.vote_msg src dst originator r v ↔ st'.vote_msg src dst originator r v)) ∨
    (is_byz src ∧ (st.vote_msg src dst originator r v → st'.vote_msg src dst originator r v)))
  -- unchanged
  ∧ (st.sent = st'.sent)
  ∧ (st.echoed = st'.echoed)
  ∧ (st.voted = st'.voted)
  ∧ (st.output = st'.output)


action start_round (n : address) (r : round) (v : value) = {
  require ¬ sent n r;
  initial_msg n N r v := True;
  sent n r := True
}

action echo (n : address) (originator : address) (r : round) (v : value) = {
  require initial_msg originator n r v;
  require ¬ echoed n originator r V;
  echoed n originator r v := True;
  echo_msg n DST originator r v := True
}

action vote (n : address) (originator : address) (r : round) (v : value) = {
  -- received 2f + 1 echo messages OR f + 1 vote messages
  require (∃ (q : nodeset), nset.supermajority q ∧
              ∀ (src : address), nset.member src q → echo_msg src n originator r v) ∨
          (∃ (q : nodeset), nset.greater_than_third q ∧
              ∀ (src : address), nset.member src q → vote_msg src n originator r v);
  require ¬ voted n originator r V;
  voted n originator r v := True;
  vote_msg n DST originator r v := True
}

action deliver (n : address) (originator : address) (r : round) (v : value) = {
  -- received 2f + 1 votes
  require (∃ (q : nodeset), nset.supermajority q ∧
              ∀ (src : address), nset.member src q → vote_msg src n originator r v);
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
    ¬ is_byz dst₁ ∧ ¬ is_byz dst₂ ∧ output dst₁ src r v₁ ∧ output dst₂ src r v₂ → v₁ = v₂

-- These invariants are discovered in the order given, by inspecting the code
-- of the actions one by one.

-- start_round
invariant [sent_iff_initial]
  ∀ (src : address) (r : round),
    ¬ is_byz src → (sent src r ↔ ∃ (v : value), initial_value src r v)

-- echo
invariant [echoed_iff_echo]
  ∀ (n dst originator : address) (r : round) (v : value),
    ¬ is_byz n → (echoed n originator r v ↔ echo_msg n dst originator r v)

invariant [echoed_requires_initial]
  ∀ (n originator : address) (r : round) (v : value),
    ¬ is_byz n → (echoed n originator r v → initial_msg originator n r v)

-- vote
invariant [voted_iff_vote]
  ∀ (n dst originator : address) (r : round) (v : value),
    ¬ is_byz n → (voted n originator r v ↔ vote_msg n dst originator r v)

-- not in the decidable fragment due to edge from `address` to `nodeset`:
invariant [voted_requires_echo_quorum_or_vote_quorum]
  ∀ (n originator : address) (r : round) (v : value),
    ¬ is_byz n → (voted n originator r v →
      (∃ (q : nodeset), nset.supermajority q ∧
        ∀ (src : address), member src q → echo_msg src n originator r v) ∨
      (∃ (q : nodeset), nset.greater_than_third q ∧
        ∀ (src : address), member src q → vote_msg src n originator r v))

-- deliver
-- not in the decidable fragment due to edge from `address` to `nodeset`
invariant [output_requires_vote_quorum]
  ∀ (n originator : address) (r : round) (v : value),
    ¬ is_byz n → (output n originator r v →
      ∃ (q : nodeset), nset.supermajority q ∧
        ∀ (src : address), member src q → vote_msg src n originator r v)

-- these invariants are discovered in the order given, by eliminating CTIs

-- vote_vote_integrity
-- this version is not in the decidable fragment:
-- invariant [sent_iff_initial]
--   ∀ (src : address) (r : round),
--     sent src r ↔ ∃ (dst : address) (v : value), initial_msg src dst r v

-- So instead we use the following:
invariant [initial_value_iff_initial_msg]
  ∀ (src dst : address) (r : round) (v : value),
    ¬ is_byz src → (initial_value src r v ↔ initial_msg src dst r v)

-- deliver_agreement
invariant [honest_non_conflicting_initial_msg]
  ∀ (src dst₁ dst₂ : address) (r : round) (v₁ v₂ : value),
    (¬ is_byz src) → (initial_msg src dst₁ r v₁ ∧ initial_msg src dst₂ r v₂ → v₁ = v₂)

invariant [honest_non_conflicting_echoes]
  ∀ (src originator dst₁ dst₂ : address) (r : round) (v₁ v₂ : value),
    (¬ is_byz src) → (echo_msg src dst₁ originator r v₁ ∧ echo_msg src dst₂ originator r v₂ → v₁ = v₂)

invariant [honest_non_conflicting_votes]
  ∀ (src originator dst₁ dst₂ : address) (r : round) (v₁ v₂ : value),
    (¬ is_byz src) → (vote_msg src dst₁ originator r v₁ ∧ vote_msg src dst₂ originator r v₂ → v₁ = v₂)

set_option maxHeartbeats 10000000
set_option auto.smt.timeout 10 -- seconds
set_option sauto.smt.macrofinder true -- Ivy uses this by default

#gen_spec ReliableBroadcast

#check_invariants

theorem deliver_agreement':
    ∀ (st st' : State nodeset address round value is_byz),
      (ReliableBroadcast nodeset address round value is_byz).inv st →
        (deliver nodeset address round value is_byz) st st' →
          (agreement nodeset address round value is_byz) st' := by
  -- unhygienic intros; solve_clause
  -- this works with CVC5!
  sorry

prove_inv_init by { solve_clause }
prove_inv_safe by { solve_clause }

-- set_option trace.sauto.result true

prove_inv_inductive by {
  intro hnext hinv
  sts_induction <;> sdestruct_goal <;> try already_proven
  {
    sdestruct_hyps
    simplify_all
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

/-
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
-/

end ReliableBroadcast
