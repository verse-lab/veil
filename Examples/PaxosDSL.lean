import LeanSts.State
import LeanSts.TransitionSystem
import LeanSts.Tactics
-- import Mathlib.Tactic
import LeanSts.DSL

-- Based on: https://github.com/dranov/protocol-specs/blob/main/Paxos/paxos_epr.ivy
-- See also: https://github.com/aman-goel/ivybench/blob/master/paxos/ivy/Paxos.ivy
-- See also: https://github.com/nano-o/ivy-proofs/blob/master/paxos/paxos.ivy
-- See also: https://github.com/aman-goel/ivybench/blob/master/paxos/ivy/oopsla17_paxos.ivy

section PaxosFOL
class TotalOrder (t : Type) :=
  -- relation: total order
  le (x y : t) : Bool
  none : t
  -- axioms
  le_refl       (x : t) : le x x
  le_trans  (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total    (x y : t) : le x y ∨ le y x

class Quorum (node : Type) (quorum : outParam Type):=
  -- relation
  member (a : node) (q : quorum) : Bool
  -- axioms
  quorum_intersection :
    ∀ (q1 q2 : quorum), ∃ (a : node), member a q1 ∧ member a q2

type node
instantiate DecidableEq node
type value
instantiate DecidableEq value
type quorum
instantiate DecidableEq quorum
instantiate Quorum node quorum
type round
instantiate DecidableEq round
instantiate TotalOrder round

-- variable {node : Type} [DecidableEq node]
-- variable {value : Type} [DecidableEq value]
-- variable {quorum : Type} [DecidableEq quorum] [Quorum node quorum]
-- variable {round : Type} [DecidableEq round] [TotalOrder round]

  -- Phase 1(a): a proposer selects a proposal number (ballot) `r` and sends a
  -- _prepare_ request (`msg_1a`) with number `r` to a majority of acceptors
relation one_a : round -> Bool
  -- Phase 1(b) : if an acceptor `n` receives a _prepare_ request with number `r`
  -- greater than that of ANY _prepare_ request to which it has already responded
  -- then it responds to the request with a promise not to accept any more
  -- proposals numbered less than `r` AND with the highest-numbered proposal (if
  -- any) that it has accepted (`max_round` and `max_val`) i.e. `msg_1b`
  -- equivalent to `one_b_max_vote` in the original Ivy spec
relation one_b_max_vote : node -> round -> round -> value -> Bool
  -- Phase 2(a): if the proposer receives a response to its _prepare_ requests
  -- (numbered `r`) from a majority/quorum of acceptors, then it sends an _accept_
  -- request to each of those acceptors for a proposal numbered `r` with a
  -- value `v`, where `v` is the value of the highest-numbered proposal among
  -- the responses, or is any value if trhe responses reported no proposals
relation proposal : round -> value -> Bool
  -- Phase 2(b): if an acceptor `n` receives an _accept_ request for a proposal
  -- numbered `r`, it accepts the proposal UNLESS it has already responded
  -- to a _prepare_ request having a number greater than `r`
relation vote : node -> round -> value -> Bool
  -- Got 2(b) from a quorum
relation decision : node -> round -> value -> Bool
  -- (ghost) relation left_rnd(N:node, R:round) # := exists R2, RMAX, V. ~le(R2,R) & one_b_max_vote(N,R,RMAX,V)
relation leftRound : node -> round -> Bool
  -- (ghost) relation one_b(N:node, R:round) # := exists RMAX, V. one_b_max_vote(N,R,RMAX,V)
relation one_b : node -> round -> Bool

#gen_state

/-- Find the maximal vote in a round less than `r` made by node `n` -/
@[sts] def maximalVote (vote : node -> round -> value -> Bool) (n : node) (r : round) (maxr : round) (maxv : value) : Prop :=
  (maxr = TotalOrder.none ∧
    (∀ (MAXR : round) (V : value), ¬ (¬ TotalOrder.le r MAXR ∧ vote n MAXR V))) ∨
  (maxr ≠ TotalOrder.none ∧ ¬ TotalOrder.le r maxr ∧ vote n maxr maxv ∧
    (∀ (MAXR : round) (V : value), (¬ TotalOrder.le r MAXR ∧ vote n MAXR V) → TotalOrder.le MAXR maxr))

/-- Quorum `q` shows `(r, v)` is safe. -/
abbrev showsSafeAt
  (one_b : node -> round -> Bool)
  (one_b_max_vote : node -> round -> round -> value -> Bool)
  (q : quorum) (r : round) (v : value):  Prop :=
  -- a majority of acceptors have joined round `r` (L85 in `paxos_fol.ivy`)
  (∀ (N : node), Quorum.member N q → one_b N r) ∧
  (∃ (maxr : round),
    -- and `(r, v)` is maximal in the quorum
    ((maxr = TotalOrder.none ∧
      (∀ (N : node) (MAXR : round) (V : value),
        ¬ (Quorum.member N q ∧ one_b_max_vote N r MAXR V ∧ MAXR ≠ TotalOrder.none))) ∨
    (maxr ≠ TotalOrder.none ∧
      (∃ (N : node), Quorum.member N q ∧ one_b_max_vote N r maxr v) ∧
      (∀ (N : node) (MAXR : round) (V : value),
        (Quorum.member N q ∧ one_b_max_vote N r MAXR V ∧ MAXR ≠ TotalOrder.none) → TotalOrder.le MAXR maxr)
  )))

abbrev isSafeAt
  (one_b : node -> round -> Bool)
  (one_b_max_vote : node -> round -> round -> value -> Bool)
  (r : round) (v : value) : Prop :=
  ∃ (q : quorum), showsSafeAt _ _ _ _ one_b one_b_max_vote  q r v

abbrev chosenAt (vote : node -> round -> value -> Bool) (r : round) (v : value) : Prop :=
  ∃ (q : quorum), ∀ (n : node), Quorum.member n q → vote n r v

after_init {
  one_a _                := false;
  one_b_max_vote _ _ _ _ := false;
  proposal _ _           := false;
  vote _ _ _             := false;
  decision _ _ _         := false;
  one_b _ _              := false;
  leftRound _ _          := false
}

-- a proposer selects a round and sends a message asking nodes to join the round
action phase_1a (r : round) = {
  require r != TotalOrder.none;
  one_a r := true
}


-- "join round" = receive 1a and answer with 1b
action phase_1b (n : node) (r : round) (max_round : round) (max_val : value) = {
  require r ≠ TotalOrder.none;
  require one_a r;
  require ¬ leftRound n r;
  require maximalVote _ _ _ vote n r max_round max_val;
  -- maximalVote n r max_round max_val;
  one_b_max_vote n r max_round max_val := true;
  one_b n r := true;
  leftRound n R := leftRound n R ∨ (¬ TotalOrder.le r R)
  -- leftRound := λ N R  => st.leftRound N R ∨ (N = n ∧ ¬ TotalOrder.le r R)
}

-- "propose" = receive a quorum of 1b's and send a 2a (proposal)
action phase_2a (r : round) (v : value) = {
  require r ≠ TotalOrder.none;
  require ¬ proposal r V;
  require isSafeAt _ _ _ _ one_b one_b_max_vote r v;
  proposal r v := true
}

-- "cast vote" = receive a 2a and send 2b
action phase_2b (n : node) (r : round) (v : value) = {
  require r ≠ TotalOrder.none;
  require ¬ leftRound n r;
  require proposal r v;
  vote n r v := true
}

-- "decide" = receive a quorum of 2b's
action decision_ (n : node) (r : round) (v : value) = {
  require r ≠ TotalOrder.none;
  require chosenAt _ _ _ _ vote r v;
  decision n r v := true
}

safety ∀ (n1 n2 : node) (r1 r2 : round) (v1 v2 : value),
  (decision n1 r1 v1 ∧ decision n2 r2 v2) → r1 = r2 ∧ v1 = v2

invariant ∀ (r : round) (v1 v2 : value), proposal r v1 ∧ proposal r v2 → v1 = v2

invariant ∀ (n : node) (r : round) (v : value), vote n r v → proposal r v

invariant  ∀ (r : round) (v : value),
    (∃ (n : node), decision n r v) →
    (∃ (q : quorum), ∀ (n : node), Quorum.member n q → vote n r v)

-- Properties of `one_b_max_vote`
invariant ∀ (n : node) (r1 r2 : round) (v1 v2 : value),
  (one_b_max_vote n r1 TotalOrder.none v1 ∧ ¬ TotalOrder.le r2 r1) → ¬ vote n r1 v2

invariant ∀ (n : node) (r rmax : round) (v : value),
  (one_b_max_vote n r rmax v ∧ rmax ≠ TotalOrder.none) →
    (¬ TotalOrder.le r rmax ∧ vote n rmax v)

invariant ∀ (n : node) (r rmax rother : round) (v vother : value),
  (one_b_max_vote n r rmax v ∧ rmax ≠ TotalOrder.none ∧
    ¬ TotalOrder.le r rother ∧ ¬ TotalOrder.le rother rmax) →
    ¬ vote n rother vother

-- Properties of `none`

invariant ∀ (n : node) (r : round) (v : value), ¬ vote n TotalOrder.none v


-- Properties of choosable and proposal

invariant  ∀ (r1 r2 : round) (v1 v2 : value) (q : quorum),
  (¬ TotalOrder.le r2 r1 ∧ proposal r2 v2  ∧ v1 ≠ v2) →
  (∃ (n : node) (r3 rmax : round) (v : value),
    Quorum.member n q ∧ ¬ TotalOrder.le r3 r1 ∧
    one_b_max_vote n r3 rmax v ∧
    ¬ vote n r1 v1)


-- Properties of one_b, left_rnd
-- #conjecture one_b_max_vote(N,R,RMAX,V) -> one_b(N,R)
-- conjecture one_b(N,R2) & ~le(R2,R1) -> left_rnd(N,R1)

invariant ∀ (n : node) (r1 r2 : round),
  one_b n r2 ∧ ¬ TotalOrder.le r2 r1 → leftRound n r1

-- #check Inv

#gen_spec

prove_safety_init by {
  sdestruct st
  simp [actSimp]
  duper
}

prove_inv_init by {
  simp_all [actSimp]
}


set_option maxHeartbeats 2000000

set_option auto.smt true
set_option auto.smt.trust true
-- set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
-- set_option trace.auto.smt.stderr true
-- set_option trace.auto.smt.unsatCore true

-- FIXME: the Lean Infoview has massive performance problems
-- when we do the destruction here; it simply becomes unusable
prove_inv_inductive by {
  intro hnext hinv
  sts_induction <;> (sdestruct) <;> repeat
  sorry
}

end PaxosFOL
