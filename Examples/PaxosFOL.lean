import LeanSts.State
import LeanSts.TransitionSystem
import LeanSts.Tactics
import Mathlib.Tactic

-- Based on: https://github.com/aman-goel/ivybench/blob/master/paxos/ivy/oopsla17_paxos.ivy
-- See also: https://github.com/aman-goel/ivybench/blob/master/paxos/ivy/Paxos.ivy
-- See also: https://github.com/nano-o/ivy-proofs/blob/master/paxos/paxos.ivy

section PaxosFOL
class BoundedTotalOrder (t : Type) :=
  -- relation: total order
  le (x y : t) : Bool
  negative_one : t
  maximum : t
  -- axioms
  le_refl       (x : t) : le x x
  le_trans  (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total    (x y : t) : le x y ∨ le y x
  le_neg_one  (x : t)   : le negative_one x
  le_max      (x : t)   : le x maximum

class Quorum (node : Type) (quorum : outParam Type):=
  -- relation
  member (a : node) (q : quorum) : Bool
  -- axioms
  quorum_intersection :
    ∀ (q1 q2 : quorum), ∃ (a : node), member a q1 ∧ member a q2

variable {value : Type} [DecidableEq value]
variable {node : Type} [DecidableEq node]
variable {round : Type} [DecidableEq round] [BoundedTotalOrder round]
variable {quorum : Type} [DecidableEq quorum] [Quorum node quorum]

structure Structure :=
  -- Phase 1(a): a proposer selects a proposal number (ballot) `r` and sends a
  -- _prepare_ request (`msg_1a`) with number `r` to a majority of acceptors
  msg_1a (r : round) : Bool

  -- Phase 1(b) : if an acceptor `a` receives a _prepare_ request with number `r`
  -- greater than that of ANY _prepare_ request to which it has already responded
  -- then it responds to the request with a promise not to accept any more
  -- proposals numbered less than `r` AND with the highest-numbered proposal (if
  -- any) that it has accepted (`max_round` and `max_val`) i.e. `msg_1b`
  -- equivalent to `one_b_max_vote` in the original Ivy spec
  msg_1b (a : node) (r : round) (max_round : round) (max_val : value) : Bool

  -- Phase 2(a): if the proposer receives a response to its _prepare_ requests
  -- (numbered `r`) from a majority/quorum of acceptors, then it sends an _accept_
  -- request to each of those acceptors for a proposal numbered `r` with a
  -- value `v`, where `v` is the value of the highest-numbered proposal among
  -- the responses, or is any value if trhe responses reported no proposals
  msg_2a (r : round) (v : value) : Bool -- also called "proposal"

  -- Phase 2(b): if an acceptor `a` receives an _accept_ request for a proposal
  -- numbered `r`, it accepts the proposal UNLESS it has already responded
  -- to a _prepare_ request having a number greater than `r`
  msg_2b (a : node) (r : round) (v : value) : Bool -- also called "vote"

  -- Got 2(b) from a quorum
  decision (a : node) (r : round) (v : value) : Bool


-- equivalent to `one_b` in the original Ivy spec
@[simp] def exists1B (st : @Structure value node round) (n : node) (r : round) : Prop :=
  ∃ (rmax : round) (v : value), st.msg_1b n r rmax v

-- (ghost) relation left_rnd(N:node, R:round) # := exists R2, RMAX, V. ~le(R2,R) & one_b_max_vote(N,R,RMAX,V)
@[simp] def leftRound (st : @Structure value node round) (n : node) (r : round) : Prop :=
  ∃ (r2 : round) (rmax : round) (v : value),
    ¬ BoundedTotalOrder.le r2 r ∧
    st.msg_1b n r rmax v

-- find the maximal vote in a round less than r
-- assume ((maxr = negone & forall MAXR:round,V:value. ~(~le(r,MAXR) & vote(n,MAXR,V))) |
--         (maxr ~= negone & ~le(r,maxr) & vote(n,maxr,v) &
--         (forall MAXR:round,V:value. (~le(r,MAXR) & vote(n,MAXR,V)) -> le(MAXR,maxr))
--         ));
@[simp] def maximalVote (st : @Structure value node round) (n : node) (r : round) (maxr : round) (maxv : value) : Prop :=
  -- uninitialised, i.e. there are no votes at valid round numbers
  (maxr = BoundedTotalOrder.negative_one ∧
    (∀ (MAXR : round) (V : value), ¬ (¬ BoundedTotalOrder.le r MAXR ∧ st.msg_2b n MAXR V))) ∨
  -- (current) r > maxr AND there is a vote for (maxr, maxv) AND
  -- every other vote is at a lower round number than `maxr`
  (maxr ≠ BoundedTotalOrder.negative_one ∧
    ¬ BoundedTotalOrder.le r maxr ∧
    st.msg_2b n maxr maxv ∧
    (∀ (MAXR : round) (V : value), (¬ BoundedTotalOrder.le r MAXR ∧ st.msg_2b n MAXR V) → BoundedTotalOrder.le MAXR maxr)
  )

@[simp] def chosenAt (st : @Structure value node round) (r : round) (v : value) : Prop :=
  ∃ (q : quorum), ∀ (n : node), Quorum.member n q → st.decision n r v

-- quorum that shows (rin, vin) is safe
@[simp] def showsSafeAt (st : @Structure value node round) (qin : quorum) (rin : round) (vin : value): Prop :=
  -- a majority of acceptors have joined round `rin`
  (∀ (N : node), Quorum.member N qin → exists1B st N rin) ∧
  -- and either
  (∃ (MAXRIn : round),
    -- nothing has happened; FIXME: why does this exist?
    (MAXRIn = BoundedTotalOrder.negative_one ∧
      (∀ (N : node) (MAXR : round) (V : value),
        ¬ (Quorum.member N qin ∧ ¬ BoundedTotalOrder.le rin MAXR ∧ st.msg_2b N MAXR V))) ∨
    -- OR ∃ node in the quorum that voted for the value at some previous round MAXRIn, AND
    -- MAXRIn is the largest round number in the quorum that voted for the value
    (MAXRIn ≠ BoundedTotalOrder.negative_one ∧
      (∃ (N : node), Quorum.member N qin ∧ ¬ BoundedTotalOrder.le rin MAXRIn ∧ st.msg_2b N MAXRIn vin) ∧
      (∀ (N : node) (MAXR : round) (V : value),
        (Quorum.member N qin ∧ ¬ BoundedTotalOrder.le rin MAXR ∧ st.msg_2b N MAXR V) → BoundedTotalOrder.le MAXR MAXRIn)
    )
  )

@[simp] def isSafeAt (st : @Structure value node round) (r : round) (v : value) : Prop :=
  ∃ (q : quorum), showsSafeAt st q r v

@[simp] def initialState? (st : @Structure value node round) : Prop :=
  (∀ (r : round), ¬ st.msg_1a r) ∧
  (∀ (n : node) (r1 r2 : round) (v : value), ¬ st.msg_1b n r1 r2 v) ∧
  (∀ (r : round) (v : value), ¬ st.msg_2a r v) ∧
  (∀ (n : node) (r : round) (v : value), ¬ st.msg_2b n r v) ∧
  (∀ (n : node) (r : round) (v : value), ¬ st.decision n r v)

-- a proposer selects a round and sends a message asking nodes to join the round
@[simp] def phase_1a : RelationalTransitionSystem.action (@Structure value node round) :=
  λ (st st' : @Structure value node round) =>
    ∃ (r : round),
      -- preconditions
      r ≠ BoundedTotalOrder.negative_one ∧
      -- update
      st' = { st with msg_1a := st.msg_1a[r ↦ true] }

-- "join round" = receive 1a and answer with 1b
@[simp] def phase_1b : RelationalTransitionSystem.action (@Structure value node round) :=
  λ (st st' : @Structure value node round) =>
    ∃ (n : node) (r : round) (max_round : round) (max_val : value),
      -- preconditions
      r ≠ BoundedTotalOrder.negative_one ∧
      st.msg_1a r ∧
      ¬ leftRound st n r ∧
      maximalVote st n r max_round max_val ∧ -- find the maximal vote in a round less than `r`
      -- update
      st' = { st with msg_1b := st.msg_1b[n, r, max_round, max_val ↦ true] }
      -- NOTE: one_b and left_rnd are ghost relations which we don't update

-- "propose" = receive a quorum of 1b's and send a 2a (proposal)
@[simp] def phase_2a : RelationalTransitionSystem.action (@Structure value node round) :=
  λ (st st' : @Structure value node round) =>
    ∃ (r : round) (v : value),
      -- preconditions
      r ≠ BoundedTotalOrder.negative_one ∧
      (forall (V : value), ¬ st.msg_2a r V) ∧
      isSafeAt st r v ∧
      -- update
      st' = { st with msg_2a := st.msg_2a[r, v ↦ true] }

-- "cast vote" = receive a 2a and send 2b
@[simp] def phase_2b : RelationalTransitionSystem.action (@Structure value node round) :=
  λ (st st' : @Structure value node round) =>
    ∃ (n : node) (r : round) (v : value),
      -- preconditions
      r ≠ BoundedTotalOrder.negative_one ∧
      ¬ leftRound st n r ∧
      st.msg_2a r v ∧
      -- update
      st' = { st with msg_2b := st.msg_2b[n, r, v ↦ true] }

-- "decide" = receive a quorum of 2b's
@[simp] def decision : RelationalTransitionSystem.action (@Structure value node round) :=
  λ (st st' : @Structure value node round) =>
    ∃ (n : node) (r : round) (v : value),
      -- preconditions
      r ≠ BoundedTotalOrder.negative_one ∧
      chosenAt st r v ∧
      -- update
      st' = { st with decision := st.decision[n, r, v ↦ true] }

instance System : RelationalTransitionSystem (@Structure value node round)
  where
  init := λ st => initialState? st
  -- TLA-style
  next := λ st st' =>
    phase_1a st st' ∨
    phase_1b st st' ∨
    phase_2a st st' ∨
    phase_2b st st' ∨
    decision st st'

@[simp] def safety (st : @Structure value node round) : Prop :=
  ∀ (n1 n2 : node) (r1 r2 : round) (v1 v2 : value),
    (st.decision n1 r1 v1 ∧ st.decision n2 r2 v2) → r1 = r2 ∧ v1 = v2

def safety_init :
  ∀ (st : @Structure value node round),
    initialState? st → safety st := by
  intro st
  simp only [RelationalTransitionSystem.init, safety, System, initialState?]
  duper

@[simp] def inv_propose_same (st : @Structure value node round) : Prop :=
  ∀ (r : round) (v1 v2 : value), st.msg_2a r v1 ∧ st.msg_2a r v2 → v1 = v2

@[simp] def inv_vote_proposed (st : @Structure value node round) : Prop :=
  ∀ (n : node) (r : round) (v : value), st.msg_2b n r v → st.msg_2a r v

@[simp] def inv_decision_quorum_vote (st : @Structure value node round) : Prop :=
  ∀ (r : round) (v : value),
    (∃ (n : node), st.decision n r v) →
    (∃ (q : quorum), ∀ (n : node), Quorum.member n q → st.msg_2b n r v)

@[simp] def inv_no_votes_at_negone (st : @Structure value node round) : Prop :=
  ∀ (n : node) (v : value), ¬ st.msg_2b n BoundedTotalOrder.negative_one v

@[simp] def inv_one_b_left_rnd (st : @Structure value node round) : Prop :=
  ∀ (n : node) (r1 r2 : round),
    (exists1B st n r2 ∧ ¬ BoundedTotalOrder.le r2 r1) → leftRound st n r1

@[simp] def inv_vote_negone (st : @Structure value node round) : Prop :=
  ∀ (n : node) (r1 r2 : round) (v1 v2 : value),
    (st.msg_1b n r2 BoundedTotalOrder.negative_one v1 ∧ ¬ BoundedTotalOrder.le r2 r1) →
    ¬ st.msg_2b n r1 v2

@[simp] def inv_vote_max_rnd_negone (st : @Structure value node round) : Prop :=
  ∀ (n : node) (r1 r2 : round) (v1 v2 : value),
    (st.msg_1b n r2 r1 v1 ∧ ¬ BoundedTotalOrder.le r1 r2) →
    ¬ st.msg_2b n r1 v2

@[simp] def inv_vote_max_rnd (st : @Structure value node round) : Prop :=
  ∀ (n : node) (r rmax : round) (v : value),
    (st.msg_1b n r rmax v ∧ rmax ≠ BoundedTotalOrder.negative_one) →
    (¬ BoundedTotalOrder.le r rmax ∧ st.msg_2b n rmax v)

@[simp] def inv_no_conflicting_votes (st : @Structure value node round) : Prop :=
  ∀ (n : node) (r rmax rother : round) (v vother: value),
    (st.msg_1b n r rmax v ∧
       ¬ BoundedTotalOrder.le r rother ∧ ¬ BoundedTotalOrder.le rother rmax) →
    ¬ st.msg_2b n rother vother

@[simp] def inv_accept_no_diff_vote (st : @Structure value node round) : Prop :=
  ∀ (r1 r2 : round) (v1 v2 : value) (q : quorum),
    (¬ BoundedTotalOrder.le r2 r1 ∧ st.msg_2a r2 v2 ∧ v1 ≠ v2) →
    (∃ (n : node), Quorum.member n q ∧ leftRound st n r1 ∧ ¬ st.msg_2b n r1 v1)

@[simp] def inv (st : @Structure value node round) : Prop :=
  safety st ∧
  inv_propose_same st ∧
  inv_vote_proposed st ∧
  inv_decision_quorum_vote st ∧
  inv_no_votes_at_negone st ∧
  inv_one_b_left_rnd st ∧
  inv_vote_negone st ∧
  inv_vote_max_rnd_negone st ∧
  inv_vote_max_rnd st ∧
  inv_no_conflicting_votes st ∧
  inv_accept_no_diff_vote st

set_option maxHeartbeats 2000000

set_option auto.smt true
set_option auto.smt.trust true
-- set_option trace.auto.smt.printCommands true
-- set_option trace.auto.smt.result true
-- set_option trace.auto.smt.stderr true
-- set_option trace.auto.smt.unsatCore true

def inv_init :
  ∀ (st : @Structure value node round), initialState? st → inv st := by simp_all only [initialState?,
    Bool.not_eq_true, inv, safety, and_self, IsEmpty.forall_iff, implies_true, inv_propose_same,
    inv_vote_proposed, inv_decision_quorum_vote, exists_false, imp_false, inv_no_votes_at_negone,
    not_false_eq_true, inv_one_b_left_rnd, exists1B, false_and, leftRound, and_false,
    inv_vote_negone, inv_vote_max_rnd_negone, inv_vote_max_rnd, ne_eq, inv_no_conflicting_votes,
    inv_accept_no_diff_vote, and_true, exists_and_right, and_imp]


-- FIXME: the Lean Infoview has massive performance problems
-- when we do the destruction here; it simply becomes unusable
theorem inv_inductive :
  ∀ (st st' : @Structure value node round), System.next st st' → inv st → inv st' := by
  intro st st' hnext hinv
  sts_induction <;> (dsimp only [inv]; sdestruct) <;> repeat
  -- TODO: make this into a tactic
  (
    sdestruct st st';
    simp at hinv htr ⊢;
    try unfold updateFn at htr; try unfold updateFn2 at htr;
    try unfold updateFn3 at htr; try unfold updateFn4 at htr;
    -- duper [hinv, htr]
    auto
  )


end PaxosFOL
