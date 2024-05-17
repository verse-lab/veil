import LeanSts.State
import LeanSts.TransitionSystem
import LeanSts.Tactic
import LeanSts.DSL
import Mathlib.Tactic

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

variable {node : Type} [DecidableEq node]
variable {value : Type} [DecidableEq value]
variable {quorum : Type} [DecidableEq quorum] [Quorum node quorum]
variable {round : Type} [DecidableEq round] [TotalOrder round]

structure Structure :=
  -- Phase 1(a): a proposer selects a proposal number (ballot) `r` and sends a
  -- _prepare_ request (`msg_1a`) with number `r` to a majority of acceptors
  one_a (r : round) : Bool

  -- Phase 1(b) : if an acceptor `n` receives a _prepare_ request with number `r`
  -- greater than that of ANY _prepare_ request to which it has already responded
  -- then it responds to the request with a promise not to accept any more
  -- proposals numbered less than `r` AND with the highest-numbered proposal (if
  -- any) that it has accepted (`max_round` and `max_val`) i.e. `msg_1b`
  -- equivalent to `one_b_max_vote` in the original Ivy spec
  one_b_max_vote (n : node) (r : round) (max_round : round) (max_val : value) : Bool

  -- (ghost) relation one_b(N:node, R:round) # := exists RMAX, V. one_b_max_vote(N,R,RMAX,V)
  -- def one_b (st : @Structure node value round) (n : node) (r : round) : Prop :=
  --   ∃ (rmax : round) (v : value), st.one_b_max_vote n r rmax v
  one_b (n : node) (r : round) : Bool

  -- (ghost) relation left_rnd(N:node, R:round) # := exists R2, RMAX, V. ~le(R2,R) & one_b_max_vote(N,R,RMAX,V)
  -- def leftRound (st : @Structure node value round) (n : node) (r : round) : Prop :=
  -- ∃ (r2 : round) (rmax : round) (v : value),
  --   ¬ TotalOrder.le r2 r ∧ st.one_b_max_vote n r rmax v
  leftRound (n : node) (r : round) : Bool

  -- Phase 2(a): if the proposer receives a response to its _prepare_ requests
  -- (numbered `r`) from a majority/quorum of acceptors, then it sends an _accept_
  -- request to each of those acceptors for a proposal numbered `r` with a
  -- value `v`, where `v` is the value of the highest-numbered proposal among
  -- the responses, or is any value if trhe responses reported no proposals
  proposal (r : round) (v : value) : Bool

  -- Phase 2(b): if an acceptor `n` receives an _accept_ request for a proposal
  -- numbered `r`, it accepts the proposal UNLESS it has already responded
  -- to a _prepare_ request having a number greater than `r`
  vote (n : node) (r : round) (v : value) : Bool

  -- Got 2(b) from a quorum
  decision (n : node) (r : round) (v : value) : Bool

/-- Find the maximal vote in a round less than `r` made by node `n` -/
@[actSimp] def maximalVote (st : @Structure node value round) (n : node) (r : round) (maxr : round) (maxv : value) : Prop :=
  (maxr = TotalOrder.none ∧
    (∀ (MAXR : round) (V : value), ¬ (¬ TotalOrder.le r MAXR ∧ st.vote n MAXR V))) ∨
  (maxr ≠ TotalOrder.none ∧ ¬ TotalOrder.le r maxr ∧ st.vote n maxr maxv ∧
    (∀ (MAXR : round) (V : value), (¬ TotalOrder.le r MAXR ∧ st.vote n MAXR V) → TotalOrder.le MAXR maxr))

/-- Quorum `q` shows `(r, v)` is safe. -/
@[actSimp] def showsSafeAt (st : @Structure node value round) (q : quorum) (r : round) (v : value): Prop :=
  -- a majority of acceptors have joined round `r` (L85 in `paxos_fol.ivy`)
  (∀ (N : node), Quorum.member N q → st.one_b N r) ∧
  (∃ (maxr : round),
    -- and `(r, v)` is maximal in the quorum
    ((maxr = TotalOrder.none ∧
      (∀ (N : node) (MAXR : round) (V : value),
        ¬ (Quorum.member N q ∧ st.one_b_max_vote N r MAXR V ∧ MAXR ≠ TotalOrder.none))) ∨
    (maxr ≠ TotalOrder.none ∧
      (∃ (N : node), Quorum.member N q ∧ st.one_b_max_vote N r maxr v) ∧
      (∀ (N : node) (MAXR : round) (V : value),
        (Quorum.member N q ∧ st.one_b_max_vote N r MAXR V ∧ MAXR ≠ TotalOrder.none) → TotalOrder.le MAXR maxr)
  )))

@[actSimp] def isSafeAt (st : @Structure node value round) (r : round) (v : value) : Prop :=
  ∃ (q : quorum), showsSafeAt st q r v

@[actSimp] def chosenAt (st : @Structure node value round) (r : round) (v : value) : Prop :=
  ∃ (q : quorum), ∀ (n : node), Quorum.member n q → st.vote n r v

@[actSimp] def initialState? (st : @Structure node value round) : Prop :=
  (∀ (r : round), ¬ st.one_a r) ∧
  (∀ (n : node) (r1 r2 : round) (v : value), ¬ st.one_b_max_vote n r1 r2 v) ∧
  (∀ (n : node) (r : round), ¬ st.one_b n r) ∧
  (∀ (n : node) (r : round), ¬ st.leftRound n r) ∧
  (∀ (r : round) (v : value), ¬ st.proposal r v) ∧
  (∀ (n : node) (r : round) (v : value), ¬ st.vote n r v) ∧
  (∀ (n : node) (r : round) (v : value), ¬ st.decision n r v)

-- a proposer selects a round and sends a message asking nodes to join the round
@[actSimp] def phase_1a : RelationalTransitionSystem.action (@Structure node value round) :=
  λ (st st' : @Structure node value round) =>
    ∃ (r : round),
      -- preconditions
      r ≠ TotalOrder.none ∧
      -- update
      st' = { st with one_a := st.one_a[r ↦ true] }

-- "join round" = receive 1a and answer with 1b
@[actSimp] def phase_1b : RelationalTransitionSystem.action (@Structure node value round) :=
  λ (st st' : @Structure node value round) =>
    ∃ (n : node) (r : round) (max_round : round) (max_val : value),
      -- preconditions
      r ≠ TotalOrder.none ∧
      st.one_a r ∧
      ¬ st.leftRound n r ∧
      maximalVote st n r max_round max_val ∧
      -- update
      -- NOTE: `one_b` and `leftRound` are derived relations, which we must update
      st' = { st with one_b_max_vote := st.one_b_max_vote[n, r, max_round, max_val ↦ true],
                      one_b := st.one_b[n, r ↦ true],
                      -- left_rnd(n, R) := left_rnd(n, R) | ~le(r, R)
                      -- TODO: add a helper function in `State.lean` for this kind of thing
                      leftRound := λ N R  => st.leftRound N R ∨ (N = n ∧ ¬ TotalOrder.le r R)
       }

-- "propose" = receive a quorum of 1b's and send a 2a (proposal)
@[actSimp] def phase_2a : RelationalTransitionSystem.action (@Structure node value round) :=
  λ (st st' : @Structure node value round) =>
    ∃ (r : round) (v : value),
      -- preconditions
      r ≠ TotalOrder.none ∧
      (forall (V : value), ¬ st.proposal r V) ∧
      isSafeAt st r v ∧
      -- update
      st' = { st with proposal := st.proposal[r, v ↦ true] }

-- -- "cast vote" = receive a 2a and send 2b
@[actSimp] def phase_2b : RelationalTransitionSystem.action (@Structure node value round) :=
  λ (st st' : @Structure node value round) =>
    ∃ (n : node) (r : round) (v : value),
      -- preconditions
      r ≠ TotalOrder.none ∧
      ¬ st.leftRound n r ∧
      st.proposal r v ∧
      -- update
      st' = { st with vote := st.vote[n, r, v ↦ true] }

-- "decide" = receive a quorum of 2b's
@[actSimp] def decision : RelationalTransitionSystem.action (@Structure node value round) :=
  λ (st st' : @Structure node value round) =>
    ∃ (n : node) (r : round) (v : value),
      -- preconditions
      r ≠ TotalOrder.none ∧
      chosenAt st r v ∧
      -- update
      st' = { st with decision := st.decision[n, r, v ↦ true] }

@[safeSimp, invSimp] def unique_decision (st : @Structure node value round) : Prop :=
  ∀ (n1 n2 : node) (r1 r2 : round) (v1 v2 : value),
    (st.decision n1 r1 v1 ∧ st.decision n2 r2 v2) → r1 = r2 ∧ v1 = v2

def unique_decision_init :
  ∀ (st : @Structure node value round),
    initialState? st → unique_decision st := by
  intro st
  simp only [RelationalTransitionSystem.init, unique_decision, initialState?]
  duper

@[invSimp] def inv_propose_unique (st : @Structure node value round) : Prop :=
  ∀ (r : round) (v1 v2 : value), st.proposal r v1 ∧ st.proposal r v2 → v1 = v2

@[invSimp] def inv_vote_proposed (st : @Structure node value round) : Prop :=
  ∀ (n : node) (r : round) (v : value), st.vote n r v → st.proposal r v

@[invSimp] def inv_decision_quorum_vote (st : @Structure node value round) : Prop :=
  ∀ (r : round) (v : value),
    (∃ (n : node), st.decision n r v) →
    (∃ (q : quorum), ∀ (n : node), Quorum.member n q → st.vote n r v)

-- Properties of `one_b_max_vote`
-- These are commented out in the Ivy file BECAUSE THEY DO NOT HOLD!
-- @[invSimp] def inv_one_b_max_vote1 (st : @Structure node value round) : Prop :=
--   ∀ (n : node) (r1 r2 : round) (v1 v2 : value),
--     (st.one_b_max_vote n r1 TotalOrder.none v1 ∧ ¬ TotalOrder.le r2 r1) → ¬ st.vote n r1 v2

-- @[invSimp] def inv_one_b_max_vote2 (st : @Structure node value round) : Prop :=
--   ∀ (n : node) (r rmax : round) (v : value),
--     (st.one_b_max_vote n r rmax v ∧ rmax ≠ TotalOrder.none) →
--     (¬ TotalOrder.le r rmax ∧ st.vote n rmax v)

-- @[invSimp] def inv_one_b_max_vote3 (st : @Structure node value round) : Prop :=
--   ∀ (n : node) (r rmax rother : round) (v vother : value),
--     (st.one_b_max_vote n r rmax v ∧ rmax ≠ TotalOrder.none ∧
--        ¬ TotalOrder.le r rother ∧ ¬ TotalOrder.le rother rmax) →
--     ¬ st.vote n rother vother

-- Properties of `none`

@[invSimp] def inv_no_vote_at_none (st : @Structure node value round) : Prop :=
  ∀ (n : node) (v : value), ¬ st.vote n TotalOrder.none v

-- Properties of choosable and proposal
@[invSimp] def inv_choose_propose (st : @Structure node value round) : Prop :=
  ∀ (r1 r2 : round) (v1 v2 : value) (q : quorum),
    (¬ TotalOrder.le r2 r1 ∧ st.proposal r2 v2  ∧ v1 ≠ v2) →
    (∃ (n : node) (r3 rmax : round) (v : value),
      Quorum.member n q ∧ ¬ TotalOrder.le r3 r1 ∧
      st.one_b_max_vote n r3 rmax v ∧
      ¬ st.vote n r1 v1)

-- Properties of one_b, left_rnd
-- #conjecture one_b_max_vote(N,R,RMAX,V) -> one_b(N,R)
-- conjecture one_b(N,R2) & ~le(R2,R1) -> left_rnd(N,R1)

@[invSimp] def one_b_left_round (st : @Structure node value round) : Prop :=
  ∀ (n : node) (r1 r2 : round),
    st.one_b n r2 ∧ ¬ TotalOrder.le r2 r1 → st.leftRound n r1

@[invSimp] def inv' (st : @Structure node value round) : Prop :=
  unique_decision st ∧
  inv_propose_unique st ∧
  inv_vote_proposed st ∧
  inv_decision_quorum_vote st ∧
  inv_no_vote_at_none st ∧
  inv_choose_propose st ∧
  one_b_left_round st

instance System : RelationalTransitionSystem (@Structure node value round)
  where
  init := λ st => initialState? st
  -- TLA-style
  next := λ st st' =>
    phase_1a st st' ∨
    phase_1b st st' ∨
    phase_2a st st' ∨
    phase_2b st st' ∨
    decision st st'
  safe := unique_decision
  inv := inv'

def inv_init :
  ∀ (st : @Structure node value round), initialState? st → inv' st := by
    simp_all only [invSimp, actSimp,
    Bool.not_eq_true, and_self, IsEmpty.forall_iff, implies_true, exists_false,
    imp_false, false_and, not_false_eq_true, ne_eq, and_false, and_true,
    exists_and_left, exists_and_right, and_imp]

set_option maxHeartbeats 2000000

set_option auto.smt true
set_option auto.smt.trust true
-- set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
-- set_option trace.auto.smt.stderr true
-- set_option trace.auto.smt.unsatCore true

-- theorem inv_automated :
--   @invInductive (@Structure node value round) System := by
--   intro st st' hnext hinv
--   sts_induction <;> sdestruct <;> try solve_clause
--   { sorry }
--   { sorry }
--   { sorry }
--   { sorry }

-- The first `sorry`'ed goal from above
theorem extracted_1 (st st' : @Structure node value round)
  (hinv : RelationalTransitionSystem.inv st) (hnext : phase_1b st st') :
  inv_choose_propose st' := by
  -- sdestruct st;
  -- sdestruct st';
  -- simp only [actSimp, invSimp, Structure.mk.injEq] at *
  -- auto[Quorum.quorum_intersection, TotalOrder.le_refl, TotalOrder.le_total, TotalOrder.le_antisymm,
      --  TotalOrder.le_trans, hinv, hnext]
  sorry

theorem extracted_2 (st st' : @Structure node value round)
  (hinv : RelationalTransitionSystem.inv st) (hnext : phase_2a st st') :
  inv_choose_propose st' := sorry

theorem extracted_3 (st st' : @Structure node value round)
  (hinv : RelationalTransitionSystem.inv st) (hnext : phase_2b st st') :
  inv_choose_propose st' := sorry

theorem extracted_4 (st st' : @Structure node value round)
  (hinv : RelationalTransitionSystem.inv st) (hnext : decision st st') :
  unique_decision st' := sorry

end PaxosFOL
