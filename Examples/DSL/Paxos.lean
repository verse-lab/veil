import Veil.State
import Veil.TransitionSystem
import Veil.Tactic
import Veil.DSL
import Examples.DSL.Std

-- Based on: https://github.com/dranov/protocol-specs/blob/main/Paxos/paxos_epr.ivy
-- See also: https://github.com/aman-goel/ivybench/blob/master/paxos/ivy/Paxos.ivy
-- See also: https://github.com/nano-o/ivy-proofs/blob/master/paxos/paxos.ivy
-- See also: https://github.com/aman-goel/ivybench/blob/master/paxos/ivy/oopsla17_paxos.ivy

namespace PaxosFOL
open Classical

type node
type value
type quorum
instantiate q : Quorum node quorum
type round
instantiate tot : TotalOrderWithNone round

  -- Phase 1(a): a proposer selects a proposal number (ballot) `r` and sends a
  -- _prepare_ request (`msg_1a`) with number `r` to a majority of acceptors
relation one_a : round -> Prop
  -- Phase 1(b) : if an acceptor `n` receives a _prepare_ request with number `r`
  -- greater than that of ANY _prepare_ request to which it has already responded
  -- then it responds to the request with a promise not to accept any more
  -- proposals numbered less than `r` AND with the highest-numbered proposal (if
  -- any) that it has accepted (`max_round` and `max_val`) i.e. `msg_1b`
  -- equivalent to `one_b_max_vote` in the original Ivy spec
relation one_b_max_vote : node -> round -> round -> value -> Prop
  -- Phase 2(a): if the proposer receives a response to its _prepare_ requests
  -- (numbered `r`) from a majority/quorum of acceptors, then it sends an _accept_
  -- request to each of those acceptors for a proposal numbered `r` with a
  -- value `v`, where `v` is the value of the highest-numbered proposal among
  -- the responses, or is any value if trhe responses reported no proposals
relation proposal : round -> value -> Prop
  -- Phase 2(b): if an acceptor `n` receives an _accept_ request for a proposal
  -- numbered `r`, it accepts the proposal UNLESS it has already responded
  -- to a _prepare_ request having a number greater than `r`
relation vote : node -> round -> value -> Prop
  -- Got 2(b) from a quorum
relation decision : node -> round -> value -> Prop
  -- (ghost) relation left_rnd(N:node, R:round) # := exists R2, RMAX, V. ~le(R2,R) & one_b_max_vote(N,R,RMAX,V)
relation leftRound : node -> round -> Prop
  -- (ghost) relation one_b(N:node, R:round) # := exists RMAX, V. one_b_max_vote(N,R,RMAX,V)
relation one_b : node -> round -> Prop

#gen_state

ghost relation maximalVote (n : node) (r: round) (maxr : round) (maxv : value) :=
    (maxr = TotalOrderWithNone.none ∧
      (∀ (MAXR : round) (V : value), ¬ (¬ TotalOrderWithNone.le r MAXR ∧ vote n MAXR V))) ∨
    (maxr ≠ TotalOrderWithNone.none ∧ ¬ TotalOrderWithNone.le r maxr ∧ vote n maxr maxv ∧
      (∀ (MAXR : round) (V : value), (¬ TotalOrderWithNone.le r MAXR ∧ vote n MAXR V) → TotalOrderWithNone.le MAXR maxr))


/- Quorum `q` shows `(r, v)` is safe. -/
ghost relation showsSafeAt (q : quorum) (r : round) (v : value) :=
    (Quorum.member N q → one_b N r) ∧
  (∃ (maxr : round),
    -- and `(r, v)` is maximal in the quorum
    ((maxr = TotalOrderWithNone.none ∧
      (∀ (N : node) (MAXR : round) (V : value),
        ¬ (Quorum.member N q ∧ one_b_max_vote N r MAXR V ∧ MAXR ≠ TotalOrderWithNone.none))) ∨
    (maxr ≠ TotalOrderWithNone.none ∧
      (∃ (N : node), Quorum.member N q ∧ one_b_max_vote N r maxr v) ∧
      (∀ (N : node) (MAXR : round) (V : value),
        (Quorum.member N q ∧ one_b_max_vote N r MAXR V ∧ MAXR ≠ TotalOrderWithNone.none) → TotalOrderWithNone.le MAXR maxr)
  )))

ghost relation isSafeAt (r : round) (v : value) :=
  ∃ (q : quorum), showsSafeAt q r v

ghost relation chosenAt (r : round) (v : value) :=
  ∃ (q : quorum), ∀ (n : node), Quorum.member n q → vote n r v

after_init {
  one_a R                   := False;
  one_b_max_vote N R1 R2 V  := False;
  proposal R V              := False;
  vote N R V                := False;
  decision N R V            := False;
  one_b N R                 := False;
  leftRound N R             := False
}

-- a proposer selects a round and sends a message asking nodes to join the round
action phase_1a (r : round) = {
  require r ≠ TotalOrderWithNone.none;
  one_a r := True
}


-- "join round" = receive 1a and answer with 1b
action phase_1b (n : node) (r : round) (max_round : round) (max_val : value) = {
  require r ≠ TotalOrderWithNone.none;
  require one_a r;
  require ¬ leftRound n r;
  require maximalVote n r max_round max_val;
  -- maximalVote n r max_round max_val;
  one_b_max_vote n r max_round max_val := True;
  one_b n r := True;
  leftRound n R := leftRound n R ∨ (¬ TotalOrderWithNone.le r R)
  -- leftRound := λ N R  => st.leftRound N R ∨ (N = n ∧ ¬ TotalOrderWithNone.le r R)
}

-- "propose" = receive a quorum of 1b's and send a 2a (proposal)
action phase_2a (r : round) (v : value) = {
  require r ≠ TotalOrderWithNone.none;
  require ∀ V, ¬ proposal r V;
  require isSafeAt r v;
  proposal r v := True
}

-- "cast vote" = receive a 2a and send 2b
action phase_2b (n : node) (r : round) (v : value) = {
  require r ≠ TotalOrderWithNone.none;
  require ¬ leftRound n r;
  require proposal r v;
  vote n r v := True
}

-- "decide" = receive a quorum of 2b's
action decision_ (n : node) (r : round) (v : value) = {
  require r ≠ TotalOrderWithNone.none;
  require chosenAt r v;
  decision n r v := True
}

safety [agreement] (decision N1 R1 V1 ∧ decision N2 R2 V2) → R1 = R2 ∧ V1 = V2

invariant proposal R V1 ∧ proposal R V2 → V1 = V2

invariant vote N R V → proposal R V

invariant
    (∃ (n : node), decision n R V) →
    (∃ (q : quorum), ∀ (n : node), Quorum.member n q → vote n R V)

-- Properties of `one_b_max_vote`
invariant
  (one_b_max_vote N R1 TotalOrderWithNone.none V1 ∧ ¬ TotalOrderWithNone.le R2 R1) → ¬ vote N R1 V2

invariant
  (one_b_max_vote N R RMAX V ∧ RMAX ≠ TotalOrderWithNone.none) →
    (¬ TotalOrderWithNone.le R RMAX ∧ vote N RMAX V)

invariant ∀ (N : node) (r rmax rother : round) (v vother : value),
  (one_b_max_vote N r rmax v ∧ rmax ≠ TotalOrderWithNone.none ∧
    ¬ TotalOrderWithNone.le r rother ∧ ¬ TotalOrderWithNone.le rother rmax) →
    ¬ vote N rother vother

-- Properties of `none`

invariant ¬ vote N TotalOrderWithNone.none V


-- Properties of choosable and proposal

invariant
  (¬ TotalOrderWithNone.le R2 R1 ∧ proposal R2 V2  ∧ V1 ≠ V2) →
  (∃ (N : node) (R3 RMAX : round) (V : value),
    Quorum.member N Q ∧ ¬ TotalOrderWithNone.le R3 R1 ∧
    one_b_max_vote N R3 RMAX V ∧
    ¬ vote N R1 V1)


-- Properties of one_b, left_rnd
-- #conjecture one_b_max_vote(N,R,RMAX,V) -> one_b(N,R)
-- conjecture one_b(N,R2) & ~le(R2,R1) -> left_rnd(N,R1)

invariant one_b N R2 ∧ ¬ TotalOrderWithNone.le R2 R1 → leftRound N R1

#gen_spec

prove_inv_init by { simp_all [initSimp, invSimp, actSimp] }
prove_inv_safe by { sdestruct st ; simp [invSimp, safeSimp] }

set_option maxHeartbeats 2000000

-- prove_inv_inductive by {
--   constructor
--   . apply inv_init
--   intro st st' hnext hinv
--   sts_induction <;> sdestruct_goal <;> sorry -- try solve_clause
--   -- { sorry }
--   -- { sorry }
--   -- { sorry }
--   -- { sorry }
-- }

-- unsat trace {
--   phase_1a
--   phase_2b
-- } by {
--   sintro st0 st1 st2
--   simp [initSimp, actSimp, wlp, Paxos.State.mk.injEq]
--   duper
-- }

end PaxosFOL
