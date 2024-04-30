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

-- set_option pp.all true

set_option trace.sts true

relation fooo := 5 = (N : Nat)

-- #print fooo

relation maximalVote (n : node) (r: round) (maxr : round) (maxv : value) :=
    (maxr = TotalOrder.none ∧
      (∀ (MAXR : round) (V : value), ¬ (¬ TotalOrder.le r MAXR ∧ vote n MAXR V))) ∨
    (maxr ≠ TotalOrder.none ∧ ¬ TotalOrder.le r maxr ∧ vote n maxr maxv ∧
      (∀ (MAXR : round) (V : value), (¬ TotalOrder.le r MAXR ∧ vote n MAXR V) → TotalOrder.le MAXR maxr))




/- Quorum `q` shows `(r, v)` is safe. -/
relation showsSafeAt :=
    True

#check showsSafeAt

macro "showsSafeAt" : term => `(showsSafeAt (st := by exact_state))

relation isSafeAt := showsSafeAt

#print isSafeAt

end PaxosFOL
