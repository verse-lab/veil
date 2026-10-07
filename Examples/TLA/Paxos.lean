module

public import Veil

-- source:https://github.com/DistAlgo/proofs/blob/master/basic-paxos/PaxosLam.tla
-- ------------------------------- MODULE Paxos -------------------------------
-- (***************************************************************************)
-- (* This is a TLA+ specification of the Paxos Consensus algorithm,          *)
-- (* described in                                                            *)
-- (*                                                                         *)
-- (*  Paxos Made Simple:                                                     *)
-- (*   http://research.microsoft.com/en-us/um/people/lamport/pubs/pubs.html#paxos-simple *)
-- (*                                                                         *)
-- (* and a TLAPS-checked proof of its correctness.  This was mostly done as  *)
-- (* a test to see how the SMT backend of TLAPS is now working.              *)
-- (***************************************************************************)
-- EXTENDS Integers, TLAPS, TLC

public class PaxosMember (acceptor : outParam Type) (quorum : Type) where
  member : acceptor → quorum → Bool

public instance : PaxosMember (Fin 3) (Fin 3) where
  member a q :=
    match a.val, q.val with
    | 0, 0 => true
    | 1, 0 => true
    | 0, 1 => true
    | 2, 1 => true
    | 1, 2 => true
    | 2, 2 => true
    | _, _ => false

veil module Paxos

-- Ballot type: Fin (MaxBallot + 2), where 0 = "no ballot" (TLA+'s -1)
-- and 1..MaxBallot+1 = valid ballots (TLA+'s 0..MaxBallot)
abbrev BallotTy (maxBallot : Nat) := Fin (maxBallot + 2)

-- CONSTANTS Acceptors, Values, Quorums
type acceptor
type value
type quorum

-- Ballots == 0..MaxBallot (closed interval)
param maxBallot : Nat

-- ASSUME QuorumAssumption ==
--           /\ Quorums \subseteq SUBSET Acceptors
--           /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

instantiate pm : PaxosMember acceptor quorum

-- immutable relation member (A : acceptor) (Q : quorum)
-- PaxosMember acceptor quorum
open PaxosMember
-- None == CHOOSE v : v \notin Values
-- We use Option value instead: none = None, some v = v ∈ Values

-- -----------------------------------------------------------------------------
-- (***************************************************************************)
-- (* This section of the spec defines the invariant Inv.                     *)
-- (***************************************************************************)
-- Messages ==      [type : {"1a"}, bal : Ballots]
--             \cup [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
--                     maxVal : Values \cup {None}, acc : Acceptors]
--             \cup [type : {"2a"}, bal : Ballots, val : Values]
--             \cup [type : {"2b"}, bal : Ballots, val : Values, acc : Acceptors]

@[veil_decl]
inductive Msg (ac val blt : Type) where
  | phase1a (bal : blt) : Msg ac val blt
  | phase1b (acc : ac) (bal : blt) (maxVBal : blt) (maxVal : Option val) : Msg ac val blt
  | phase2a (bal : blt) (v : val) : Msg ac val blt
  | phase2b (acc : ac) (bal : blt) (v : val) : Msg ac val blt
deriving instance Veil.Enumeration for Msg

abbrev Msg.ballot (m : Msg ac val blt) : blt :=
  match m with
  | .phase1a bal => bal
  | .phase1b _ bal _ _ => bal
  | .phase2a bal _ => bal
  | .phase2b _ bal _ => bal

abbrev PaxosMsg (ac val : Type) (maxBallot : Nat) := Msg ac val (BallotTy maxBallot)

type MsgSet
type AcceptorSet

instantiate msgSet : TSet (PaxosMsg acceptor value maxBallot) MsgSet
instantiate acSet : TSet acceptor AcceptorSet

-- VARIABLES msgs,    \* The set of messages that have been sent.
--           maxBal,  \* maxBal[a] is the highest-number ballot acceptor a
--                    \*   has participated in.
--           maxVBal, \* maxVBal[a] is the highest ballot in which a has
--           maxVal   \*   voted, and maxVal[a] is the value it voted for
--                    \*   in that ballot.

individual msgs : MsgSet
function maxVBal (a : acceptor) : BallotTy maxBallot
function maxBal (a : acceptor) : BallotTy maxBallot
function maxVal (a : acceptor) : Option value

#gen_state

assumption [quorum_intersection]
  ∀ (q1 q2 : quorum), ∃ (r : acceptor), member r q1 ∧ member r q2

-- Init == /\ msgs = {}
--         /\ maxVBal = [a \in Acceptors |-> -1]
--         /\ maxBal  = [a \in Acceptors |-> -1]
--         /\ maxVal  = [a \in Acceptors |-> None]

after_init {
  let noBallot : BallotTy maxBallot := ⟨0, Nat.zero_lt_succ _⟩
  msgs := msgSet.empty
  maxVBal A := noBallot
  maxBal A := noBallot
  maxVal A := none
}

-- Send(m) == msgs' = msgs \cup {m}
procedure Send (m : PaxosMsg acceptor value maxBallot) {
  msgs := msgSet.insert m msgs
}

-- (***************************************************************************)
-- (* Phase 1a: A leader selects a ballot number b and sends a 1a message     *)
-- (* with ballot b to a majority of acceptors.  It can do this only if it    *)
-- (* has not already sent a 1a message for ballot b.                         *)
-- (***************************************************************************)
-- Phase1a(b) == /\ ~ \E m \in msgs : (m.type = "1a") /\ (m.bal = b)
--               /\ Send([type |-> "1a", bal |-> b])
--               /\ UNCHANGED <<maxVBal, maxBal, maxVal>>
action Phase1a (b : BallotTy maxBallot) {
  -- NOTE: This `require` is controlled by the `Next`
  let noBallot : BallotTy maxBallot := ⟨0, Nat.zero_lt_succ _⟩
  require b ≠ noBallot

  require ¬ ∃ msg : { m // m ∈ msgs },
    -- NOTE: If this `match` has type `Prop`, then synthesizing its `Decidable` instance might be difficult
    (match msg.val with
      | .phase1a bal => decide $ bal = b
      | _ => false) = true
  Send (.phase1a b)
}

-- (***************************************************************************)
-- (* Phase 1b: If an acceptor receives a 1a message with ballot b greater    *)
-- (* than that of any 1a message to which it has already responded, then it  *)
-- (* responds to the request with a promise not to accept any more proposals *)
-- (* for ballots numbered less than b and with the highest-numbered ballot   *)
-- (* (if any) for which it has voted for a value and the value it voted for  *)
-- (* in that ballot.  That promise is made in a 1b message.                  *)
-- (***************************************************************************)
-- Phase1b(a) ==
--   \E m \in msgs :
--      /\ m.type = "1a"
--      /\ m.bal > maxBal[a]
--      /\ Send([type |-> "1b", bal |-> m.bal, maxVBal |-> maxVBal[a],
--                maxVal |-> maxVal[a], acc |-> a])
--      /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
--      /\ UNCHANGED <<maxVBal, maxVal>>

action Phase1b (a : acceptor) {
  let m : { m // m ∈ msgs } :| (match m.val with
    | .phase1a b => b > maxBal a
    | _ => false) = true
  let b := m.val.ballot
  Send (.phase1b a b (maxVBal a) (maxVal a))
  maxBal a := b
}

-- (***************************************************************************)
-- (* Phase 2a: If the leader receives a response to its 1b message (for      *)
-- (* ballot b) from a quorum of acceptors, then it sends a 2a message to all *)
-- (* acceptors for a proposal in ballot b with a value v, where v is the     *)
-- (* value of the highest-numbered proposal among the responses, or is any   *)
-- (* value if the responses reported no proposals.  The leader can send only *)
-- (* one 2a message for any ballot.                                          *)
-- (***************************************************************************)
-- Phase2a(b) ==
--   /\ ~ \E m \in msgs : (m.type = "2a") /\ (m.bal = b)
--   /\ \E v \in Values :
--        /\ \E Q \in Quorums :
--             \E S \in SUBSET {m \in msgs : (m.type = "1b") /\ (m.bal = b)} :
--                /\ \A a \in Q : \E m \in S : m.acc = a
--                /\ \/ \A m \in S : m.maxVBal = -1
--                   \/ \E c \in 0..(b-1) :
--                         /\ \A m \in S : m.maxVBal =< c
--                         /\ \E m \in S : /\ m.maxVBal = c
--                                         /\ m.maxVal = v
--        /\ Send([type |-> "2a", bal |-> b, val |-> v])
--   /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

ghost relation quorumCovered (Q : quorum) (S : MsgSet) :=
-- ghost relation quorumCovered (Q : quorum) (S : List (PaxosMsg acceptor value maxBallot)) :=
  ∀ a, member a Q → ∃ m : { m // m ∈ S }, (match m.val with
    | .phase1b acc .. => decide $ acc = a
    | _ => false) = true

ghost relation allNoBallot (S : MsgSet) :=
-- ghost relation allNoBallot (S : List (PaxosMsg acceptor value maxBallot)) :=
  let noBallot : BallotTy maxBallot := ⟨0, Nat.zero_lt_succ _⟩
  ∀ m : { m // m ∈ S }, (match m.val with
    | .phase1b _ _ maxVBal _ => decide $ maxVBal = noBallot
    | _ => false) = true

ghost relation validBallotExists (S : MsgSet) (b : BallotTy maxBallot) (v : value) :=
-- ghost relation validBallotExists (S : List (PaxosMsg acceptor value maxBallot)) (b : BallotTy maxBallot) (v : value) :=
  ∃ c < b, c.val ≠ 0 ∧
    (∀ m : { m // m ∈ S }, (match m.val with
      | .phase1b _ _ maxVBal _ => decide $ maxVBal ≤ c
      | _ => false) = true) ∧
    (∃ m : { m // m ∈ S }, (match m.val with
      | .phase1b _ _ maxVBal maxVal => decide $ maxVBal = c ∧ maxVal = some v
      | _ => false) = true)

-- Optimization: instead of picking MsgSet (huge), pick AcceptorSet (only 2^n possibilities)
action Phase2a (b : BallotTy maxBallot) {
  -- NOTE: This `require` is controlled by the `Next`
  let noBallot : BallotTy maxBallot := ⟨0, Nat.zero_lt_succ _⟩
  require b ≠ noBallot

  -- ~ \E m \in msgs : (m.type = "2a") /\ (m.bal = b)
  require ¬ ∃ msg : { m // m ∈ msgs },
    (match msg.val with
      | .phase2a bal _ => decide $ bal = b
      | _ => false) = true

  let v ← pick value
  let Q ← pick quorum

  /- Instead of picking S from the set of all subsets of messages,
    we pick a subset of acceptors, and construct S by filtering messages from those
    acceptors. As we only care about condition `m.acc = a`.
    This reduces the non-deterministic choices to 2^|acceptors|.  -/
  let selectedAcceptors ← pick AcceptorSet
  let S := msgSet.filter msgs fun m =>
    match m with
    | .phase1b acc bal .. => bal == b && acSet.contains acc selectedAcceptors
    | _ => false
  -- NOTE: The `Decidable` instance for the second `require` can be synthesized here, while the first one cannot,
  -- so we put them separately to avoid certain hussle
  require quorumCovered Q S
  require allNoBallot S ∨ validBallotExists S b v
  Send (.phase2a b v)
}

-- (***************************************************************************)
-- (* Phase 2b: If an acceptor receives a 2a message for a ballot numbered    *)
-- (* b, it votes for the message's value in ballot b unless it has already   *)
-- (* responded to a 1a request for a ballot number greater than or equal to  *)
-- (* b.                                                                      *)
-- (***************************************************************************)
-- Phase2b(a) ==
--   \E m \in msgs :
--     /\ m.type = "2a"
--     /\ m.bal >= maxBal[a]
--     /\ Send([type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a])
--     /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
--     /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
--     /\ maxVal' = [maxVal EXCEPT ![a] = m.val]

action Phase2b (a : acceptor) {
  let m : { m // m ∈ msgs } :| (match m.val with
    | .phase2a bal _ => decide $ bal ≥ maxBal a
    | _ => false) = true
  let m := m.val
  -- NOTE: `v` should be obtained right after knowing that `m` is a valid 2a message,
  -- but currently we cannot do that, so use a trick
  let b := m.ballot
  let v := match m with
    | .phase2a _ v => v
    | _ => default    -- this is a dead branch, but exploits the `Inhabited` instance of `value`
  Send (.phase2b a b v)
  maxVBal a := b
  maxBal a := b
  maxVal a := some v
}

-- Next == \/ \E b \in Ballots : Phase1a(b) \/ Phase2a(b)
--         \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

-- Spec == Init /\ [][Next]_vars
-- -----------------------------------------------------------------------------
-- (***************************************************************************)
-- (* How a value is chosen:                                                  *)
-- (*                                                                         *)
-- (* This spec does not contain any actions in which a value is explicitly   *)
-- (* chosen (or a chosen value learned).  Wnat it means for a value to be    *)
-- (* chosen is defined by the operator Chosen, where Chosen(v) means that v  *)
-- (* has been chosen.  From this definition, it is obvious how a process     *)
-- (* learns that a value has been chosen from messages of type "2b".         *)
-- (***************************************************************************)
-- VotedForIn(a, v, b) == \E m \in msgs : /\ m.type = "2b"
--                                        /\ m.val  = v
--                                        /\ m.bal  = b
--                                        /\ m.acc  = a

-- ChosenIn(v, b) == \E Q \in Quorums :
--                      \A a \in Q : VotedForIn(a, v, b)

-- Chosen(v) == \E b \in Ballots : ChosenIn(v, b)
ghost relation VotedForIn (a : acceptor) (v : value) (b : BallotTy maxBallot) :=
  msgSet.contains (.phase2b a b v) msgs
ghost relation ChosenIn (v : value) (b : BallotTy maxBallot) :=
  ∃ (Q : quorum), ∀ a, member a Q → VotedForIn a v b
ghost relation Chosen (v : value) :=
  ∃ b, ChosenIn v b
-- (***************************************************************************)
-- (* The consistency condition that a consensus algorithm must satisfy is    *)
-- (* the invariance of the following state predicate Consistency.            *)
-- (***************************************************************************)
-- Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => (v1 = v2)
invariant [Consistency] ∀ v1 v2, Chosen v1 ∧ Chosen v2 → v1 = v2

#gen_spec
#gen_executable

-- #model_check compiled
-- {
--   acceptor := Fin 3,
--   value := Fin 2,
--   quorum := Fin 3,
--   maxBallot := 3,
--   MsgSet := OrdList (PaxosMsg (Fin 3) (Fin 2) 3),
--   AcceptorSet := OrdList (Fin 3)
-- }

end Paxos
