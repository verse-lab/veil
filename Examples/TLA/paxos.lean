import veil

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

veil module Paxos

-- CONSTANTS Acceptors, Values, Quorums
type acceptor
type value
type quorum
type ballot

-- ASSUME QuorumAssumption ==
--           /\ Quorums \subseteq SUBSET Acceptors
--           /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

-- (***************************************************************************)
-- (* The following lemma is an immediate consequence of the assumption.      *)
-- (***************************************************************************)
-- LEMMA QuorumNonEmpty == \A Q \in Quorums : Q # {}
-- BY QuorumAssumption

-- Ballots == Nat

instantiate tot : TotalOrderWithZero ballot
immutable individual minusOne : ballot
immutable individual validBallots : List ballot
immutable relation member (A : acceptor) (Q : quorum)

-- VARIABLES msgs,    \* The set of messages that have been sent.
--           maxBal,  \* maxBal[a] is the highest-number ballot acceptor a
--                    \*   has participated in.
--           maxVBal, \* maxVBal[a] is the highest ballot in which a has
--           maxVal   \*   voted, and maxVal[a] is the value it voted for
--                    \*   in that ballot.

-- vars == <<msgs, maxBal, maxVBal, maxVal>>


-- None == CHOOSE v : v \notin Values

-- LEMMA NoneNotAValue == None \notin Values
-- BY NoSetContainsEverything DEF None

type MsgSet
type AcceptorSet

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
inductive MsgType where
  | Phase1a
  | Phase1b
  | Phase2a
  | Phase2b
deriving instance Veil.Enumeration for MsgType

@[veil_decl]
structure Msg (ac val blt : Type) where
  msgType : MsgType
  acc : ac
  val : val
  bal : blt
  maxVBal : blt
deriving instance Veil.Enumeration for Msg

instantiate msgTset : TSet (Msg acceptor value ballot) MsgSet
instantiate acSet : TSet acceptor AcceptorSet

individual msgs : MsgSet
function maxVBal (a : acceptor) : ballot
function maxBal (a : acceptor) : ballot
function maxVal (a : acceptor) : value
immutable individual AcceptorsUNIV : List acceptor

#gen_state

-- Init == /\ msgs = {}
--         /\ maxVBal = [a \in Acceptors |-> -1]
--         /\ maxBal  = [a \in Acceptors |-> -1]
--         /\ maxVal  = [a \in Acceptors |-> None]

theory ghost relation lt (x y : ballot) := (tot.le x y ∧ x ≠ y)
theory ghost relation next (x y : ballot) := (lt x y ∧ ∀ z, lt x z → tot.le y z)
theory ghost relation ge (x y : ballot) := (tot.le y x)
theory ghost relation gt (x y : ballot) := (tot.le y x ∧ x ≠ y)

assumption [quorum_intersection]
  ∀ (q1 q2 : quorum), ∃ (r : acceptor), member r q1 ∧ member r q2

after_init {
  msgs := msgTset.empty
  maxVBal A := minusOne
  maxBal A := minusOne
  maxVal A := (default : value)
}

-- Send(m) == msgs' = msgs \cup {m}
procedure Send (m : Msg acceptor value ballot) {
  msgs := msgTset.insert m msgs
}

-- (***************************************************************************)
-- (* Phase 1a: A leader selects a ballot number b and sends a 1a message     *)
-- (* with ballot b to a majority of acceptors.  It can do this only if it    *)
-- (* has not already sent a 1a message for ballot b.                         *)
-- (***************************************************************************)
-- Phase1a(b) == /\ ~ \E m \in msgs : (m.type = "1a") /\ (m.bal = b)
--               /\ Send([type |-> "1a", bal |-> b])
--               /\ UNCHANGED <<maxVBal, maxBal, maxVal>>
action Phase1a (b : ballot){
  require b ≠ minusOne
  let filterMsgs := msgTset.filter msgs (fun m => decide $ m.msgType = MsgType.Phase1a ∧ m.bal = b)
  require msgTset.count filterMsgs = 0
  let sentMsg : Msg acceptor value ballot := {
    msgType := MsgType.Phase1a,
    bal := b,
    /-Unused variable-/
    acc := default,
    val := default,
    maxVBal := default
  }
  Send sentMsg
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
  -- let m :| msgTset.contains m msgs ∧ m.msgType = MsgType.Phase1a
  let filteredMsgs := msgTset.filter msgs (fun m =>
    decide $ m.msgType = MsgType.Phase1a ∧ gt m.bal (maxBal a))
  let m :| msgTset.contains m filteredMsgs
  -- require gt m.bal (maxBal a)
  let replyMsg : Msg acceptor value ballot := {
    msgType := MsgType.Phase1b,
    acc := a,
    val := maxVal a,
    bal := m.bal,
    maxVBal := maxVBal a
  }
  Send replyMsg
  maxBal a := m.bal
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

-- Imperative version: Q is an action parameter, S is picked non-deterministically
-- from SUBSET of 1b messages, and v is computed from S
-- Optimization: instead of picking MsgSet (huge), pick AcceptorSet (only 2^n possibilities)
action Phase2a (b : ballot) {
  require b ≠ minusOne
  let filterMsgs := msgTset.filter msgs (fun m =>
    decide $ m.msgType = MsgType.Phase2a ∧ m.bal = b)
  require msgTset.count filterMsgs = 0
  let v ← pick value
  let Q ← pick quorum
  let all1bMsgs := msgTset.filter msgs (fun m =>
    decide $ m.msgType = MsgType.Phase1b ∧ m.bal = b)

  /- Instead of picking S from the set of all subsets of messages,
    we pick a subset of acceptors, and construct S by filtering messages from those
    acceptors. As we only care about condition `m.acc = a`.
    This reduces the non-deterministic choices to 2^|acceptors|.  -/
  let selectedAcceptors ← pick AcceptorSet
  let S := msgTset.filter all1bMsgs (fun m => acSet.contains m.acc selectedAcceptors)

  let quorumCovered := AcceptorsUNIV |>.all (fun a =>
    /- `/\ \A a \in Q : \E m \in S : m.acc = a, member a Q → (∃m ∈ S, m.acc = a)`-/
    !member a Q || (msgTset.toList S |>.any (fun m => decide (m.acc = a))))
  require quorumCovered
  -- \/ \A m \in S : m.maxVBal = -1
  -- \/ \E c \in 0..(b-1) : /\ \A m \in S : m.maxVBal =< c
  --                        /\ \E m \in S : m.maxVBal = c /\ m.maxVal = v
  let sList := msgTset.toList S
  let allMinusOne := sList.all (fun m => decide (m.maxVBal = minusOne))
  let vb := validBallots.any (fun c =>
    (decide $ lt c b) ∧
    sList.all (fun m => decide (tot.le m.maxVBal c)) ∧
    sList.any (fun m => decide (m.maxVBal = c ∧ m.val = v)))
  require allMinusOne ∨ vb
  let sentMsg : Msg acceptor value ballot := {
    msgType := MsgType.Phase2a,
    val := v,
    bal := b,
    acc := default,
    maxVBal := default
    }
  Send sentMsg
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
  -- let m :| msgTset.contains m msgs ∧ m.msgType = MsgType.Phase2a
  -- require ge m.bal (maxBal a)
  let filteredMsgs := msgTset.filter msgs (fun m =>
    decide $ m.msgType = MsgType.Phase2a ∧ ge m.bal (maxBal a))
  let m :| msgTset.contains m filteredMsgs
  let replyMsg : Msg acceptor value ballot := {
    msgType := MsgType.Phase2b,
    acc := a,
    val := m.val,
    bal := m.bal,
    maxVBal := default
  }
  Send replyMsg
  maxVBal a := m.bal
  maxBal a := m.bal
  maxVal a := m.val
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

ghost relation VotedForIn (a : acceptor) (v : value) (b : ballot) :=
  ∃ m, msgTset.contains m msgs ∧ m.msgType = MsgType.Phase2b ∧ m.val = v ∧ m.bal = b ∧ m.acc = a
ghost relation ChosenIn (v : value) (b : ballot) :=
  ∃ Q, ∀ a, member a Q → VotedForIn a v b
ghost relation Chosen (v : value) :=
  ∃ b, ChosenIn v b

-- (***************************************************************************)
-- (* The consistency condition that a consensus algorithm must satisfy is    *)
-- (* the invariance of the following state predicate Consistency.            *)
-- (***************************************************************************)
-- Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => (v1 = v2)
invariant [Consistency] ∀ v1 v2, Chosen v1 → Chosen v2 → v1 = v2


-- TypeOK == /\ msgs \in SUBSET Messages
--           /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
--           /\ maxBal \in  [Acceptors -> Ballots \cup {-1}]
--           /\ maxVal \in  [Acceptors -> Values \cup {None}]
--           /\ \A a \in Acceptors : maxBal[a] >= maxVBal[a]

-- (***************************************************************************)
-- (* WontVoteIn(a, b) is a predicate that implies that a has not voted and   *)
-- (* never will vote in ballot b.                                            *)
-- (***************************************************************************)
-- WontVoteIn(a, b) == /\ \A v \in Values : ~ VotedForIn(a, v, b)
--                     /\ maxBal[a] > b
ghost relation WontVoteIn (a : acceptor) (b : ballot) :=
  (∀ v, ¬ VotedForIn a v b) ∧ gt (maxBal a) b
-- (***************************************************************************)
-- (* The predicate SafeAt(v, b) implies that no value other than perhaps v   *)
-- (* has been or ever will be chosen in any ballot numbered less than b.     *)
-- (***************************************************************************)
-- SafeAt(v, b) ==
--   \A c \in 0..(b-1) :
--     \E Q \in Quorums :
--       \A a \in Q : VotedForIn(a, v, c) \/ WontVoteIn(a, c)
ghost relation SafeAt (v : value) (b : ballot) :=
  ∀ c, lt c b →
    ∃ Q, ∀ a, member a Q → (VotedForIn a v c ∨ WontVoteIn a c)


-- invariant [MsgInv] MsgInv1b ∧ MsgInv2a ∧ MsgInv2b
set_option synthInstance.maxSize 10000
set_option synthInstance.maxHeartbeats 2000000
set_option synthInstance.maxSize 2000
#gen_spec

-- \* Modification History
-- \* Created Sat Nov 17 16:02:06 PST 2012 by lamport
#model_check
{
  ballot := Fin 4,   -- 0 = minusOne, 1..3 = valid ballots (matches TLA+ MaxBallot = 2, i.e., 0..2)
  value := Fin 2,    -- matches TLA+ Values = {v1, v2}
  acceptor := Fin 3,
  quorum := Fin 3,
  MsgSet := Std.ExtTreeSet (Msg (Fin 3) (Fin 2) (Fin 4)),
  AcceptorSet := Std.ExtTreeSet (Fin 3)
}
{
  AcceptorsUNIV := [0, 1, 2],  -- a0, a1, a2
  -- Quorums: q0 = {a0, a1}, q1 = {a0, a2}, q2 = {a1, a2}
  member := fun a q =>
    match q.val, a.val with
    | 0, 0 => true  -- q0 contains a0
    | 1, 0 => true  -- q1 contains a0
    | 0, 1 => true  -- q0 contains a1
    | 2, 1 => true  -- q2 contains a1
    | 1, 2 => true  -- q1 contains a2
    | 2, 2 => true  -- q2 contains a2
    | _, _ => false
  minusOne := 0
  validBallots := [1, 2, 3]  -- 0 represents -1 (no ballot), valid ballots are 1, 2, 3
}

end Paxos
