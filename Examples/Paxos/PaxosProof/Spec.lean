import Veil

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

instantiate tot : TotalOrderWithZeroAndNone ballot
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

assumption [AcceptorsUNIV_complete]
  ∀ (a : acceptor), a ∈ AcceptorsUNIV

assumption [validBallots_complete]
  ∀ b, b ≠ tot.none ↔ b ∈ validBallots

after_init {
  msgs := msgTset.empty
  maxVBal A := tot.none
  maxBal A := tot.none
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
  require b ≠ tot.none
  let filterMsgs := msgTset.filter msgs (fun m => m.msgType == MsgType.Phase1a && m.bal == b)
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
    m.msgType == MsgType.Phase1a && decide (gt m.bal (maxBal a)))
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
  require b ≠ tot.none
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
  -- forbid picking acceptors that don't have a 1b for ballot b
  require (acSet.toList selectedAcceptors).all (fun a =>
    (msgTset.toList all1bMsgs).any (fun m => decide (m.acc = a)))
  let S := msgTset.filter all1bMsgs (fun m => acSet.contains m.acc selectedAcceptors)

  let quorumCovered := AcceptorsUNIV |>.all (fun a =>
    /- `/\ \A a \in Q : \E m \in S : m.acc = a, member a Q → (∃m ∈ S, m.acc = a)`-/
    !member a Q || (msgTset.toList S |>.any (fun m => decide (m.acc = a))))
  require quorumCovered
  -- \/ \A m \in S : m.maxVBal = -1
  -- \/ \E c \in 0..(b-1) : /\ \A m \in S : m.maxVBal =< c
  --                        /\ \E m \in S : m.maxVBal = c /\ m.maxVal = v
  let sList := msgTset.toList S
  let allMinusOne := sList.all (fun m => decide (m.maxVBal = tot.none))
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
safety [Consistency] ∀ v1 v2, Chosen v1 → Chosen v2 → v1 = v2


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
  ∀ c, lt c b → c ≠ tot.none →
    ∃ Q, ∀ a, member a Q → (VotedForIn a v c ∨ WontVoteIn a c)


-- TypeOK: maxBal[a] >= maxVBal[a] for all acceptors
-- (other conjuncts are type-level in Lean)
invariant [TypeOK] ∀ a, ge (maxBal a) (maxVBal a)

-- MsgInv for 1b messages
invariant [MsgInv1b] ∀ m, msgTset.contains m msgs → m.msgType = MsgType.Phase1b →
  -- m.bal <= maxBal[m.acc]
  tot.le m.bal (maxBal m.acc) ∧
  -- Either (maxVBal in Ballots ∧ VotedForIn) or (maxVBal = -1)
  ((m.maxVBal ≠ tot.none ∧ VotedForIn m.acc m.val m.maxVBal) ∨ (m.maxVBal = tot.none)) ∧
  -- For all c in (maxVBal+1)..(bal-1), no vote exists
  (∀ c, lt m.maxVBal c → lt c m.bal → ∀ v, ¬VotedForIn m.acc v c)

-- MsgInv for 2a messages
invariant [MsgInv2a] ∀ m, msgTset.contains m msgs → m.msgType = MsgType.Phase2a →
  -- SafeAt(m.val, m.bal)
  SafeAt m.val m.bal ∧
  -- Unique 2a message per ballot
  (∀ ma, msgTset.contains ma msgs → ma.msgType = MsgType.Phase2a → ma.bal = m.bal → ma = m)

-- MsgInv for 2b messages
invariant [MsgInv2b] ∀ m, msgTset.contains m msgs → m.msgType = MsgType.Phase2b →
  -- There exists a 2a message with same ballot and value
  (∃ ma, msgTset.contains ma msgs ∧ ma.msgType = MsgType.Phase2a ∧ ma.bal = m.bal ∧ ma.val = m.val) ∧
  -- m.bal <= maxVBal[m.acc]
  tot.le m.bal (maxVBal m.acc)

-- AccInv: acceptor invariants
invariant [AccInv] ∀ a,
  -- maxVBal[a] <= maxBal[a]
  tot.le (maxVBal a) (maxBal a) ∧
  -- (maxVBal[a] >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])
  (maxVBal a ≠ tot.none → VotedForIn a (maxVal a) (maxVBal a)) ∧
  -- For all c > maxVBal[a], no vote exists
  (∀ c, gt c (maxVBal a) → ∀ v, ¬VotedForIn a v c)

-- 2a messages only exist at valid ballots (not none)
invariant [two_a_valid_ballot] ∀ m, msgTset.contains m msgs → m.msgType = MsgType.Phase2a →
  m.bal ≠ tot.none

-- VotedInv: VotedForIn implies SafeAt and ballot ordering
invariant [VotedInv] ∀ a v b, VotedForIn a v b →
  SafeAt v b ∧ tot.le b (maxVBal a)

-- VotedOnce: All votes in the same ballot are for the same value
invariant [VotedOnce] ∀ a1 a2 b v1 v2,
  VotedForIn a1 v1 b → VotedForIn a2 v2 b → v1 = v2

#time #gen_spec

-- theorem Phase2b_Consistency (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
--     [acceptor_inhabited : Inhabited.{1} acceptor] (value : Type) [value_dec_eq : DecidableEq.{1} value]
--     [value_inhabited : Inhabited.{1} value] (quorum : Type) [quorum_dec_eq : DecidableEq.{1} quorum]
--     [quorum_inhabited : Inhabited.{1} quorum] (ballot : Type) [ballot_dec_eq : DecidableEq.{1} ballot]
--     [ballot_inhabited : Inhabited.{1} ballot] [tot : TotalOrderWithZeroAndNone ballot] (MsgSet : Type)
--     [MsgSet_dec_eq : DecidableEq.{1} MsgSet] [MsgSet_inhabited : Inhabited.{1} MsgSet] (AcceptorSet : Type)
--     [AcceptorSet_dec_eq : DecidableEq.{1} AcceptorSet] [AcceptorSet_inhabited : Inhabited.{1} AcceptorSet]
--     [msgTset : TSet (Msg acceptor value ballot) MsgSet] [acSet : TSet acceptor AcceptorSet] (χ : State.Label → Type)
--     [χ_rep :
--       ∀ __veil_f,
--         Veil.FieldRepresentation (State.Label.toDomain acceptor value quorum ballot MsgSet AcceptorSet __veil_f)
--           (State.Label.toCodomain acceptor value quorum ballot MsgSet AcceptorSet __veil_f) (χ __veil_f)]
--     [χ_rep_lawful :
--       ∀ __veil_f,
--         Veil.LawfulFieldRepresentation (State.Label.toDomain acceptor value quorum ballot MsgSet AcceptorSet __veil_f)
--           (State.Label.toCodomain acceptor value quorum ballot MsgSet AcceptorSet __veil_f) (χ __veil_f)
--           (χ_rep __veil_f)]
--     [σ_sub : IsSubStateOf (@State χ) σ]
--     [ρ_sub : IsSubReaderOf (@Theory acceptor value quorum ballot MsgSet AcceptorSet) ρ]
--     [Phase2b_dec_0 :
--       (a : acceptor) →
--         (__do_lift : State χ) →
--           (m : Msg acceptor value ballot) →
--             Decidable
--               (And (@Eq.{1} MsgType m.1 MsgType.Phase2a)
--                 (@TotalOrderWithZeroAndNone.le ballot tot
--                   (@Veil.FieldRepresentation.get
--                     (State.Label.toDomain acceptor value quorum ballot MsgSet AcceptorSet State.Label.maxBal)
--                     (State.Label.toCodomain acceptor value quorum ballot MsgSet AcceptorSet State.Label.maxBal)
--                     (χ State.Label.maxBal) (χ_rep State.Label.maxBal) __do_lift.3 a)
--                   m.4))] :
--     ∀ (a : acceptor),
--       Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
--         (@Phase2b.ext ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
--           quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
--           AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub
--           Phase2b_dec_0 a)
--         (@Assumptions ρ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
--           quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
--           AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet ρ_sub)
--         (@Invariants ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
--           quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
--           AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub)
--         (@Consistency ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
--           quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
--           AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
--   by
--   unveil
--   placeholder


-- theorem Phase2a_MsgInv2a (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
--     [acceptor_inhabited : Inhabited.{1} acceptor] (value : Type) [value_dec_eq : DecidableEq.{1} value]
--     [value_inhabited : Inhabited.{1} value] (quorum : Type) [quorum_dec_eq : DecidableEq.{1} quorum]
--     [quorum_inhabited : Inhabited.{1} quorum] (ballot : Type) [ballot_dec_eq : DecidableEq.{1} ballot]
--     [ballot_inhabited : Inhabited.{1} ballot] [tot : TotalOrderWithZeroAndNone ballot] (MsgSet : Type)
--     [MsgSet_dec_eq : DecidableEq.{1} MsgSet] [MsgSet_inhabited : Inhabited.{1} MsgSet] (AcceptorSet : Type)
--     [AcceptorSet_dec_eq : DecidableEq.{1} AcceptorSet] [AcceptorSet_inhabited : Inhabited.{1} AcceptorSet]
--     [msgTset : TSet (Msg acceptor value ballot) MsgSet] [acSet : TSet acceptor AcceptorSet] (χ : State.Label → Type)
--     [χ_rep :
--       ∀ __veil_f,
--         Veil.FieldRepresentation (State.Label.toDomain acceptor value quorum ballot MsgSet AcceptorSet __veil_f)
--           (State.Label.toCodomain acceptor value quorum ballot MsgSet AcceptorSet __veil_f) (χ __veil_f)]
--     [χ_rep_lawful :
--       ∀ __veil_f,
--         Veil.LawfulFieldRepresentation (State.Label.toDomain acceptor value quorum ballot MsgSet AcceptorSet __veil_f)
--           (State.Label.toCodomain acceptor value quorum ballot MsgSet AcceptorSet __veil_f) (χ __veil_f)
--           (χ_rep __veil_f)]
--     [σ_sub : IsSubStateOf (@State χ) σ]
--     [ρ_sub : IsSubReaderOf (@Theory acceptor value quorum ballot MsgSet AcceptorSet) ρ]
--     [Phase2a_dec_0 :
--       (b c : ballot) → Decidable (And (@TotalOrderWithZeroAndNone.le ballot tot c b) (Not (@Eq.{1} ballot c b)))]
--     [Phase2a_dec_1 :
--       (c : ballot) → (m : Msg acceptor value ballot) → Decidable (@TotalOrderWithZeroAndNone.le ballot tot m.5 c)] :
--     ∀ (b : ballot),
--       Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
--         (@Phase2a.ext ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
--           quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
--           AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub
--           Phase2a_dec_0 Phase2a_dec_1 b)
--         (@Assumptions ρ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
--           quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
--           AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet ρ_sub)
--         (@Invariants ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
--           quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
--           AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub)
--         (@MsgInv2a ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
--           quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
--           AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
--   by
--   unveil
--   placeholder


-- #model_check
-- {
--   acceptor := Fin 3,    -- 3 acceptors (a0, a1, a2)
--   value := Fin 2,       -- 2 values (v0, v1)
--   quorum := Fin 3,      -- 3 majority quorums
--   ballot := Fin 4,      -- 0 = none, 1, 2, 3 = valid ballots (matches TLA+ MaxBallot = 2)
--   MsgSet := Std.ExtTreeSet (Msg (Fin 3) (Fin 2) (Fin 4)) compare,
--   AcceptorSet := Std.ExtTreeSet (Fin 3) compare
-- }
-- {
--   -- Quorum membership: each quorum is a majority (2 of 3 acceptors)
--   -- Quorum 0: {acceptor 0, acceptor 1}
--   -- Quorum 1: {acceptor 0, acceptor 2}
--   -- Quorum 2: {acceptor 1, acceptor 2}
--   member := fun a q =>
--     match a.val, q.val with
--     | 0, 0 => true  -- acceptor 0 in quorum 0
--     | 1, 0 => true  -- acceptor 1 in quorum 0
--     | 0, 1 => true  -- acceptor 0 in quorum 1
--     | 2, 1 => true  -- acceptor 2 in quorum 1
--     | 1, 2 => true  -- acceptor 1 in quorum 2
--     | 2, 2 => true  -- acceptor 2 in quorum 2
--     | _, _ => false,
--   validBallots := [1, 2, 3],  -- Valid ballots (excluding none=0)
--   AcceptorsUNIV := [0, 1, 2]  -- All acceptors
-- }

end Paxos
