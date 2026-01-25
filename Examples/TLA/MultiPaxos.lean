import Veil

open Std
-- ------------------------------- MODULE MultiPaxosUs -------------------------------
-- (***************************************************************************)
-- (* This is a TLA+ specification of the MultiPaxos Consensus algorithm,     *)
-- (* described in                                                            *)
-- (*                                                                         *)
-- (*  The Part-Time Parliament:                                              *)
-- (*  http://research.microsoft.com/en-us/um/people/lamport/pubs/lamport-paxos.pdf *)
-- (*                                                                         *)
-- (* and a TLAPS-checked proof of its correctness. This is an extension of   *)
-- (* the proof of Basic Paxos found in TLAPS examples directory.             *)
-- (***************************************************************************)
-- EXTENDS Integers, TLAPS

veil module MultiPaxosUs
-- CONSTANTS Acceptors, Values, Quorums, Proposers
type ballot
type slot
type value
type acceptor
type proposer
type quorum


@[veil_decl]
structure Voted (bl slt vl : Type) where
  bal  : bl
  slot : slt
  val  : vl
deriving instance Veil.Enumeration for Voted

@[veil_decl]
structure Decree (slt vl : Type) where
  slot : slt
  val  : vl
deriving instance Veil.Enumeration for Decree

/-
Messages ==
[type : {"1a"}, bal : Ballots, from : Proposers] \ cup
[ type : {"1b"}, bal : Ballots,
  voted : SUBSET [bal : Ballots,
  slot : Slots,
  val : Values],
  from : Acceptors]
[type : {"2a"}, bal : Ballots, decrees : SUBSET [slot : Slots, val : Values], from : Proposers]
[type : {"2b"}, bal : Ballots, slot : Slots, val : Values, from : Acceptors]
-/
type SlotSet
type VotedSet
type DecreeSet
type MsgSet
type AcceptorSet

@[veil_decl]
inductive MsgType where
  | Phase1a
  | Phase1b
  | Phase2a
  | Phase2b
deriving instance Veil.Enumeration for MsgType


@[veil_decl]
inductive MsgSrc (prop acc : Type) where
  | fromProposer : prop → MsgSrc prop acc
  | fromAcceptor : acc → MsgSrc prop acc
deriving instance Veil.Enumeration for MsgSrc

@[veil_decl]
structure Msg (prop acc val blt slt vcont dcont : Type) where
  msgType : MsgType
  src : MsgSrc prop acc
  val : val
  bal : blt
  slot : slt
  decrees : dcont
  voted : vcont
deriving instance Veil.Enumeration for Msg


instantiate tot : TotalOrderWithZero ballot
instantiate voteTset : TSet (Voted ballot slot value) VotedSet
instantiate slotTset : TSet slot SlotSet
instantiate decreeSet : TSet (Decree slot value) DecreeSet
instantiate msgTset : TSet (Msg proposer acceptor value ballot slot VotedSet DecreeSet) MsgSet
instantiate acceptorTset : TSet acceptor AcceptorSet

immutable individual one : ballot
immutable relation member (A : acceptor) (Q : quorum)

individual sent : MsgSet
immutable individual SlotsUNIV : List slot
immutable individual AcceptorsUNIV : List acceptor

#gen_state


theory ghost relation lt (x y : ballot) := (tot.le x y ∧ x ≠ y)
theory ghost relation next (x y : ballot) := (lt x y ∧ ∀ z, lt x z → tot.le y z)
assumption [zero_one] next tot.zero one
-- ASSUME QuorumAssumption ==
--           /\ Quorums \subseteq SUBSET Acceptors
--           /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}
assumption [quorum_intersection]
  ∀ (q1 q2 : quorum), ∃ (r : acceptor), member r q1 ∧ member r q2

after_init {
  sent := msgTset.empty
}


procedure Send (m : MsgSet) {
  sent := msgTset.toList m |>.foldl (fun acc msg => msgTset.insert msg acc) sent
}

-- (***************************************************************************)
-- (* Phase 1a: Executed by a proposer, it selects a ballot number on which   *)
-- (* Phase 1a has never been initiated. This number is sent to any set of    *)
-- (* acceptors which contains at least one quorum from Quorums. Trivially it *)
-- (* can be broadcasted to all Acceptors. For safety, any subset of          *)
-- (* Acceptors would suffice. For liveness, a subset containing at least one *)
-- (* Quorum is needed.                                                       *)
-- (***************************************************************************)
-- Phase1a(p) == \E b \in Ballots:
--   Send({[type |-> "1a", from |-> p, bal |-> b]})
action Phase1a (p : proposer) {
  let b ← pick ballot
  let sentMsg : Msg proposer acceptor value ballot slot VotedSet DecreeSet := {
    msgType := MsgType.Phase1a,
    src := MsgSrc.fromProposer p,
    val := default,
    bal := b,
    slot := default,
    decrees := default,
    voted := default}
  Send (msgTset.insert sentMsg msgTset.empty)
}

-- (***************************************************************************)
-- (* Phase 1b: If an acceptor receives a 1a message with ballot b greater    *)
-- (* than that of any 1a message to which it has already responded, then it  *)
-- (* responds to the request with a promise not to accept any more proposals *)
-- (* for ballots numbered less than b; otherwise it sends a preempt to the   *)
-- (* proposer telling the greater ballot.                                    *)
-- (* In case of a 1b reply, the acceptor writes a mapping in S -> B \times V *)
-- (* This This mapping reveals for each slot, the value that the acceptor    *)
-- (* most recently (i.e., highest ballot) voted on, if any.                  *)
-- (***************************************************************************)

-- voteds(a) == {[bal |-> m.bal, slot |-> m.slot, val |-> m.val]: m \in {m \in sent: m.type = "2b" /\ m.from = a}}
-- set_option trace.veil.desugar true
procedure voteds (a : acceptor) {
  let voteSet' : VotedSet :=
    msgTset.map (msgTset.filter sent (fun m => m.msgType = MsgType.Phase2b ∧ m.src = MsgSrc.fromAcceptor a))
     (fun m =>
      { bal    := m.bal,
        slot   := m.slot,
        val    := m.val : Voted ballot slot value })
  return voteSet'
}

-- PartialBmax(T) ==
--   {t \in T : \A t1 \in T : t1.slot = t.slot => t1.bal =< t.bal}
procedure PartialBmax (T : VotedSet) {
  let partialBmaxSet' := voteTset.filter T (fun t =>
    voteTset.toList T |>.all (fun t1 =>
      decide $ t1.slot = t.slot → (tot.le t1.bal t.bal) ))
  return partialBmaxSet'
}


-- Phase1b(a) == \E m \in sent:
--   /\ m.type = "1a"
--   /\ \A m2 \in {m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.from = a}: m.bal > m2.bal
--   /\ Send({[type |-> "1b", from |-> a, bal |-> m.bal, voted |-> PartialBmax(voteds(a))]})
action Phase1b (a : acceptor) {
  let phase1aMsgs := msgTset.filter sent (fun m => m.msgType = MsgType.Phase1a)
  let m :| m ∈ phase1aMsgs
  let prevMsgsFromA := msgTset.filter sent (fun m2 =>
    (m2.msgType = MsgType.Phase1b ∨ m2.msgType = MsgType.Phase2b)
    ∧ m2.src = MsgSrc.fromAcceptor a)
  /- `/\ \A m2 \in {m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.from = a}: m.bal > m2.bal` -/
  let allPrevBallotsLower := msgTset.toList prevMsgsFromA |>.all (fun m2 => decide (lt m2.bal m.bal))
  require allPrevBallotsLower
  let votedSet ← voteds a
  let partialBmaxSet ← PartialBmax votedSet
  let replyMsg : Msg proposer acceptor value ballot slot VotedSet DecreeSet := {
    msgType := MsgType.Phase1b,
    src := MsgSrc.fromAcceptor a,
    bal := m.bal,
    voted := partialBmaxSet,
    /- Unused fields -/
    val := default,
    slot := default,
    decrees := default }
  Send (msgTset.insert replyMsg msgTset.empty)
}

-- (***************************************************************************)
-- (* Phase 2a: If the proposer receives a response to its 1b message (for    *)
-- (* ballot b) from a quorum of acceptors, then it sends a 2a message to all *)
-- (* acceptors for a proposal in ballot b. Per slot received in the replies, *)
-- (* the proposer finds out the value most recently (i.e., highest ballot)   *)
-- (* voted by the acceptors in the received set. Thus a mapping in S -> V    *)
-- (* is created. This mapping along with the ballot that passed Phase 1a is  *)
-- (* propogated to again, any subset of Acceptors - Hopefully to one         *)
-- (* containing at least one Quorum.                                         *)
-- (* Bmax            creates the desired mapping from received replies.      *)
-- (* NewProposals    instructs how new slots are entered in the system.      *)
-- (***************************************************************************)
-- Bmax(T) ==
--   {[slot |-> t.slot, val |-> t.val] : t \in PartialBmax(T)}
procedure Bmax (T : VotedSet) {
  let partialBmaxSet ← PartialBmax T
  let result : DecreeSet :=
    voteTset.map partialBmaxSet (fun t =>
    { slot := t.slot,
      val := t.val : Decree slot value })
  return result
}

-- FreeSlots(T) ==
--   {s \in Slots : ~ \E t \in T : t.slot = s}
procedure FreeSlots (T : VotedSet) {
  let result := SlotsUNIV |>.filter (fun s =>
    voteTset.toList T |>.all (fun t => decide (t.slot ≠ s)) )
  return result
}


-- NewProposals(T) ==
--   (CHOOSE D \in SUBSET [slot : FreeSlots(T), val : Values] \ {}:
--     \A d1, d2 \in D : d1.slot = d2.slot => d1 = d2)
procedure NewProposals (T : VotedSet) {
  let freeSlotList ← FreeSlots T
  /- TLA+ `CHOOSE` is deterministic. See https://www.learntla.com/core/operators.html.
  "_TLC will always choose the `lowest` value that matches the set_",
  Here simulate `CHOOSE` by picking only the FIRST free slot with default value. -/
  let result := match freeSlotList with
    | [] => decreeSet.empty
    | s :: _ => decreeSet.insert { slot := s, val := default } decreeSet.empty
  return result
}


-- ProposeDecrees(T) ==
--   Bmax(T) \cup NewProposals(T)
procedure ProposeDecrees (T : VotedSet) {
  let bmaxSet ← Bmax T
  let newProposalsSet ← NewProposals T
  let proposeDecreesSet := decreeSet.union bmaxSet newProposalsSet
  return proposeDecreesSet
}


-- VS(S, Q) == UNION {m.voted: m \in {m \in S: m.from \in Q}}
procedure VS (S : MsgSet) (Q : quorum) {
  let filteredMsgs := msgTset.filter S (fun m =>
    match m.src with
    | MsgSrc.fromAcceptor a => member a Q
    | MsgSrc.fromProposer _ => false)
  let result := msgTset.toList filteredMsgs
    |>.foldl (fun acc m => voteTset.union acc m.voted) voteTset.empty
  return result
}


-- Phase2a(p) == \E b \in Ballots:
--   /\ ~\E m \in sent: (m.type = "2a") /\ (m.bal = b)
--   /\ \E Q \in Quorums, S \in SUBSET {m \in sent: (m.type = "1b") /\ (m.bal = b)}:
--        /\ \A a \in Q: \E m \in S: m.from = a
--        /\ Send({[type |-> "2a", from |-> p, bal |-> b, decrees |-> ProposeDecrees(VS(S, Q))]})
-- Optimization: instead of picking MsgSet (huge), pick AcceptorSet (only 2^n possibilities)
-- Then construct S by filtering 1b messages from selected acceptors
action Phase2a (p : proposer) {
  let b ← pick ballot
  let existing2a := msgTset.filter sent (fun m => m.msgType = MsgType.Phase2a ∧ m.bal = b)
  require msgTset.count existing2a = 0
  let Q ← pick quorum
  -- Get all 1b messages with this ballot
  -- Non-deterministically pick a subset of acceptors (only 2^n possibilities, much smaller than MsgSet)
  -- Construct S: filter 1b messages from selected acceptors
  let all1bMsgs := msgTset.filter sent (fun m => m.msgType = MsgType.Phase1b ∧ m.bal = b)
  let selectedAcceptors ← pick AcceptorSet
  let S := msgTset.filter all1bMsgs (fun m =>
    match m.src with
    | .fromAcceptor a => acceptorTset.contains a selectedAcceptors
    | _ => false)
  -- Check: every acceptor in Q has a 1b message in S
  let quorumCovered := AcceptorsUNIV |>.all (fun a =>
    !member a Q || (msgTset.toList S |>.any (fun m =>
      decide (m.src = MsgSrc.fromAcceptor a))))
  require quorumCovered
  let sentMsg := {
    msgType := MsgType.Phase2a,
    src := MsgSrc.fromProposer p,
    bal := b,
    decrees := ← ProposeDecrees (← VS S Q),
    /- Unused fields -/
    val := default,
    slot := default,
    voted := default }
  Send (msgTset.insert sentMsg msgTset.empty)
}


-- (***************************************************************************)
-- (* Phase 2b: If an acceptor receives a 2a message for a ballot which is    *)
-- (* the highest that it has seen, it votes for the all the message's values *)
-- (* in ballot b.                                                            *)
-- (***************************************************************************)
-- Phase2b(a) == \E m \in sent:
--   /\ m.type = "2a"
--   /\ \A m2 \in {m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.from = a}: m.bal >= m2.bal
--   /\ Send({[type |-> "2b", from |-> a, bal |-> m.bal, slot |-> d.slot, val |-> d.val]: d \in m.decrees})
action Phase2b (a : acceptor) {
  let phase2aMsgs := msgTset.filter sent (fun m => m.msgType = MsgType.Phase2a)
  let m :| m ∈ phase2aMsgs
  let prevMsgsFromA := msgTset.filter sent (fun m2 =>
    (m2.msgType = MsgType.Phase1b ∨ m2.msgType = MsgType.Phase2b) ∧ m2.src = MsgSrc.fromAcceptor a)
  /- `/\ \A m2 \in {m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.from = a}: m.bal >= m2.bal` -/
  let allPrevBallotsLeq := msgTset.toList prevMsgsFromA |>.all (fun m2 => decide (tot.le m2.bal m.bal))
  require allPrevBallotsLeq
  let replyMsgSet := decreeSet.map m.decrees (fun d =>
      { msgType := MsgType.Phase2b,
        src := MsgSrc.fromAcceptor a,
        val := d.val,
        bal := m.bal,
        slot := d.slot,
        decrees := default,
        voted := default } )
  Send replyMsgSet
}

-- invariant [sent_not_empty] msgTset.count sent < 7
set_option synthInstance.maxHeartbeats 2000000
set_option synthInstance.maxSize 2000
-- #exit
#gen_spec

-- Based on MultiPaxosUs.cfg:
-- Acceptors = {a1, a2, a3}        -> Fin 3
-- Proposers = {p1, p2}            -> Fin 2
-- Values = {v1, v2}               -> Fin 2
-- Quorums = {{a1,a2},{a1,a3},{a2,a3}} -> Fin 3
-- MaxBallot = 2                   -> 0..2, Fin 3
-- MaxSlot = 1                     -> 0..1, Fin 2
#model_check
{
  ballot := Fin 3,
  slot := Fin 2,
  value := Fin 2,
  acceptor := Fin 3,
  proposer := Fin 2,
  quorum := Fin 3,
  SlotSet := ExtTreeSet (Fin 2) compare,
  VotedSet := ExtTreeSet (Voted (Fin 3) (Fin 2) (Fin 2)) compare,
  DecreeSet := ExtTreeSet (Decree (Fin 2) (Fin 2)) compare,
  MsgSet := ExtTreeSet (Msg (Fin 2) (Fin 3) (Fin 2) (Fin 3) (Fin 2) (ExtTreeSet (Voted (Fin 3) (Fin 2) (Fin 2)) compare) (ExtTreeSet (Decree (Fin 2) (Fin 2)) compare)) compare,
  AcceptorSet := ExtTreeSet (Fin 3) compare
}
{
  one := 1,
  AcceptorsUNIV := [0, 1, 2],  -- a0, a1, a2
  -- Quorums: q0 = {a0, a1}, q1 = {a0, a2}, q2 = {a1, a2}
  member := fun a q =>
    match a.val, q.val with
    | 0, 0 => true  -- q0 contains a0
    | 1, 0 => true  -- q0 contains a1
    | 0, 1 => true
    | 2, 1 => true
    | 1, 2 => true
    | 2, 2 => true
    | _, _ => false
  SlotsUNIV := [0, 1]  -- slot 0, 1
}


end MultiPaxosUs
