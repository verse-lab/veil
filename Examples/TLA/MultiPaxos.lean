module

public import Veil

-- source: https://github.com/sachand/HistVar/blob/master/Multi-Paxos/MultiPaxosUs.tla
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
-- EXTENDS Integers, FiniteSets

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

veil module MultiPaxos

-- Ballot type: Fin (maxBallot + 1), encoding TLA+'s Ballots == 0..MaxBallot
-- (Unlike Paxos, MultiPaxos has no "no ballot" sentinel)
abbrev BallotTy (maxBallot : Nat) := Fin (maxBallot + 1)

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

-- Messages ==
--   [type : {"1a"}, bal : Ballots, from : Proposers]
--   \cup [type : {"1b"}, bal : Ballots, voted : SUBSET [...], from : Acceptors]
--   \cup [type : {"2a"}, bal : Ballots, decrees : SUBSET [...], from : Proposers]
--   \cup [type : {"2b"}, bal : Ballots, slot : Slots, val : Values, from : Acceptors]
@[veil_decl]
inductive Msg (prp ac vl blt slt vcont dcont : Type) where
  | phase1a (src : prp) (bal : blt) : Msg prp ac vl blt slt vcont dcont
  | phase1b (src : ac) (bal : blt) (voted : vcont) : Msg prp ac vl blt slt vcont dcont
  | phase2a (src : prp) (bal : blt) (decrees : dcont) : Msg prp ac vl blt slt vcont dcont
  | phase2b (src : ac) (bal : blt) (slot : slt) (val : vl) : Msg prp ac vl blt slt vcont dcont
deriving instance Veil.Enumeration for Msg

abbrev Msg.ballot (m : Msg prp ac vl blt slt vcont dcont) : blt :=
  match m with
  | .phase1a _ bal => bal
  | .phase1b _ bal _ => bal
  | .phase2a _ bal _ => bal
  | .phase2b _ bal _ _ => bal

abbrev MultiPaxosMsg (prp ac vl : Type) (maxBallot : Nat) (slt vcont dcont : Type) :=
  Msg prp ac vl (BallotTy maxBallot) slt vcont dcont

abbrev MultiPaxosVoted (maxBallot : Nat) (slot value : Type) :=
  Voted (BallotTy maxBallot) slot value

-- CONSTANTS Acceptors, Values, Quorums, Proposers, MaxBallot, MaxSlot
type acceptor
type proposer
type value
type quorum
type slot

param maxBallot : Nat

type VotedSet
type DecreeSet
type MsgSet
type AcceptorSet

instantiate voteSet : TSet (MultiPaxosVoted maxBallot slot value) VotedSet
instantiate decSet : TSet (Decree slot value) DecreeSet
instantiate msgSet : TSet (MultiPaxosMsg proposer acceptor value maxBallot slot VotedSet DecreeSet) MsgSet
instantiate acSet : TSet acceptor AcceptorSet

-- ASSUME QuorumAssumption
instantiate pm : PaxosMember acceptor quorum

-- immutable relation member (A : acceptor) (Q : quorum)
-- PaxosMember acceptor quorum
open PaxosMember

-- VARIABLES sent
individual sent : MsgSet

-- Slots == 0..MaxSlot (provided as a list for iteration in FreeSlots)
-- immutable individual SlotsUNIV : List slot
instantiate slotEnumerable : Veil.Enumeration slot

#gen_state

assumption [quorum_intersection]
  ∀ (q1 q2 : quorum), ∃ (r : acceptor), member r q1 ∧ member r q2

-- Init == /\ sent = {}
after_init {
  sent := msgSet.empty
}

-- Send(m) == sent' = sent \cup m
procedure Send (m : MsgSet) {
  sent := msgSet.union m sent
}

-- (***************************************************************************)
-- (* Phase 1a: Executed by a proposer, it selects a ballot number on which   *)
-- (* Phase 1a has never been initiated. This number is sent to any set of    *)
-- (* acceptors which contains at least one quorum from Quorums. Trivially it *)
-- (* can be broadcasted to all Acceptors. For safety, any subset of          *)
-- (* Acceptors would suffice. For liveness, a subset containing at least one *)
-- (* Quorum is needed.                                                       *)
-- (***************************************************************************)

-- TODO need singleton

-- Phase1a(p) == \E b \in Ballots: Send({[type |-> "1a", from |-> p, bal |-> b]})
action Phase1a (p : proposer) {
  let b ← pick (BallotTy maxBallot)
  Send (msgSet.ofList [(.phase1a p b)])
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

-- voteds(a) == {[bal |-> m.bal, slot |-> m.slot, val |-> m.val]:
--               m \in {m \in sent: m.type = "2b" /\ m.from = a}}
ghost function voteds (a : acceptor) : VotedSet :=
  msgSet.filterMap sent fun m =>
    match m with
    | .phase2b src bal slot val => if src = a then some { bal := bal, slot := slot, val := val } else none
    | _ => none

-- PartialBmax(T) ==
--   {t \in T : \A t1 \in T : t1.slot = t.slot => t1.bal =< t.bal}
ghost function PartialBmax (T : VotedSet) : VotedSet :=
  voteSet.filter T fun t =>
    decide <|
      ∀ t1 : { t1 // t1 ∈ T }, t1.val.slot = t.slot → t1.val.bal ≤ t.bal

-- Ghost relation: all previous 1b/2b messages from acceptor a have ballot < b
-- Encodes: \A m2 \in {m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.from = a}: b > m2.bal
ghost relation allPrevBallotsLower (a : acceptor) (b : BallotTy maxBallot) :=
  ∀ m : { m // m ∈ sent }, (match m.val with
    | .phase1b src bal _ => decide $ src = a → bal < b
    | .phase2b src bal _ _ => decide $ src = a → bal < b
    | _ => true) = true

-- Phase1b(a) == \E m \in sent:
--   /\ m.type = "1a"
--   /\ \A m2 \in {m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.from = a}: m.bal > m2.bal
--   /\ Send({[type |-> "1b", from |-> a, bal |-> m.bal, voted |-> PartialBmax(voteds(a))]})
action Phase1b (a : acceptor) {
  let m : { m // m ∈ sent } :| (match m.val with
    | .phase1a _ _ => true
    | _ => false) = true
  let b := m.val.ballot
  require allPrevBallotsLower a b
  let votedSet := voteds a
  let partialBmaxSet := PartialBmax votedSet
  Send (msgSet.ofList [(.phase1b a b partialBmaxSet)])
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
ghost function Bmax (T : VotedSet) : DecreeSet :=
  voteSet.map (PartialBmax T) fun t =>
    { slot := t.slot, val := t.val : Decree slot value }

-- FreeSlots(T) ==
--   {s \in Slots : ~ \E t \in T : t.slot = s}
ghost function FreeSlots (T : VotedSet) : List slot :=
  slotEnumerable.allValues.filter fun s =>
    decide <| ¬ ∃ t : { t // t ∈ T }, t.val.slot = s

-- NewProposals(T) ==
--   (CHOOSE D \in SUBSET [slot : FreeSlots(T), val : Values] \ {}:
--     \A d1, d2 \in D : d1.slot = d2.slot => d1 = d2)
ghost function NewProposals (T : VotedSet) : DecreeSet :=
  let freeSlotList := FreeSlots T
  /- TLA+ `CHOOSE` is deterministic. See https://www.learntla.com/core/operators.html.
  "_TLC will always choose the `lowest` value that matches the set_",
  Here simulate `CHOOSE` by picking only the FIRST free slot with default value. -/
  match freeSlotList with
  | [] => decSet.empty
  | s :: _ => decSet.ofList [{ slot := s, val := default }]

-- ProposeDecrees(T) ==
--   Bmax(T) \cup NewProposals(T)
ghost function ProposeDecrees (T : VotedSet) : DecreeSet :=
  decSet.union (Bmax T) (NewProposals T)

-- TODO need iterated union

-- VS(S, Q) == UNION {m.voted: m \in {m \in S: m.from \in Q}}
ghost function VS (S : MsgSet) (Q : quorum) : VotedSet :=
  -- NOTE: Here we implicitly require that S only contains `1b` messages,
  -- due to some typing issue
  let sub := msgSet.filter S fun m =>
    match m with
    | .phase1b src _ _ => member src Q
    | _ => false
  msgSet.toList sub |>.foldl (init := voteSet.empty) fun acc m =>
    match m with
    | .phase1b _ _ voted => voteSet.union acc voted
    | _ => acc

-- Ghost relation: quorum Q is covered by 1b messages in S
-- Encodes: \A a \in Q: \E m \in S: m.from = a
ghost relation quorumCovered (Q : quorum) (S : MsgSet) :=
  ∀ a, member a Q → ∃ m : { m // m ∈ S }, (match m.val with
    | .phase1b src .. => decide $ src = a
    | _ => false) = true

-- Phase2a(p) == \E b \in Ballots:
--   /\ ~\E m \in sent: (m.type = "2a") /\ (m.bal = b)
--   /\ \E Q \in Quorums, S \in SUBSET {m \in sent: (m.type = "1b") /\ (m.bal = b)}:
--        /\ \A a \in Q: \E m \in S: m.from = a
--        /\ Send({[type |-> "2a", from |-> p, bal |-> b, decrees |-> ProposeDecrees(VS(S, Q))]})

/-
-- Optimization: instead of picking MsgSet (huge), pick AcceptorSet (only 2^n possibilities)
action Phase2a (p : proposer) {
  let b ← pick (BallotTy maxBallot)

  -- ~\E m \in sent: (m.type = "2a") /\ (m.bal = b)
  require ¬ ∃ msg : { m // m ∈ sent },
    (match msg.val with
      | .phase2a _ bal _ => decide $ bal = b
      | _ => false) = true

  let Q ← pick quorum

  /- Instead of picking S from the set of all subsets of messages,
    we pick a subset of acceptors, and construct S by filtering messages from those
    acceptors. As we only care about condition `m.from = a`.
    This reduces the non-deterministic choices to 2^|acceptors|.  -/
  let selectedAcceptors ← pick AcceptorSet
  let S := msgSet.filter sent (fun m =>
    match m with
    | .phase1b src bal _ => bal == b && acSet.contains src selectedAcceptors
    | _ => false)

  require quorumCovered Q S

  let proposeDecreesSet := ProposeDecrees (VS S Q)
  Send (msgSet.ofList [(.phase2a p b proposeDecreesSet)])
}
-/

-- Authentic translation: pick S directly from SUBSET of filtered 1b messages
action Phase2a (p : proposer) {
  let b ← pick (BallotTy maxBallot)

  -- ~\E m \in sent: (m.type = "2a") /\ (m.bal = b)
  require ¬ ∃ msg : { m // m ∈ sent },
    (match msg.val with
      | .phase2a _ bal _ => decide $ bal = b
      | _ => false) = true

  let Q ← pick quorum

  -- S \in SUBSET {m \in sent: (m.type = "1b") /\ (m.bal = b)}
  let filtered1b := msgSet.filter sent fun m =>
    match m with
    | .phase1b _ bal _ => decide $ bal = b
    | _ => false
  let S :| msgSet.isSubset S filtered1b

  -- \A a \in Q: \E m \in S: m.from = a
  require quorumCovered Q S

  let proposeDecreesSet := ProposeDecrees (VS S Q)
  Send (msgSet.insert (.phase2a p b proposeDecreesSet) msgSet.empty)
}

-- (***************************************************************************)
-- (* Phase 2b: If an acceptor receives a 2a message for a ballot which is    *)
-- (* the highest that it has seen, it votes for all the message's values     *)
-- (* in ballot b.                                                            *)
-- (***************************************************************************)

-- Ghost relation: all previous 1b/2b messages from acceptor a have ballot ≤ b
-- Encodes: \A m2 \in {m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.from = a}: b >= m2.bal
ghost relation allPrevBallotsLeq (a : acceptor) (b : BallotTy maxBallot) :=
  ∀ m : { m // m ∈ sent }, (match m.val with
    | .phase1b src bal _ => decide $ src = a → bal ≤ b
    | .phase2b src bal _ _ => decide $ src = a → bal ≤ b
    | _ => true) = true

-- Phase2b(a) == \E m \in sent:
--   /\ m.type = "2a"
--   /\ \A m2 \in {m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.from = a}: m.bal >= m2.bal
--   /\ Send({[type |-> "2b", from |-> a, bal |-> m.bal, slot |-> d.slot, val |-> d.val]: d \in m.decrees})
action Phase2b (a : acceptor) {
  let m : { m // m ∈ sent } :| (match m.val with
    | .phase2a .. => true
    | _ => false) = true
  let b := m.val.ballot
  require allPrevBallotsLeq a b
  let decrees := match m.val with
    | .phase2a _ _ d => d
    | _ => default  -- dead branch
  let replyMsgSet := decSet.map decrees fun d =>
    Msg.phase2b a b d.slot d.val
  Send replyMsgSet
}

-- VotedForIn(a, b, s, v) ==
--   \E m \in sent : /\ m.type = "2b" /\ m.bal = b /\ m.slot = s /\ m.val = v /\ m.from = a
ghost relation VotedForIn (a : acceptor) (b : BallotTy maxBallot) (s : slot) (v : value) :=
  msgSet.contains (.phase2b a b s v) sent

-- ChosenIn(b, s, v) == \E Q \in Quorums : \A a \in Q : VotedForIn(a, b, s, v)
ghost relation ChosenIn (b : BallotTy maxBallot) (s : slot) (v : value) :=
  ∃ (Q : quorum), ∀ a, member a Q → VotedForIn a b s v

-- Chosen(v, s) == \E b \in Ballots : ChosenIn(b, s, v)
ghost relation Chosen (v : value) (s : slot) :=
  ∃ b, ChosenIn b s v

-- Consistency == \A v1, v2 \in Values, s \in Slots : Chosen(v1, s) /\ Chosen(v2, s) => (v1 = v2)
invariant [consistency]
  ∀ (v1 v2 : value) (s : slot), (Chosen v1 s ∧ Chosen v2 s) → (v1 = v2)

#gen_spec
#gen_executable

-- #model_check compiled
-- {
--   slot := Fin 3,
--   value := Fin 2,
--   acceptor := Fin 3,
--   proposer := Fin 2,
--   quorum := Fin 3,
--   maxBallot := 2,
--   VotedSet := OrdList _,
--   DecreeSet := OrdList _,
--   MsgSet := OrdList _,
--   AcceptorSet := OrdList _
-- }

end MultiPaxos
