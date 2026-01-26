------------------------------- MODULE MultiPaxosUs -------------------------------
(***************************************************************************)
(* This is a TLA+ specification of the MultiPaxos Consensus algorithm,     *)
(* described in                                                            *)
(*                                                                         *)
(*  The Part-Time Parliament:                                              *)
(*  http://research.microsoft.com/en-us/um/people/lamport/pubs/lamport-paxos.pdf *)
(*                                                                         *)
(* and a TLAPS-checked proof of its correctness. This is an extension of   *)
(* the proof of Basic Paxos found in TLAPS examples directory.             *)
(***************************************************************************)
EXTENDS Integers
\* TLAPS

CONSTANTS Acceptors, Values, Quorums, Proposers, MaxBallot, MaxSlot

ASSUME QuorumAssumption ==
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

Ballots == 0..MaxBallot
Slots == 0..MaxSlot

VARIABLES sent

vars == <<sent>>

Send(m) == sent' = sent \cup m

None == CHOOSE v : v \notin Values

Init == /\ sent = {}

(***************************************************************************)
(* Phase 1a: Executed by a proposer, it selects a ballot number on which   *)
(* Phase 1a has never been initiated. This number is sent to any set of    *)
(* acceptors which contains at least one quorum from Quorums. Trivially it *)
(* can be broadcasted to all Acceptors. For safety, any subset of          *)
(* Acceptors would suffice. For liveness, a subset containing at least one *)
(* Quorum is needed.                                                       *)
(***************************************************************************)
Phase1a(p) == \E b \in Ballots: Send({[type |-> "1a", from |-> p, bal |-> b]})
              
(***************************************************************************)
(* Phase 1b: If an acceptor receives a 1a message with ballot b greater    *)
(* than that of any 1a message to which it has already responded, then it  *)
(* responds to the request with a promise not to accept any more proposals *)
(* for ballots numbered less than b; otherwise it sends a preempt to the   *)
(* proposer telling the greater ballot.                                    *)
(* In case of a 1b reply, the acceptor writes a mapping in S -> B \times V *)
(* This This mapping reveals for each slot, the value that the acceptor    *)
(* most recently (i.e., highest ballot) voted on, if any.                  *)
(***************************************************************************)
PartialBmax(T) ==
  {t \in T : \A t1 \in T : t1.slot = t.slot => t1.bal =< t.bal}

voteds(a) == {[bal |-> m.bal, slot |-> m.slot, val |-> m.val]: m \in {m \in sent: m.type = "2b" /\ m.from = a}}

Phase1b(a) == \E m \in sent:
  /\ m.type = "1a"
  /\ \A m2 \in {m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.from = a}: m.bal > m2.bal
  /\ Send({[type |-> "1b", from |-> a, bal |-> m.bal, voted |-> PartialBmax(voteds(a))]})       

(***************************************************************************)
(* Phase 2a: If the proposer receives a response to its 1b message (for    *)
(* ballot b) from a quorum of acceptors, then it sends a 2a message to all *)
(* acceptors for a proposal in ballot b. Per slot received in the replies, *)
(* the proposer finds out the value most recently (i.e., highest ballot)   *)
(* voted by the acceptors in the received set. Thus a mapping in S -> V    *)
(* is created. This mapping along with the ballot that passed Phase 1a is  *)
(* propogated to again, any subset of Acceptors - Hopefully to one         *)
(* containing at least one Quorum.                                         *)
(* Bmax            creates the desired mapping from received replies.      *)
(* NewProposals    instructs how new slots are entered in the system.      *)
(***************************************************************************)
Bmax(T) ==
  {[slot |-> t.slot, val |-> t.val] : t \in PartialBmax(T)}

FreeSlots(T) ==
  {s \in Slots : ~ \E t \in T : t.slot = s}

\* Original: CHOOSE returns a single D (deterministic)
\* NewProposals(T) ==
\*   (CHOOSE D \in SUBSET [slot : FreeSlots(T), val : Values] \ {{}}:
\*     \A d1, d2 \in D : d1.slot = d2.slot => d1 = d2)

\* Here, we added Exception handle and modify the mistake (from {} to {{}}).
\* Without Exception handle, TLC will throw an error.
NewProposals(T) ==
  IF FreeSlots(T) = {} THEN {}
  ELSE (CHOOSE D \in SUBSET [slot : FreeSlots(T), val : Values] \ {{}}:
          \A d1, d2 \in D : d1.slot = d2.slot => d1 = d2)

ProposeDecrees(T) ==
  Bmax(T) \cup NewProposals(T)

\* \* Modified: AllNewProposals returns the set of ALL valid D (for non-deterministic exploration)
\* AllNewProposals(T) ==
\*   { D \in SUBSET [slot : FreeSlots(T), val : Values] \ {{}} :
\*     \A d1, d2 \in D : d1.slot = d2.slot => d1 = d2 }

VS(S, Q) == UNION {m.voted: m \in {m \in S: m.from \in Q}}

\* Original Phase2a (deterministic NewProposals):
Phase2a(p) == \E b \in Ballots:
  /\ ~\E m \in sent: (m.type = "2a") /\ (m.bal = b)
  /\ \E Q \in Quorums, S \in SUBSET {m \in sent: (m.type = "1b") /\ (m.bal = b)}:
       /\ \A a \in Q: \E m \in S: m.from = a
       /\ Send({[type |-> "2a", from |-> p, bal |-> b, decrees |-> ProposeDecrees(VS(S, Q))]})

\* Modified Phase2a: uses \E to explore all possible D in AllNewProposals
\* Phase2a(p) == \E b \in Ballots:
\*   /\ ~\E m \in sent: (m.type = "2a") /\ (m.bal = b)
\*   /\ \E Q \in Quorums, S \in SUBSET {m \in sent: (m.type = "1b") /\ (m.bal = b)}:
\*        /\ \A a \in Q: \E m \in S: m.from = a
\*        /\ LET T == VS(S, Q) IN
\*           \E D \in AllNewProposals(T):
\*             Send({[type |-> "2a", from |-> p, bal |-> b, decrees |-> Bmax(T) \cup D]})

(***************************************************************************)
(* Phase 2b: If an acceptor receives a 2a message for a ballot which is    *)
(* the highest that it has seen, it votes for the all the message's values *)
(* in ballot b.                                                            *)
(***************************************************************************)
Phase2b(a) == \E m \in sent:
  /\ m.type = "2a"
  /\ \A m2 \in {m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.from = a}: m.bal >= m2.bal
  /\ Send({[type |-> "2b", from |-> a, bal |-> m.bal, slot |-> d.slot, val |-> d.val]: d \in m.decrees})
    
Next == \/ \E p \in Proposers : Phase1a(p) 
        \/ \E p \in Proposers : Phase2a(p)
        \/ \E a \in Acceptors : Phase1b(a) 
        \/ \E a \in Acceptors : Phase2b(a)

Spec == Init /\ [][Next]_vars       
-----------------------------------------------------------------------------
(***************************************************************************)
(* How a value is chosen:                                                  *)
(*                                                                         *)
(* This spec does not contain any actions in which a value is explicitly   *)
(* chosen (or a chosen value learned).  What it means for a value to be    *)
(* chosen is defined by the operator Chosen, where Chosen(v, s) means that *)
(* v has been chosen for slot s.                                           *)
(***************************************************************************)
VotedForIn(a, b, s, v) ==
  \E m \in sent : /\ m.type = "2b"
                  /\ m.bal = b
                  /\ m.slot = s
                  /\ m.val = v
                  /\ m.from = a

ChosenIn(b, s, v) == \E Q \in Quorums :
                     \A a \in Q : VotedForIn(a, b, s, v)

Chosen(v, s) == \E b \in Ballots : ChosenIn(b, s, v)

(***************************************************************************)
(* The consistency condition that a consensus algorithm must satisfy is    *)
(* the invariance of the following state predicate Consistency.            *)
(***************************************************************************)
Consistency == \A v1, v2 \in Values, s \in Slots : Chosen(v1, s) /\ Chosen(v2, s) => (v1 = v2)
-----------------------------------------------------------------------------
(***************************************************************************)
(* This section of the spec defines the invariant Inv.                     *)
(***************************************************************************)
Messages ==      [type : {"1a"}, bal : Ballots, from : Proposers]
            \cup [type : {"1b"}, bal : Ballots, voted : SUBSET [bal : Ballots, slot : Slots, val : Values], from : Acceptors]
            \cup [type : {"2a"}, bal : Ballots, decrees : SUBSET [slot : Slots, val : Values], from : Proposers]
            \cup [type : {"2b"}, bal : Ballots, slot : Slots, val : Values, from : Acceptors]

TypeOK == sent \in SUBSET Messages

(***************************************************************************)
(* WontVoteIn(a, b, s) is a predicate that implies that a has not voted    *)
(* and never will vote in ballot b wrt slot s.                             *)
(***************************************************************************)                                       
WontVoteIn(a, b, s) == /\ \A v \in Values : ~ VotedForIn(a, b, s, v)
                       /\ \E m \in sent: m.type \in {"1b", "2b"} /\ m.from = a /\ m.bal > b

(***************************************************************************)
(* The predicate SafeAt(v, b, s) implies that no value other than perhaps  *)
(* v has been or ever will be chosen in any ballot numbered less than b    *)
(* for slot s.                                                             *)
(***************************************************************************)                   
SafeAt(b, s, v) == 
  \A c \in 0..(b-1) :
    \E Q \in Quorums : 
      \A a \in Q : VotedForIn(a, c, s, v) \/ WontVoteIn(a, c, s)

(***************************************************************************)
(* The following lemma is an immediate consequence of the assumption.      *)
(***************************************************************************)
\* LEMMA QuorumNonEmpty == \A Q \in Quorums : Q # {}
\* BY QuorumAssumption

\* LEMMA NPC ==
\*   \A S : /\ NewProposals(S) \in (SUBSET [slot : FreeSlots(S), val : Values]) \ {}
\*          /\ \A t1, t2 \in NewProposals(S) : t1.slot = t2.slot => t1 = t2
\*          /\ ~ \E t1 \in Bmax(S), t2 \in NewProposals(S) : t1.slot = t2.slot
\*   <1> SUFFICES ASSUME NEW S
\*                PROVE  /\ NewProposals(S) \in (SUBSET [slot : FreeSlots(S), val : Values]) \ {}
\*                       /\ \A t1, t2 \in NewProposals(S) : t1.slot = t2.slot => t1 = t2
\*                       /\ ~ \E t1 \in Bmax(S), t2 \in NewProposals(S) : t1.slot = t2.slot
\*     OBVIOUS
\*   <1>0. \E T \in (SUBSET [slot : FreeSlots(S), val : Values]) \ {} :
\*       \A t1, t2 \in T : t1.slot = t2.slot => t1 = t2
\*     BY DEF FreeSlots
\*   <1>1. NewProposals(S) \in (SUBSET [slot : FreeSlots(S), val : Values]) \ {}
\*     BY <1>0 DEF NewProposals
\*   <1>2. \A t1, t2 \in NewProposals(S) : t1.slot = t2.slot => t1 = t2
\*     BY <1>0 DEF NewProposals
\*   <1>3. ~ \E t1 \in Bmax(S), t2 \in ([slot : FreeSlots(S), val : Values] \ {}) : t1.slot = t2.slot
\*     BY DEF Bmax, PartialBmax, FreeSlots
\*   <1>4. QED
\*     BY <1>1, <1>2, <1>3

\* MsgInv ==
\*   \A m \in sent : 
\*     /\ (m.type = "1b") =>
\*          /\ \A r \in m.voted:
\*               /\ VotedForIn(m.from, r.bal, r.slot, r.val)
\*               /\ \A b \in r.bal+1..m.bal-1, v \in Values: ~VotedForIn(m.from, b, r.slot, v)
\*          /\ \A s \in Slots, b \in 0..m.bal-1, v \in Values: VotedForIn(m.from, b, s, v) =>
\*               \E r \in m.voted: r.slot = s /\ r.bal >= b
\*     /\ (m.type = "2a") => 
\*          /\ \A d \in m.decrees : SafeAt(m.bal, d.slot, d.val)
\*          /\ \A d1,d2 \in m.decrees : d1.slot = d2.slot => d1 = d2
\*          /\ \A ma \in sent : (ma.type = "2a") /\ (ma.bal = m.bal)
\*                                 => (ma = m)
\*     /\ (m.type = "2b") => 
\*          /\ \E ma \in sent : /\ ma.type = "2a"
\*                              /\ ma.bal  = m.bal
\*                              /\ \E d \in ma.decrees: d.slot = m.slot /\ d.val = m.val

\* (***************************************************************************)
\* (* The following three lemmas are simple consequences of the definitions.  *)
\* (***************************************************************************)
\* LEMMA VotedInv == 
\*         MsgInv /\ TypeOK => 
\*             \A a \in Acceptors, v \in Values, b \in Ballots, s \in Slots :
\*                 VotedForIn(a, b, s, v) => SafeAt(b, s, v)
\* BY DEF VotedForIn, MsgInv, Messages, TypeOK

\* LEMMA VotedOnce == 
\*         MsgInv => \A a1, a2 \in Acceptors, b \in Ballots, v1, v2 \in Values, s \in Slots :
\*                        VotedForIn(a1, b, s, v1) /\ VotedForIn(a2, b, s, v2) => (v1 = v2)
\* BY DEF MsgInv, VotedForIn

\* LEMMA VotedUnion ==
\*   MsgInv /\ TypeOK => \A m1, m2 \in sent: 
\*     /\ m1.type = "1b"
\*     /\ m2.type = "1b"
\*     => \A d1 \in m1.voted, d2 \in m2.voted :
\*         /\ d1.bal = d2.bal
\*         /\ d1.slot = d2.slot
\*         => d1.val = d2.val
\*   <1> SUFFICES ASSUME MsgInv /\ TypeOK,
\*                       NEW m1 \in sent, NEW m2 \in sent,
\*                       /\ m1.type = "1b"
\*                       /\ m2.type = "1b",
\*                       NEW d1 \in m1.voted, NEW d2 \in m2.voted,
\*                       d1.bal = d2.bal, d1.slot = d2.slot
\*                PROVE  d1.val = d2.val
\*     OBVIOUS
\*     <1>1. VotedForIn(m1.from, d1.bal, d1.slot, d1.val)
\*       BY DEF MsgInv
\*     <1>2. VotedForIn(m2.from, d2.bal, d2.slot, d2.val)
\*       BY DEF MsgInv
\*   <1> QED BY <1>1, <1>2, VotedOnce DEF TypeOK, Messages

\* LEMMA VotedaVoted == \A a, b, s, v:
\*   VotedForIn(a, b, s, v) <=> \E r \in voteds(a): r.bal = b /\ r.slot = s /\ r.val = v
\* BY DEF voteds, VotedForIn

\* AXIOM PBV1 == \A S \in SUBSET [bal: Ballots, slot: Slots, val: Values]: \A r \in S: \E r2 \in PartialBmax(S): r.slot = r2.slot /\ r.bal =< r2.bal
\* AXIOM PBV2 == \A S \in SUBSET [bal: Ballots, slot: Slots, val: Values], s \in Slots: (\E r \in S: r.slot = s) <=> (\E r \in PartialBmax(S): r.slot = s)
\* LEMMA PartialBmaxVoted == TypeOK => \A a \in Acceptors, s \in Slots:
\*   /\ voteds(a) \in SUBSET [bal : Ballots, slot : Slots, val : Values]
\*   /\ (\E r \in voteds(a): r.slot = s) <=> (\E r \in PartialBmax(voteds(a)): r.slot = s)
\*   /\ PartialBmax(voteds(a)) \subseteq voteds(a)
\*   /\ \A r \in voteds(a): \E r2 \in PartialBmax(voteds(a)): r.slot = r2.slot /\ r.bal =< r2.bal
\*   <1> SUFFICES ASSUME NEW a \in Acceptors, NEW s \in Slots, TypeOK
\*                PROVE  /\ voteds(a) \in SUBSET [bal : Ballots, slot : Slots, val : Values]
\*                       /\ (\E r \in voteds(a): r.slot = s) <=> (\E r \in PartialBmax(voteds(a)): r.slot = s)
\*                       /\ PartialBmax(voteds(a)) \subseteq voteds(a)
\*                       /\ \A r \in voteds(a): \E r2 \in PartialBmax(voteds(a)): r.slot = r2.slot /\ r.bal =< r2.bal
\*     OBVIOUS
\*   <1> USE DEF Ballots, Slots
\*   <1>0. voteds(a) \in SUBSET [bal : Ballots, slot : Slots, val : Values]
\*     BY DEF voteds, TypeOK, Messages
\*   <1>1. (\E r \in voteds(a): r.slot = s) <=> (\E r \in PartialBmax(voteds(a)): r.slot = s)
\*     BY PBV2, <1>0
\*   <1>2. PartialBmax(voteds(a)) \subseteq voteds(a)
\*     BY DEF PartialBmax, voteds
\*   <1>3. \A r \in voteds(a), s2 \in Slots: r.slot = s2 =>
\*             (\E r2 \in PartialBmax(voteds(a)): r2.slot = s2 /\ r.bal =< r2.bal)
\*     BY PBV1, <1>0
\* (*
\*     <2> SUFFICES ASSUME NEW r \in voteds(a), NEW s2 \in Slots,
\*                         r.slot = s2
\*                  PROVE  \E r2 \in PartialBmax(voteds(a)): r2.slot = s2 /\ r.bal =< r2.bal
\*       OBVIOUS
\*     <2>0. PICK r2 \in voteds(a): r2.slot = s2 => r.bal =< r2.bal BY <1>0
\*     <2>1. \A t \in voteds(a): (\A t2 \in voteds(a): t2.slot = t.slot => t2.bal =< t.bal) <=> t \in PartialBmax(voteds(a))
\*           BY <1>0 DEF PartialBmax
\*     <2>2. r2 \in PartialBmax(voteds(a)) BY <2>0, <2>1, <1>0, <1>2
\*     <2> QED BY <2>1, <1>0, <1>2*)
\*   <1> QED
\*     BY <1>0, <1>1, <1>2, <1>3
\* (***************************************************************************)
\* (* Inv is the complete inductive invariant.                                *)
\* (***************************************************************************)
\* Inv == TypeOK /\ MsgInv

\* LEMMA Phase1aVotedForInv ==
\*   TypeOK =>
\*   \A p \in Proposers : Phase1a(p) =>
\*                             \A aa \in Acceptors, bb \in Ballots, vv \in Values, ss \in Slots :
\*                               VotedForIn(aa, bb, ss, vv) <=> VotedForIn(aa, bb, ss, vv)'
\* BY DEF VotedForIn, Send, TypeOK, Messages, Phase1a

\* LEMMA Phase1bVotedForInv ==
\*   TypeOK =>
\*   \A a \in Acceptors : Phase1b(a) =>
\*                             \A aa \in Acceptors, bb \in Ballots, vv \in Values, ss \in Slots :
\*                               VotedForIn(aa, bb, ss, vv) <=> VotedForIn(aa, bb, ss, vv)'
\* BY DEF VotedForIn, Send, TypeOK, Messages, Phase1b

\* LEMMA Phase2aMsg == \A p \in Proposers: Phase2a(p) => \A m \in sent' \ sent: m.type = "2a"
\* <1> SUFFICES ASSUME NEW p \in Proposers, Phase2a(p)  PROVE \A m \in sent' \ sent: m.type = "2a"
\*     OBVIOUS
\*   <1>1. PICK b \in Ballots, Q \in Quorums, S \in SUBSET sent:
\*           /\ ~ \E m2 \in sent: m2.type = "2a" /\ m2.bal = b
\*           /\ S \in SUBSET {m2 \in sent: (m2.type = "1b") /\ (m2.bal = b)}
\*           /\\A a \in Q: \E m2\in S: m2.from = a
\*           /\Send({[type |-> "2a", bal |-> b, from |-> p, decrees |-> ProposeDecrees(VS(S, Q))]})
\*       BY DEF Phase2a
\* <1> QED BY <1>1 DEF Send

\* LEMMA Phase2aVotedForInv == TypeOK => \A p \in Proposers: Phase2a(p) => \A a \in Acceptors, b \in Ballots, s \in Slots, v \in Values:
\*                               VotedForIn(a, b, s, v) <=> VotedForIn(a, b, s, v)'
\* BY Phase2aMsg DEF VotedForIn,
\* Send, TypeOK, Messages, Phase2a
\* -----------------------------------------------------------------------------
\* (***************************************************************************)
\* (* The following lemma shows that (the invariant implies that) the         *)
\* (* predicate SafeAt(v, b,s) is stable, meaning that once it becomes true,  *)
\* (* it remains true throughout the rest of the excecution.                  *)
\* (***************************************************************************)
\* LEMMA SafeAtStable == Inv /\ Next => \A b \in Ballots, s \in Slots, v \in Values:
\*                         SafeAt(b, s, v) => SafeAt(b, s, v)'
\* <1> SUFFICES ASSUME Inv, Next, NEW b \in Ballots, NEW s \in Slots, NEW v \in Values, SafeAt(b, s, v)
\*              PROVE  SafeAt(b, s, v)'
\*     OBVIOUS
\* <1> USE DEF Send, Inv, Ballots
\* <1>1. CASE \E p \in Proposers: Phase1a(p)  BY <1>1 DEF SafeAt, Phase1a, VotedForIn, WontVoteIn
\* <1>2. CASE \E a \in Acceptors: Phase1b(a)
\*       BY <1>2, QuorumAssumption DEF TypeOK, SafeAt, WontVoteIn, VotedForIn, Phase1b
\* <1>3. ASSUME NEW p \in Proposers, Phase2a(p)  PROVE SafeAt(b, s, v)'
\*   <2>1. \A a \in Acceptors, b2 \in Ballots, s2 \in Slots: WontVoteIn(a, b2, s2) <=> WontVoteIn(a, b2, s2)'
\*         BY <1>3, Phase2aMsg, Phase2aVotedForInv DEF WontVoteIn, Send, Phase2a
\*   <2> QED BY <2>1, QuorumAssumption, Phase2aVotedForInv, <1>3 DEF SafeAt
\* <1>4. ASSUME NEW a \in Acceptors, Phase2b(a)  PROVE SafeAt(b, s, v)'
\*   <2>1. PICK m \in sent: Phase2b(a)!(m)  BY <1>4 DEF Phase2b
\*   <2>2 \A a2 \in Acceptors, b2 \in Ballots, s2 \in Slots, v2 \in Values :
\*           VotedForIn(a2, b2, s2, v2) => VotedForIn(a2, b2, s2, v2)'
\*     BY <2>1 DEF TypeOK, VotedForIn
\*   <2>4. ASSUME NEW a2 \in Acceptors, NEW b2 \in Ballots, NEW s2 \in Slots,
\*                WontVoteIn(a2, b2, s2), NEW v2 \in Values
\*         PROVE  ~VotedForIn(a2, b2, s2, v2)'
\*     <3>1. PICK m1 \in sent: m1.type \in {"1b", "2b"} /\ m1.from = a2 /\ m1.bal > b2
\*       BY <2>4 DEF WontVoteIn
\*     <3>2. a2 = a => b2 # m.bal
\*       BY <2>1, <2>4, <3>1, a2 = a => m.bal >= m1.bal DEF TypeOK, Messages
\*     <3>3. a2 # a => ~VotedForIn(a2, b2, s2, v2)'
\*       BY <2>1, <2>4 DEF WontVoteIn, VotedForIn
\*     <3>. QED
\*       BY <2>1, <2>2, <2>4, <3>2, <3>3 DEF Phase2b, VotedForIn, WontVoteIn, TypeOK, Messages, Send
\*   <2>5 \A a2 \in Acceptors, b2 \in Ballots, s2 \in Slots : WontVoteIn(a2, b2, s2) => WontVoteIn(a2, b2, s2)'
\*     BY <2>1, <2>4 DEF WontVoteIn, Send
\*   <2> QED
\*     BY <2>2, <2>5, QuorumAssumption DEF SafeAt
\* <1> QED BY <1>1, <1>2, <1>3, <1>4 DEF Next

\* THEOREM Invariant == Spec => []Inv
\* <1> USE DEF Ballots, Slots
\* <1>1. Init => Inv
\*   BY DEF Init, Inv, TypeOK, MsgInv, VotedForIn
\* <1>2. Inv /\ [Next]_vars => Inv'
\*   <2> SUFFICES ASSUME Inv,
\*                       [Next]_vars
\*                PROVE  Inv'
\*     OBVIOUS
\*   <2> USE DEF Inv
\*   <2>1. CASE Next
\*   <3>1. TypeOK'
\*     <4>1. ASSUME NEW p \in Proposers, Phase1a(p)  PROVE TypeOK'
\*       <5>1. PICK b \in Ballots: Phase1a(p)!(b)  BY <4>1 DEF Phase1a
\*       <5>2. sent' \ sent \subseteq Messages  BY <5>1 DEF TypeOK, Send, Messages
\*       <5> QED BY <5>1, <5>2 DEF TypeOK, Send
\*     <4>2. ASSUME NEW p \in Proposers, Phase2a(p)  PROVE TypeOK'
\*       <5>1. PICK b \in Ballots, Q \in Quorums, S \in SUBSET sent:
\*                 /\ S \in SUBSET {m \in sent: (m.type = "1b") /\ (m.bal = b)}
\*                 /\ \A a \in Q: \E m \in S: m.from = a
\*                 /\ Send({[type |-> "2a", from |-> p, bal |-> b,
\*                      decrees |-> ProposeDecrees(VS(S, Q))]})  BY <4>2 DEF Phase2a
\*       <5>2. FreeSlots(VS(S, Q)) \subseteq Slots  BY <5>1 DEF FreeSlots, TypeOK, Messages, VS
\*       <5>3. PartialBmax(VS(S, Q)) \subseteq [bal: Ballots, slot: Slots, val: Values]
\*             BY <5>1 DEF PartialBmax, TypeOK, Messages, VS
\*       <5>4. /\ NewProposals(VS(S, Q)) \subseteq [slot: Slots, val: Values]
\*             /\ Bmax(VS(S, Q)) \subseteq [slot: Slots, val: Values]  BY <5>3, <5>2, NPC DEF Bmax
\*       <5>5. ProposeDecrees(VS(S, Q)) \subseteq [slot: Slots, val: Values]  BY <5>4 DEF ProposeDecrees
\*       <5>6. \A m2 \in sent' \ sent: /\ m2.type = "2a" /\ m2.from = p /\ m2.bal = b
\*                                     /\ m2.decrees = ProposeDecrees(VS(S, Q))
\*             BY <5>1, <5>5 DEF Send, TypeOK, Messages
\*       <5>7. (sent \in SUBSET Messages)'  BY <4>2, <5>6, <5>1, <5>5, sent' \ sent \subseteq Messages DEF Phase2a,
\*             TypeOK, Send, Messages
\*       <5> QED BY <5>7, <4>2 DEF Phase2a, TypeOK, Send
\*     <4>3. ASSUME NEW a \in Acceptors, Phase1b(a)  PROVE TypeOK'
\*       <5>1. PICK m \in sent: Phase1b(a)!(m)  BY <4>3 DEF Phase1b
\*       <5>2. \A a2 \in Acceptors: voteds(a2) \subseteq [bal : Ballots, slot : Slots, val : Values]
\*             BY DEF voteds, TypeOK, Messages
\*       <5>4. {[type |-> "1b", from |-> a, bal |-> m.bal, voted |-> PartialBmax(voteds(a))]} \subseteq Messages  BY <5>1, <5>2 DEF TypeOK, Messages, Send, PartialBmax
\*       <5> QED BY <5>1, <5>4 DEF TypeOK, Send
\*     <4>4. ASSUME NEW a \in Acceptors, Phase2b(a)  PROVE TypeOK'
\*       <5>1. PICK m \in sent: Phase2b(a)!(m)  BY <4>4 DEF Phase2b
\*       <5>5. sent' \ sent \subseteq Messages  BY <5>1 DEF TypeOK, Send, Messages
\*       <5> QED BY <5>5 DEF Phase2b, TypeOK
\*     <4> QED BY <2>1, <4>1, <4>2, <4>3, <4>4 DEF Next
  
\*   <3>3. MsgInv'
\*     <4>1. ASSUME NEW p \in Proposers, Phase1a(p) PROVE  MsgInv'
\*         BY <4>1, Phase1aVotedForInv, <3>1, SafeAtStable, <2>1 DEF Phase1a, MsgInv, Send, TypeOK, Messages
\*     <4>2. ASSUME NEW a \in Acceptors, Phase1b(a) PROVE  MsgInv'
\*       <5>1. PICK m \in sent : Phase1b(a)!(m)
\*           BY <4>2 DEF Phase1b
\*       <5>2. voteds(a) = voteds(a)'
\*         BY <5>1 DEF Send, voteds, PartialBmax
\*       <5>3. \A r \in PartialBmax(voteds(a)): VotedForIn(a, r.bal, r.slot, r.val)
\*             BY DEF voteds, PartialBmax, VotedForIn
\*       <5>4. (\A r \in PartialBmax(voteds(a)): VotedForIn(a, r.bal, r.slot, r.val))'
\*             BY <5>3, <5>1, <5>2 DEF Send, VotedForIn
\*       <5>5. \A r \in PartialBmax(voteds(a)): \A b \in r.bal+1..m.bal-1, v \in Values: ~VotedForIn(a, b, r.slot, v)
\*         <6> SUFFICES ASSUME NEW r \in PartialBmax(voteds(a)),
\*                             NEW b \in (r.bal+1..m.bal-1), NEW v \in Values
\*                      PROVE  (~VotedForIn(a, b, r.slot, v))
\*           OBVIOUS
\*           <6>0. \A d \in voteds(a): d.bal \in Ballots /\ r.bal \in Ballots /\ r \in voteds(a) /\ r.bal < b
\*           BY <3>1 DEF PartialBmax, voteds, TypeOK, Messages
\*           <6>2. \A d \in voteds(a): d.slot = r.slot => d.bal < b BY <5>2, <6>0 DEF PartialBmax
\*           <6>3. ~\E d \in voteds(a): d.slot = r.slot /\ d.bal = b BY <6>0, <6>2
\*           <6>5. (~VotedForIn(a, b, r.slot, v))  BY <6>3, VotedaVoted
\*         <6> QED BY <5>1, <6>5 DEF VotedForIn, Send
\*       <5>13. ASSUME NEW m2 \in sent' PROVE MsgInv!(m2)'
\*         <6>1. ((m2.type = "1b") =>
\*                  /\ \A r \in m2.voted:
\*                       /\ VotedForIn(m2.from, r.bal, r.slot, r.val)
\*                       /\ \A b \in r.bal+1..m2.bal-1, v \in Values: ~VotedForIn(m2.from, b, r.slot, v)
\*                  /\ \A s \in Slots, b \in 0..m2.bal-1, v \in Values: VotedForIn(m2.from, b, s, v) =>
\*                       \E r \in m2.voted: r.slot = s /\ r.bal >= b)'
\*           <7>1. CASE m2 \in sent BY <7>1, <5>1, Phase1bVotedForInv, <4>2 DEF MsgInv, TypeOK, Messages
\*           <7>2. CASE m2 \in sent' \ sent
\*             <8> SUFFICES ASSUME (m2.type = "1b")'
\*                          PROVE  (/\ \A r \in m2.voted:
\*                                       /\ VotedForIn(m2.from, r.bal, r.slot, r.val)
\*                                       /\ \A b \in r.bal+1..m2.bal-1, v \in Values: ~VotedForIn(m2.from, b, r.slot, v)
\*                                  /\ \A s \in Slots, b \in 0..m2.bal-1, v \in Values: VotedForIn(m2.from, b, s, v) =>
\*                                       \E r \in m2.voted: r.slot = s /\ r.bal >= b)'
\*               OBVIOUS
\*             <8>0. m2.type = "1b" /\ m2.from = a /\ m2.bal = m.bal /\ m2.voted = PartialBmax(voteds(a))
\*                   BY <5>1, <7>2 DEF Send
\*             <8>1. (\A r \in m2.voted:
\*                      /\ VotedForIn(m2.from, r.bal, r.slot, r.val)
\*                      /\ \A b \in r.bal+1..m2.bal-1, v \in Values: ~VotedForIn(m2.from, b, r.slot, v))'
\*               BY <5>2, <7>2, <5>1, <5>4, <5>5, <8>0 DEF Send, VotedForIn
\*             <8>2. (\A s \in Slots, b \in 0..m2.bal-1, v \in Values: VotedForIn(m2.from, b, s, v) =>
\*                      \E r \in m2.voted: r.slot = s /\ r.bal >= b)'
\*               <9> SUFFICES ASSUME NEW s \in Slots', NEW b \in Ballots', NEW v \in Values',
\*                                   VotedForIn(m2.from, b, s, v)'
\*                            PROVE  (\E r \in m2.voted: r.slot = s /\ r.bal >= b)'
\*                 OBVIOUS
\*               <9>1. m2.from \in Acceptors /\ VotedForIn(m2.from, b, s, v) BY <3>1, <4>2, Phase1bVotedForInv DEF TypeOK, Messages
\*               <9>2. PartialBmax(voteds(m2.from)) = PartialBmax(voteds(m2.from))' BY <5>1 DEF PartialBmax, voteds, Send
\*               <9>3. PICK r3 \in voteds(m2.from) : r3.bal = b /\ r3.slot = s /\ r3.val = v BY <9>1, VotedaVoted
\*               <9>4. \A r \in voteds(m2.from) : \E r2 \in PartialBmax(voteds(m2.from)) : r.slot = r2.slot /\ r.bal =< r2.bal
\*                 BY <9>1, <9>3, PartialBmaxVoted
\*               <9>5. \E r2 \in PartialBmax(voteds(m2.from)) : s = r2.slot /\ b =< r2.bal BY <9>3, <9>4
\*               <9> QED BY <9>2, <9>5, <8>0
\*             <8>3. QED
\*               BY <8>1, <8>2
\*           <7> QED BY <7>1, <7>2
\*         <6>2. (/\ (m2.type = "2a") => 
\*                      /\ \A d \in m2.decrees : SafeAt(m2.bal, d.slot, d.val)
\*                      /\ \A d1,d2 \in m2.decrees : d1.slot = d2.slot => d1 = d2
\*                      /\ \A ma \in sent : (ma.type = "2a") /\ (ma.bal = m2.bal)
\*                                         => (ma = m2)
\*                /\ (m2.type = "2b") => 
\*                     \E ma \in sent : /\ ma.type = "2a" /\ ma.bal  = m2.bal
\*                                      /\ \E d \in ma.decrees: d.slot = m2.slot /\ d.val = m2.val)'
\*           BY <5>13, Phase1bVotedForInv, <5>1, <4>2, <3>1, SafeAtStable, <2>1 DEF Send, TypeOK,
\*               MsgInv, Messages
\*         <6> QED BY <6>1, <6>2 DEF MsgInv
\*       <5> QED BY <5>13 DEF MsgInv
\*     <4>3. ASSUME NEW p \in Proposers, Phase2a(p) PROVE  MsgInv'
\*       <5> SUFFICES ASSUME NEW m \in sent'
\*                    PROVE  (MsgInv!(m))'
\*           BY DEF MsgInv
\*       <5> PICK b \in Ballots, Q \in Quorums, S \in SUBSET sent:
\*             /\ ~ \E m2 \in sent: m2.type = "2a" /\ m2.bal = b
\*             /\ S \in SUBSET {m2 \in sent: (m2.type = "1b") /\ (m2.bal = b)}
\*             /\\A a \in Q: \E m2\in S: m2.from = a
\*             /\Send({[type |-> "2a", bal |-> b, from |-> p, decrees |-> ProposeDecrees(VS(S, Q))]})
\*           BY <4>3 DEF Phase2a
\*       <5>3. \A m2 \in sent' \ sent: m2.type = "2a" /\ m2.bal = b  BY DEF Send
\*       <5>4. ((m.type = "1b") =>
\*               /\ \A r \in m.voted:
\*                     /\ VotedForIn(m.from, r.bal, r.slot, r.val)
\*                     /\ \A b3 \in r.bal+1..m.bal-1, v \in Values: ~VotedForIn(m.from, b3, r.slot, v)
\*               /\ \A s \in Slots, b3 \in 0..m.bal-1, v \in Values: VotedForIn(m.from, b3, s, v) =>
\*                     \E r \in m.voted: r.slot = s /\ r.bal >= b3)'
\*             BY <4>3, <5>3, <3>1, Phase2aVotedForInv DEF TypeOK, Messages, MsgInv
\*       <5>5. ((m.type = "2a") => /\ \A d \in m.decrees: SafeAt(m.bal, d.slot, d.val)
\*                                 /\ \A d1,d2 \in m.decrees: d1.slot = d2.slot => d1 = d2
\*                                 /\ \A m3 \in sent: (m3.type = "2a" /\ m.bal = m3.bal) => m3 = m)'
\*         <6> SUFFICES ASSUME (m.type = "2a")'
\*                      PROVE  (/\ \A d \in m.decrees: SafeAt(m.bal, d.slot, d.val)
\*                              /\ \A d1,d2 \in m.decrees: d1.slot = d2.slot => d1 = d2
\*                              /\ \A m3 \in sent: (m3.type = "2a" /\ m.bal = m3.bal) => m3 = m)'
\*             OBVIOUS
\*         <6> USE DEF VS
\*         <6>2. (\A d \in m.decrees: SafeAt(m.bal, d.slot, d.val))'
\*           <7>1. \A d \in [slot: FreeSlots(VS(S, Q)), val: Values] \ {}: SafeAt(b, d.slot, d.val)
\*             <8> SUFFICES ASSUME NEW d \in [slot: FreeSlots(VS(S, Q)), val: Values] \ {}  PROVE  SafeAt(b, d.slot, d.val)
\*                 OBVIOUS
\*             <8>1. \A m2 \in S: ~\E d2 \in m2.voted: m2.from \in Q /\ d.slot = d2.slot  BY DEF FreeSlots
\*             <8>4. \A v \in Values, b2 \in Ballots, a \in Q: b2 \in 0..b-1 => ~VotedForIn(a, b2, d.slot, v)
\*                   BY <8>1 DEF FreeSlots, TypeOK, Messages, MsgInv
\*             <8> QED BY <8>4, <3>1 DEF SafeAt, NewProposals, FreeSlots, WontVoteIn, TypeOK, Messages
\*           <7>2. \A d \in [slot: FreeSlots(VS(S, Q)), val: Values] \ {}: SafeAt(b, d.slot, d.val)'  BY <7>1, SafeAtStable,
\*                 <3>1, <2>1 DEF NewProposals, FreeSlots, TypeOK, Messages
\*           <7>3. \A d \in NewProposals(VS(S, Q)): SafeAt(b, d.slot, d.val)'  BY <7>2, NPC DEF NewProposals
\*           <7>4. \A d \in PartialBmax(VS(S, Q)): SafeAt(b, d.slot, d.val)
\*             <8> SUFFICES ASSUME NEW d \in PartialBmax(VS(S, Q)), NEW b2 \in Ballots, b2 \in 0..(b-1)
\*                          PROVE  \E Q2\in Quorums: \A a \in Q2:
\*                                    VotedForIn(a, b2, d.slot, d.val) \/ WontVoteIn(a, b2, d.slot)
\*                 BY DEF SafeAt
\*             <8>3. ~\E d2 \in VS(S, Q): (d2.bal > d.bal /\ d2.slot = d.slot)
\*                   BY \A d2 \in VS(S, Q): ~(~(d2.bal <= d.bal) /\ d2.slot = d.slot) DEF PartialBmax, TypeOK, Messages
\*             <8>4. /\ VS(S, Q) \in SUBSET [bal: Ballots, slot: Slots, val: Values]
\*                   /\ d \in [bal: Ballots, slot: Slots, val: Values]
\*                   BY <3>1 DEF TypeOK, Messages, PartialBmax
\*             <8>5. \A d2 \in VS(S, Q): d2.slot = d.slot => d.bal >= d2.bal
\*               BY DEF PartialBmax
\*             <8>2a. PICK aa \in Q: VotedForIn(aa, d.bal, d.slot, d.val)
\*               BY DEF MsgInv, PartialBmax, TypeOK, Messages
\*             <8>2b. \A a2 \in Q: \E m6 \in sent: m6.type = "1b" /\ m6.bal > b2 /\ m6.from = a2 OBVIOUS
\*             <8>2c. \A a2 \in Q, s3 \in Slots:
\*                      (\A v3 \in Values: ~VotedForIn(a2, b2, s3, v3)) => WontVoteIn(a2, b2, s3)
\*                 BY <8>2b DEF WontVoteIn
\*             <8>2d. \A a2 \in Q: \E m4 \in S:
\*                      /\ m4.from = a2
\*                      /\ \A r \in m4.voted :
\*                            /\ VotedForIn(a2, r.bal, r.slot, r.val)
\*                            /\ r.slot = d.slot => r.bal =< d.bal
\*                            /\ \A b4 \in r.bal + 1..b - 1, v \in Values :
\*                                  ~VotedForIn(a2, b4, r.slot, v)
\*                      /\ \A s \in Slots, b4 \in 0..m4.bal-1, v \in Values :
\*                            VotedForIn(a2, b4, s, v)
\*                            => (\E r \in m4.voted : r.slot = s /\ r.bal >= b4)
\*               BY <8>5 DEF MsgInv
\*             <8>6. CASE b2 \in d.bal+1..b-1
\*               <9>1. \A a2 \in Q:
\*                       \A b4 \in d.bal + 1..b - 1, v \in Values :
\*                         ~VotedForIn(a2, b4, d.slot, v)
\*                 BY <8>2d, <8>4 DEF TypeOK, Messages
\*               <9>2. \A a2 \in Q, v \in Values: ~VotedForIn(a2, b2, d.slot, v)
\*                     BY <8>6, <8>4, <9>1
\*               <9> QED BY <9>2 DEF WontVoteIn, SafeAt
\*             <8>7. CASE b2 = d.bal
\*               BY <8>7, <8>6, <8>4, <8>2a, VotedOnce, QuorumAssumption,
\*               \A a2 \in Q, v2 \in Values: VotedForIn(a2, b2, d.slot, v2) => v2 = d.val, <8>2c DEF SafeAt
\*             <8>8. CASE b2 \in 0..d.bal-1
\*                 <9>2. SafeAt(d.bal, d.slot, d.val)  BY <8>2a, QuorumAssumption, <8>4, VotedInv
\*                 <9> QED BY <8>8, <9>2, <8>5 DEF SafeAt, MsgInv, TypeOK, Messages
\*             <8> QED BY <8>6, <8>7, <8>8, <8>4
\*           <7>5. PartialBmax(VS(S, Q)) \in SUBSET [bal: Ballots, slot: Slots, val: Values]  BY DEF PartialBmax, TypeOK, Messages
\*           <7>6. \A d \in PartialBmax(VS(S, Q)): SafeAt(b, d.slot, d.val)'  BY <7>4, SafeAtStable, <3>1, <7>5, <2>1
\*           <7>7. \A d \in Bmax(VS(S, Q)): SafeAt(b, d.slot, d.val)'  BY <7>6, <7>5 DEF Bmax
\*           <7>8. \A d \in Bmax(VS(S, Q)) \cup NewProposals(VS(S, Q)): SafeAt(b, d.slot, d.val)'  BY <7>7, <7>3
\*           <7>9. (\A m2 \in sent: m2.type = "2a" => \A d \in m2.decrees: SafeAt(m2.bal, d.slot, d.val))'
\*             <8> SUFFICES ASSUME NEW m2 \in sent', (m2.type = "2a")', NEW d \in m2.decrees
\*                          PROVE  (SafeAt(m2.bal, d.slot, d.val))'
\*                 OBVIOUS
\*             <8>1. CASE m2 \in sent  BY <3>1, SafeAtStable, <8>1, <2>1 DEF MsgInv, Messages, TypeOK
\*             <8>2. CASE m2 \in sent' \ sent
\*               <9> HIDE DEF VS
\*               <9>1. SafeAt(m2.bal, d.slot, d.val)'  BY <7>8, <8>2, b = m2.bal DEF Send, ProposeDecrees
\*               <9> QED BY <3>1, <9>1 DEF Send, TypeOK, Messages
\*             <8> QED BY <8>1, <8>2
\*           <7> QED BY <7>9
\*         <6>3. (\A d1,d2 \in m.decrees: d1.slot = d2.slot => d1 = d2)'
\*           <7>1. \A m2 \in sent' \ sent: \A d1,d2 \in m2.decrees: d1.slot = d2.slot => d1 = d2
\*             <8>1. VS(S, Q) \in SUBSET [bal: Ballots, slot: Slots, val: Values]  BY DEF Messages, TypeOK
\*             <8>2. \A r1, r2 \in PartialBmax(VS(S, Q)): r1.slot = r2.slot => r1.bal = r2.bal  BY <8>1 DEF PartialBmax
\*             <8>3. PartialBmax(VS(S, Q)) \subseteq VS(S, Q)  BY <8>1 DEF PartialBmax
\*             <8>4. \A r1, r2 \in PartialBmax(VS(S, Q)): r1.bal = r2.bal /\ r1.slot = r2.slot => r1.val = r2.val
\*                   BY <8>3, VotedUnion
\*             <8>5. \A r1, r2 \in PartialBmax(VS(S, Q)): r1.slot = r2.slot => r1.bal = r2.bal /\ r1.val = r2.val
\*                   BY <8>4, <8>2, <8>3, <8>1
\*             <8>6. \A r1, r2 \in Bmax(VS(S, Q)): r1.slot = r2.slot => r1 = r2  BY <8>5, Isa DEF Bmax
\*             <8> HIDE DEF VS
\*             <8> QED BY <8>6, NPC DEF ProposeDecrees, Send
\*           <7> QED BY <7>1 DEF MsgInv
\*         <6>4. (\A m2 \in sent: (m2.type = "2a" /\ m2.bal = m.bal) => (m2 = m))'
\*           <7>1. \A m2 \in sent: (m2.type = "2a") => (m2.bal # b)  OBVIOUS
\*           <7>2. CASE m \in sent BY <7>2, <5>3, <7>1 DEF MsgInv
\*           <7> HIDE DEF VS
\*           <7>3. CASE m \in sent' \ sent BY <7>3, <5>3, <7>1 DEF Send
\*           <7> QED BY <7>2, <7>3
\*         <6> QED BY <6>2, <6>3, <6>4
\*       <5>6. ((m.type = "2b") => \E m3 \in sent: m3.type = "2a" /\ m.bal = m3.bal /\ \E d \in m3.decrees: d.slot = m.slot /\ d.val = m.val)'  BY <5>3, m.type = "2b" => m \in sent,
\*             <3>1 DEF TypeOK, Messages, MsgInv, Send
\*       <5> QED BY <5>4, <5>5, <5>6
\*     <4>4. ASSUME NEW a \in Acceptors, Phase2b(a) PROVE  MsgInv'
\*       <5> SUFFICES ASSUME NEW m \in sent'
\*                    PROVE  (/\ (m.type = "1b") =>
\*                                 /\ \A r \in m.voted:
\*                                      /\ VotedForIn(m.from, r.bal, r.slot, r.val)
\*                                      /\ \A b \in r.bal+1..m.bal-1, v \in Values: ~VotedForIn(m.from, b, r.slot, v)
\*                                 /\ \A s \in Slots, b \in 0..m.bal-1, v \in Values: VotedForIn(m.from, b, s, v) =>
\*                                      \E r \in m.voted: r.slot = s /\ r.bal >= b
\*                            /\ (m.type = "2a") => 
\*                                 /\ \A d \in m.decrees : SafeAt(m.bal, d.slot, d.val)
\*                                 /\ \A d1,d2 \in m.decrees : d1.slot = d2.slot => d1 = d2
\*                                 /\ \A ma \in sent : (ma.type = "2a") /\ (ma.bal = m.bal)
\*                                                        => (ma = m)
\*                            /\ (m.type = "2b") => 
\*                                 /\ \E ma \in sent : /\ ma.type = "2a"
\*                                                     /\ ma.bal  = m.bal
\*                                                     /\ \E d \in ma.decrees: d.slot = m.slot /\ d.val = m.val)'
\*         BY DEF MsgInv
\*       <5>. PICK m1 \in sent : Phase2b(a)!(m1)
\*         BY <4>4 DEF Phase2b
\*       <5>0. \A aa,vv,bb,ss: VotedForIn(aa, bb, ss, vv) => VotedForIn(aa, bb, ss, vv)'
\*         BY DEF VotedForIn, Send
\*       <5>10. \A aa, vv, bb, ss: aa # a =>
\*                 VotedForIn(aa, bb, ss, vv) <=> VotedForIn(aa, bb, ss, vv)'
\*         BY DEF VotedForIn, Send
\*       <5>1. ((m.type = "1b") =>
\*                /\ \A r \in m.voted:
\*                     /\ VotedForIn(m.from, r.bal, r.slot, r.val)
\*                     /\ \A b \in r.bal+1..m.bal-1, v \in Values: ~VotedForIn(m.from, b, r.slot, v)
\*                /\ \A s \in Slots, b \in 0..m.bal-1, v \in Values: VotedForIn(m.from, b, s, v) =>
\*                     \E r \in m.voted: r.slot = s /\ r.bal >= b)'
\*         <6> SUFFICES ASSUME (m.type = "1b")'
\*                      PROVE  (/\ \A r \in m.voted:
\*                                   /\ VotedForIn(m.from, r.bal, r.slot, r.val)
\*                                   /\ \A b \in r.bal+1..m.bal-1, v \in Values: ~VotedForIn(m.from, b, r.slot, v)
\*                              /\ \A s \in Slots, b \in 0..m.bal-1, v \in Values: VotedForIn(m.from, b, s, v) =>
\*                                   \E r \in m.voted: r.slot = s /\ r.bal >= b)'
\*           OBVIOUS
\*         <6>0. /\ m \in sent
\*               /\ \A r \in m.voted :
\*                    /\ VotedForIn(m.from, r.bal, r.slot, r.val)
\*                    /\ \A b \in r.bal + 1..m.bal - 1, v \in Values :
\*                         ~VotedForIn(m.from, b, r.slot, v)
\*               /\ \A s \in Nat, b \in 0..m.bal-1, v \in Values :
\*                    VotedForIn(m.from, b, s, v)
\*                    => (\E r \in m.voted : r.slot = s /\ r.bal >= b)
\*           BY DEF Send, MsgInv
\*         <6>5. CASE m.from # a BY <6>5, <5>10, <6>0 DEF TypeOK, Messages, Send
\*         <6>6. CASE m.from = a
\*           <7>1. \A b \in 0..m.bal-1, ss \in Slots, vv \in Values: VotedForIn(a, b, ss, vv) <=> VotedForIn(a, b, ss, vv)'
\*             BY <6>6, m.bal =< m1.bal, \A m2 \in sent' \ sent: m2.bal = m1.bal DEF Send, VotedForIn, TypeOK, Messages
\*           <7>2. (\A r \in m.voted:
\*                    /\ VotedForIn(m.from, r.bal, r.slot, r.val)
\*                    /\ \A b \in r.bal+1..m.bal-1, v \in Values: ~VotedForIn(m.from, b, r.slot, v))'
\*             BY <6>6, <5>0, <3>1, <2>1, <6>0, <7>1 DEF TypeOK, Messages, Send
\*           <7>3. (\A s \in Slots, b \in 0..m.bal-1, v \in Values: VotedForIn(m.from, b, s, v) =>
\*                    \E r \in m.voted: r.slot = s /\ r.bal >= b)'
\*             BY <6>6, <5>0, <6>0, <7>1 DEF Send
\*           <7> QED BY <7>3, <7>2
\*         <6> QED BY <6>5, <6>6
\*       <5>2. ((m.type = "2a") => 
\*                /\ \A d \in m.decrees : SafeAt(m.bal, d.slot, d.val)
\*                /\ \A d1,d2 \in m.decrees : d1.slot = d2.slot => d1 = d2
\*                /\ \A ma \in sent : (ma.type = "2a") /\ (ma.bal = m.bal)
\*                                       => (ma = m))'
\*         BY SafeAtStable, <3>1, <2>1 DEF MsgInv, TypeOK, Messages, Send
\*       <5>3. ((m.type = "2b") => 
\*                /\ \E ma \in sent : /\ ma.type = "2a"
\*                                    /\ ma.bal  = m.bal
\*                                    /\ \E d \in ma.decrees: d.slot = m.slot /\ d.val = m.val)'
\*         BY <3>1, <2>1 DEF MsgInv, TypeOK, Messages, Send
\*       <5>4. QED
\*         BY <5>1, <5>2, <5>3
\*     <4>. QED
\*       BY <4>1, <4>2, <4>3, <4>4, <2>1 DEF Next
\*   <3>4. QED
\*     BY <3>1, <3>3 DEF Inv, vars, Next
\*   <2>2. CASE UNCHANGED vars
\*     BY <2>2 DEF vars, Inv, TypeOK, MsgInv, VotedForIn, SafeAt, WontVoteIn
\*   <2>3. QED
\*     BY <2>1, <2>2
\* <1>3. QED
\*   BY <1>1, <1>2, PTL DEF Spec

\* THEOREM Consistent == Spec => []Consistency
\* <1> USE DEF Ballots
\* <1>1. Inv => Consistency
\*   <2> SUFFICES ASSUME Inv, NEW v1 \in Values,  NEW v2 \in Values, NEW s \in Slots, NEW b1 \in Ballots, NEW b2 \in Ballots,
\*                       ChosenIn(b1, s, v1), ChosenIn(b2, s, v2), b1 <= b2
\*                PROVE  v1 = v2
\*       BY DEF Consistency, Chosen
\*   <2>1. CASE b1 = b2
\*     <3>1. \E a \in Acceptors: VotedForIn(a, b1, s, v1) /\ VotedForIn(a, b1, s, v2)
\*           BY <2>1, QuorumAssumption DEF ChosenIn
\*     <3> QED BY <3>1, VotedOnce DEF Inv
\*   <2>2. CASE b1 < b2
\*     <3>1. SafeAt(b2, s, v2)  BY VotedInv, QuorumAssumption DEF ChosenIn, Inv
\*     <3>2. PICK Q1 \in Quorums: \A a \in Q1: VotedForIn(a, b1, s, v1)  BY DEF ChosenIn
\*     <3>3. PICK Q2 \in Quorums: \A a \in Q2: VotedForIn(a, b1, s, v2) \/ WontVoteIn(a, b1, s)  BY <3>1, <2>2 DEF SafeAt
\*     <3>4. PICK a \in Q1 \cap Q2: (VotedForIn(a, b1, s, v1) /\ VotedForIn(a, b1, s, v2)) \/ (VotedForIn(a, b1, s, v1) /\ WontVoteIn(a, b1, s))
\*           BY QuorumAssumption, <3>2, <3>3
\*     <3> QED BY <3>4, QuorumAssumption, VotedOnce DEF WontVoteIn, Inv
\*   <2> QED BY <2>1, <2>2
\* <1> QED BY Invariant, <1>1, PTL

=============