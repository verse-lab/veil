import Veil

open Std
/-
This file specifies the Byzantine broadcast protocol in Veil, which is a
TLA+ encoding of a parameterized model of the broadcast distributed algorithm
with Byzantine faults.

This is a one-round version of asynchronous reliable broadcast (Fig. 7) from:

[1] T. K. Srikanth, Sam Toueg. Simulating authenticated broadcasts to derive
simple fault-tolerant algorithms. Distributed Computing 1987,
Volume 2, Issue 2, pp 80-94

The protocol works as follows:
- There are N processes, of which F can be faulty (Byzantine)
- There are T >= F possible faulty processes
- The constraint is N > 3*T
- Processes can be in states: V0 (no INIT), V1 (received INIT), SE (sent ECHO), AC (accepted)
- Correct processes send ECHO messages based on certain conditions
- A correct process accepts when it receives enough ECHO messages

Properties:
- Correctness: if a correct process broadcasts, then every correct process accepts
- Relay: if a correct process accepts, then every correct process accepts
- Unforgeability: if no correct process broadcasts, then no correct process accepts
-/
veil module BcastByz

type process
type procSet
instantiate pset : TSet process procSet
-- instantiate thread : Fintype process


enum PCState = { V0, V1, SE, AC }
enum phase = { init, run }

-- N: total number of processes
-- T: upper bound on Byzantine processes
-- F: actual number of faulty processes
immutable individual N : Nat
immutable individual T : Nat
immutable individual F : Nat
immutable individual Proc : procSet
-- State variables

-- M == { "ECHO" }
-- immutable individual M : process
-- (* ByzMsgs == { <<p, "ECHO">> : p \in Faulty }: quite complicated to write a TLAPS proof
--    for the cardinality of the expression { e : x \in S}
--  *)

-- individual Corr : Finset process    -- correct processes
individual Corr : procSet
individual Faulty : procSet             -- faulty processes
relation pc (p : process) (st : PCState)  -- control state of each process
-- relation pointer (ph : phase)             -- current phase of the protocol

-- In TLA+: sent \subseteq Proc \times M
-- Since all messages are <<p, "ECHO">>, we only need to track which processes have sent
-- sent is the set of processes that have sent messages
-- relation sent (p : process)
individual sent : procSet
function rcvd (receiver : process) : procSet
#gen_state


-- Ghost definitions for readability
ghost relation isCorrect (p : process) := pset.contains p Corr
ghost relation isFaulty (p : process) := pset.contains p Faulty
-- Initial state


-- Init ==
--   /\ sent = {}                          (* No messages sent initially *)
--   /\ pc \in [ Proc -> {"V0", "V1"} ]    (* Some processes received INIT messages, some didn't *)
--   /\ rcvd = [ i \in Proc |-> {} ]       (* No messages received initially *)
--   /\ Corr \in SUBSET Proc
--   /\ Cardinality(Corr) = N - F          (* N - F processes are correct, but their identities are unknown*)
--   /\ Faulty = Proc \ Corr               (* The rest (F) are faulty*)
after_init  {
  -- No messages sent initially
  sent := pset.empty
  -- sentCount := 0
  rcvd P := pset.empty
  -- All processes start in V0 state
  pc P ST := ST == V0
  -- let b :| pset.count b ≠ 0
  -- pc P ST := if pset.contains P b then ST == V1 else ST == V0
  let t :| pset.count t == N - F
  Corr := t
  Faulty := pset.diff Proc t
}


-- ByzMsgs == Faulty \X M

-- Helper: receive messages (can receive from correct processes and potentially Byzantine)
-- This models the Receive(self, includeByz) from TLA+
-- action ReceiveMessages (self : process) (includeByz : Bool) {
--   require isCorrect self
--   -- Non-deterministically receive some subset of available messages
--   -- Messages from correct processes that have sent
--   -- Plus potentially messages from Byzantine processes
--   let newSender ← pick process
--   if (sent newSender ∨ (includeByz ∧ isFaulty newSender)) then
--     -- Can receive this message
--     rcvd self newSender := true
--     -- Update count of received messages
--     rcvdCount self := *  -- Non-deterministically update (will be constrained by invariant)
-- }

-- Receive(self, includeByz) ==
--   \E newMessages \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {}) ) :
--     rcvd' = [ i \in Proc |-> IF i # self THEN rcvd[i] ELSE rcvd[self] \cup newMessages ]
-- ReceiveFromCorrectSender(self) == Receive(self, FALSE)
-- ReceiveFromAnySender(self) == Receive(self, TRUE)
procedure ReceiveFromAnySender (self : process) {
  require isCorrect self
  let includeByz := true
  let sender ← pick process
  -- Only receive from senders who have actually sent (not from Byzantine)
  -- if (sender ∈ sent ∨ (includeByz ∧ isFaulty sender)) then
  if pset.contains sender sent ∨ (includeByz ∧ isFaulty sender) then
    rcvd self := pset.insert sender (rcvd self)
}


procedure ReceiveFromCorrectSender (self : process){
  require isCorrect self
  let includeByz := false
  let sender ← pick process
  -- Only receive from senders who have actually sent (not from Byzantine)
  -- if (sender ∈ sent ∨ (includeByz ∧ isFaulty sender)) then
  if pset.contains sender sent ∨ (includeByz ∧ isFaulty sender) then
      rcvd self := pset.insert sender (rcvd self)
}



-- UponV1(self) ==
--   /\ pc[self] = "V1"
--   /\ pc' = [pc EXCEPT ![self] = "SE"]
--   /\ sent' = sent \cup { <<self, "ECHO">> }
--   /\ UNCHANGED << Corr, Faulty >>
action ReceiveFromAnySender_UponV1 (self : process) {
  require isCorrect self
  require pc self V1
  ReceiveFromAnySender self
  sent := pset.insert self sent
}



-- UponNonFaulty(self) ==
--   /\ pc[self] \in { "V0", "V1" }
--   /\ Cardinality(rcvd'[self]) >= N - 2*T
--   /\ Cardinality(rcvd'[self]) < N - T
--   /\ pc' = [ pc EXCEPT ![self] = "SE" ]
--   /\ sent' = sent \cup { <<self, "ECHO">> }
--   /\ UNCHANGED << Corr, Faulty >>
action ReceiveFromAnySender_UponNonFaulty (self : process) {
  require isCorrect self
  require pc self V0 ∨ pc self V1
  ReceiveFromAnySender self
  pc self ST := ST == SE
  sent := pset.insert self sent
  assume pset.count (rcvd self) >= N - 2 * T
  assume pset.count (rcvd self) < N - T
}





-- UponAcceptNotSentBefore(self) ==
--   /\ pc[self] \in { "V0", "V1" }
--   /\ Cardinality(rcvd'[self]) >= N - T
--   /\ pc' = [ pc EXCEPT ![self] = "AC" ]
--   /\ sent' = sent \cup { <<self, "ECHO">> }
--   /\ UNCHANGED << Corr, Faulty >>
action ReceiveFromAnySender_UponAcceptNotSentBefore (self : process) {
  require isCorrect self
  require pc self V0 ∨ pc self V1
  ReceiveFromAnySender self
  assume pset.count (rcvd self) >= N - T
  pc self ST := ST == AC
  sent := pset.insert self sent
}


-- Step(self) ==
--   /\ ReceiveFromAnySender(self)
--   /\ \/ UponV1(self)
--      \/ UponNonFaulty(self)
--      \/ UponAcceptNotSentBefore(self)
--      \/ UponAcceptSentBefore(self)
-- UponAcceptSentBefore(self) ==
--   /\ pc[self] = "SE"
--   /\ Cardinality(rcvd'[self]) >= N - T
--   /\ pc' = [pc EXCEPT ![self] = "AC"]
--   /\ sent' = sent
--   /\ UNCHANGED << Corr, Faulty >>
action ReceiveFromAnySender_UponAcceptorSentBefore (self : process) {
  require isCorrect self
  ReceiveFromAnySender self
  -- No state change if already sent
  pc self ST := ST == AC
  assume pset.count (rcvd self) >= N - T
}

-- Parameter constraints from TLA+ specification
-- TypeOK == /\ N \in Nat \ {0}
--           /\ T \in Nat
--           /\ F \in Nat
--           /\ N > 3 * T
--           /\ T >= F
-- procedure ByzMsgs {
--   return pset.remove M Faulty
-- }
invariant [Corr_cup_faulty_eq_proc] pset.union Corr Faulty == Proc
invariant [card_corr] pset.count Corr >= N - T
invariant [typeOK] N > 3 * T ∧ T >= F ∧ N ≠ 0
invariant [card_faulty] pset.count Faulty <= T

#gen_spec
-- (* Constraints about the cardinalities of Faulty and Corr, their elements, and the upper bound
--    of the set of possible Byzantine messages. The FCConstraints is an invariant. One can probably
--    prove the theorems below without FCConstraints (by applying facts from FiniteSetTheorems),
--    but these proofs will be longer.
--  *)
-- FCConstraints ==
--   /\ Corr \subseteq Proc
--   /\ Faulty \subseteq Proc
--   /\ IsFiniteSet(Corr)
--   /\ IsFiniteSet(Faulty)
--   /\ Corr \cup Faulty = Proc
--   /\ Faulty = Proc \ Corr
--   /\ Cardinality(Corr) >= N - T
--   /\ Cardinality(Faulty) <= T
--   /\ ByzMsgs \subseteq Proc \X M
--   /\ IsFiniteSet(ByzMsgs)
--   /\ Cardinality(ByzMsgs) = Cardinality(Faulty)


#model_check
{ process := (Fin 4),
  procSet := (Std.ExtTreeSet (Fin 4) compare)}
{ N := 4,
  T := 1,
  F := 1,
  Proc := (Std.ExtTreeSet.empty.insertMany (List.finRange 4))}




end BcastByz
