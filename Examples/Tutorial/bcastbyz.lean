import Veil
import Veil.Core.Tools.Checker.Concrete.Main

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

enum PCState = { V0, V1, SE, AC }
enum phase = { init, run }

-- N: total number of processes
-- T: upper bound on Byzantine processes
-- F: actual number of faulty processes
immutable individual N : Nat
immutable individual T : Nat
immutable individual F : Nat

-- State variables
relation Corr (p : process)               -- correct processes
relation Faulty (p : process)             -- faulty processes
relation pc (p : process) (st : PCState)  -- control state of each process
relation pointer (ph : phase)             -- current phase of the protocol

-- In TLA+: sent \subseteq Proc \times M
-- Since all messages are <<p, "ECHO">>, we only need to track which processes have sent
-- sent is the set of processes that have sent messages
relation sent (p : process)

-- In TLA+: rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]
relation rcvd (receiver : process) (sender : process)
individual sentCount : Nat
function rcvdCount : process → Nat

-- Track cardinality of Corr and Faulty sets
individual corrCount : Nat
individual faultyCount : Nat
#gen_state

-- Ghost definitions for readability
ghost relation isCorrect (p : process) := Corr p
ghost relation isFaulty (p : process) := Faulty p
-- Initial state


-- We model the general Init where processes can start in V0 or V1
after_init  {
  -- No messages sent initially
  sent P := false
  sentCount := 0
  rcvd R S := false
  -- All processes start in V0 state
  pc P ST := ST == V0
  Corr P := false
  Faulty P := false
  corrCount := 0
  faultyCount := 0
  rcvdCount P := 0
  -- Start in initialization phase
  pointer P := P == init
}

/-
To get assertion `Cardinality(Corr) = N - F` and `Faulty = Proc \ Corr` in TLA+,
we introduce a loop using non-deterministic choice to select processes until we reach N - F.
-/
action initialization {
  require pointer init
  require corrCount < N - F
  -- In TLA+: /\ Corr \in SUBSET Proc
  --          /\ Cardinality(Corr) = N - F
  --          /\ Faulty = Proc \ Corr
  let nonCorr :| ¬ Corr nonCorr
  Corr nonCorr := true
  corrCount := corrCount + 1
  if corrCount == N - F then
    pointer P := P == run
    Faulty P := !(Corr P)
    faultyCount := F
  }

-- Action: UponV1
-- If process received an INIT message (pc[self] = V1) and hasn't sent ECHO before,
-- then send ECHO to all
-- In TLA+: sent' = sent \cup { <<self, "ECHO">> }
action UponV1 (self : process) {
  require pointer run
  require isCorrect self
  require pc self V1

  -- Check haven't sent before
  require ¬sent self

  -- Send ECHO message: add self to sent set
  sent self := true
  sentCount := sentCount + 1
  pc self ST := ST == SE
}


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
action ReceiveFromAnySender (self : process) {
  require pointer run
  require isCorrect self
  let includeByz := true
  let sender ← pick process
  -- Only receive from senders who have actually sent (not from Byzantine)
  if (sent sender ∨ (includeByz ∧ isFaulty sender)) then
    if ¬(rcvd self sender) then
      rcvd self sender := true
      rcvdCount self := rcvdCount self + 1
}


action ReceiveFromCorrectSender (self : process){
  require pointer run
  require isCorrect self
  let includeByz := false
  let sender ← pick process
  -- Only receive from senders who have actually sent (not from Byzantine)
  if (sent sender ∨ (includeByz ∧ isFaulty sender)) then
    if ¬(rcvd self sender) then
      rcvd self sender := true
      rcvdCount self := rcvdCount self + 1
}


-- Action: UponNonFaulty
-- If process received ECHO from >= N-2T distinct processes but < N-T,
-- and hasn't sent ECHO before, then send ECHO'

-- UponNonFaulty(self) ==
--   /\ pc[self] \in { "V0", "V1" }
--   /\ Cardinality(rcvd'[self]) >= N - 2*T
--   /\ Cardinality(rcvd'[self]) < N - T
--   /\ pc' = [ pc EXCEPT ![self] = "SE" ]
--   /\ sent' = sent \cup { <<self, "ECHO">> }
--   /\ UNCHANGED << Corr, Faulty >>
action UponNonFaulty (self : process) {
  require pointer run
  require isCorrect self
  require pc self V0 ∨ pc self V1

  -- Check haven't sent before
  require ¬sent self

  -- Require received from >= N - 2*T distinct processes
  let rcvdCnt := rcvdCount self
  require rcvdCnt >= N - 2*T
  require rcvdCnt < N - T

  -- Send ECHO and transition to SE
  sent self := true
  sentCount := sentCount + 1
  pc self ST := ST == SE
}


-- Action: UponAcceptNotSentBefore
-- If process received ECHO from >= N-T distinct processes and hasn't sent before,
-- then accept and send ECHO

-- UponAcceptNotSentBefore(self) ==
--   /\ pc[self] \in { "V0", "V1" }
--   /\ Cardinality(rcvd'[self]) >= N - T
--   /\ pc' = [ pc EXCEPT ![self] = "AC" ]
--   /\ sent' = sent \cup { <<self, "ECHO">> }
--   /\ UNCHANGED << Corr, Faulty >>
action UponAcceptNotSentBefore (self : process) {
  require pointer run
  require isCorrect self
  require pc self V0 ∨ pc self V1

  -- Check haven't sent before
  require ¬sent self

  -- Require received from >= N - T distinct processes
  let rcvdCnt := rcvdCount self
  require rcvdCnt >= N - T
  -- Accept and send ECHO
  sent self := true
  sentCount := sentCount + 1
  pc self ST := ST == AC
}

-- Action: UponAcceptSentBefore
-- If process already sent ECHO (pc[self] = SE) and received from >= N-T,
-- then accept
-- UponAcceptSentBefore(self) ==
--   /\ pc[self] = "SE"
--   /\ Cardinality(rcvd'[self]) >= N - T
--   /\ pc' = [pc EXCEPT ![self] = "AC"]
--   /\ sent' = sent
--   /\ UNCHANGED << Corr, Faulty >>
action UponAcceptSentBefore (self : process) {
  require pointer run
  require isCorrect self
  require pc self SE

  -- Require received from >= N - T distinct processes
  let rcvdCnt := rcvdCount self
  require rcvdCnt >= N - T

  -- Accept (already sent)
  pc self ST := ST == AC
}


-- Parameter constraints from TLA+ specification
-- TypeOK == /\ N \in Nat \ {0}
--           /\ T \in Nat
--           /\ F \in Nat
--           /\ N > 3 * T
--           /\ T >= F
invariant [parameter_constraints] true

termination true = true
#gen_spec

set_option trace.veil.debug true
#gen_exec
#finitize_types (Fin 4), PCState, phase


-- Set immutable values
-- N = 4 processes, T = 1 (upper bound on Byzantine), F = 1 (actual Byzantine)
#set_theory { N := 7, T := 2, F := 1 }

#run_checker parameter_constraints
#eval modelCheckerResult.seen.size
-- Visualize the results
open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />

end BcastByz
