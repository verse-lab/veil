module

public import Veil

/-
Veil translation/adaptation of TLA+ material from tlaplus/Examples.
Copyright (c) 2016: The TLA+ project and other contributors.
Upstream MIT license: Benchmarks/TLA/TLAPlusExamples/LICENSE
Original specification: Igor Konnov, Thanh Hai Tran, Josef Widder, 2016.
-/

open Std
/-
src : https://github.com/tlaplus/Examples/blob/a997ee6813b7c20951311e3658a8579270d9f306/specifications/bcastByz/bcastByz.tla
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

-/
veil module BcastByz

type process
type procSet
instantiate pset : TSet process procSet
-- instantiate thread : Fintype process

enum PCState = { V0, V1, SE, AC }

-- N: total number of processes
-- T: upper bound on Byzantine processes
-- F: actual number of faulty processes
immutable individual N : Nat
immutable individual T : Nat
immutable individual F : Nat
-- immutable individual Proc : procSet

instantiate processEnumerable : Veil.Enumeration process

-- State variables

-- M == { "ECHO" }
-- immutable individual M : process
-- (* ByzMsgs == { <<p, "ECHO">> : p \in Faulty }: quite complicated to write a TLAPS proof
--    for the cardinality of the expression { e : x \in S}
--  *)

-- individual Corr : Finset process    -- correct processes
individual Corr : procSet
individual Faulty : procSet             -- faulty processes
function pc (p : process) : PCState  -- control state of each process
-- relation pointer (ph : phase)             -- current phase of the protocol

-- In TLA+: sent \subseteq Proc \times M
-- Since all messages are <<p, "ECHO">>, we only need to track which processes have sent
-- sent is the set of processes that have sent messages
-- relation sent (p : process)
individual sent : procSet
function rcvd (receiver : process) : procSet

set_option veil.deferVCGeneration true

veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

-- ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)
-- The conjuncts about `Nat` hold by the types of `N`, `T` and `F`.
assumption [NTF] N > 3 * T ∧ T ≥ F

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
after_init {
  sent := pset.empty
  rcvd P := pset.empty
  let V1Set ← pick procSet
  pc P := if pset.contains P V1Set then V1 else V0
  let corrSet :| pset.count corrSet = N - F
  Corr := corrSet
  Faulty := pset.diff (pset.ofList processEnumerable.allValues) Corr
}

-- ByzMsgs == Faulty \X M

-- Receive(self, includeByz) ==
--   \E newMessages \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {}) ) :
--     rcvd' = [ i \in Proc |-> IF i # self THEN rcvd[i] ELSE rcvd[self] \cup newMessages ]
-- ReceiveFromCorrectSender(self) == Receive(self, FALSE)
-- ReceiveFromAnySender(self) == Receive(self, TRUE)
procedure Receive (self : process) (includeByz : Bool) {
  let superSet := if includeByz then pset.union sent Faulty else sent
  let newMessages :| pset.isSubset newMessages superSet
  rcvd self := pset.union (rcvd self) newMessages
}

-- NOTE: `ReceiveFromCorrectSender` is not used in the `Step` part

procedure ReceiveFromAnySender (self : process) {
  Receive self true
}

/- This action is used to model the behavior of a process
doing nothing (stuttering) in TLA+, which corresponding to Line 160:
  `\/ UNCHANGED vars (* add a self-loop for terminating computations *)`
in bcastByz.tla.
With this action, we can not only obtain the same
number of `distinct states` as TLA+ verision, but `total states` as well.-/
action Stutter {
  pure ()
}

-- UponV1(self) ==
--   /\ pc[self] = "V1"
--   /\ pc' = [pc EXCEPT ![self] = "SE"]
--   /\ sent' = sent \cup { <<self, "ECHO">> }
--   /\ UNCHANGED << Corr, Faulty >>
action Step_UponV1 (self : process) {
  require isCorrect self
  require pc self = V1
  ReceiveFromAnySender self
  pc self := SE
  sent := pset.insert self sent
}

-- UponNonFaulty(self) ==
--   /\ pc[self] \in { "V0", "V1" }
--   /\ Cardinality(rcvd'[self]) >= N - 2*T
--   /\ Cardinality(rcvd'[self]) < N - T
--   /\ pc' = [ pc EXCEPT ![self] = "SE" ]
--   /\ sent' = sent \cup { <<self, "ECHO">> }
--   /\ UNCHANGED << Corr, Faulty >>
action Step_UponNonFaulty (self : process) {
  require isCorrect self
  require pc self ∈ [V0, V1]
  ReceiveFromAnySender self
  assume pset.count (rcvd self) ≥ N - 2 * T
  assume pset.count (rcvd self) < N - T
  pc self := SE
  sent := pset.insert self sent
}

-- UponAcceptNotSentBefore(self) ==
--   /\ pc[self] \in { "V0", "V1" }
--   /\ Cardinality(rcvd'[self]) >= N - T
--   /\ pc' = [ pc EXCEPT ![self] = "AC" ]
--   /\ sent' = sent \cup { <<self, "ECHO">> }
--   /\ UNCHANGED << Corr, Faulty >>
action Step_UponAcceptNotSentBefore (self : process) {
  require isCorrect self
  require pc self ∈ [V0, V1]
  ReceiveFromAnySender self
  assume pset.count (rcvd self) ≥ N - T
  pc self := AC
  sent := pset.insert self sent
}

-- UponAcceptSentBefore(self) ==
--   /\ pc[self] = "SE"
--   /\ Cardinality(rcvd'[self]) >= N - T
--   /\ pc' = [pc EXCEPT ![self] = "AC"]
--   /\ sent' = sent
--   /\ UNCHANGED << Corr, Faulty >>
action Step_UponAcceptorSentBefore (self : process) {
  require isCorrect self
  require pc self = SE
  ReceiveFromAnySender self
  assume pset.count (rcvd self) ≥ N - T
  pc self := AC
}

-- Step(self) ==
--   /\ ReceiveFromAnySender(self)
--   /\ \/ UponV1(self)
--      \/ UponNonFaulty(self)
--      \/ UponAcceptNotSentBefore(self)
--      \/ UponAcceptSentBefore(self)

-- Parameter constraints from TLA+ specification
-- TypeOK == /\ N \in Nat \ {0}
--           /\ T \in Nat
--           /\ F \in Nat
--           /\ N > 3 * T
--           /\ T >= F
-- procedure ByzMsgs {
--   return pset.remove M Faulty
-- }

invariant [Corr_cup_faulty_eq_proc] pset.union Corr Faulty == (pset.ofList processEnumerable.allValues)
invariant [card_corr] pset.count Corr ≥ N - T
invariant [card_faulty] pset.count Faulty ≤ T

termination false

#gen_spec

-- TLC checks this spec with `Benchmarks/TLA/TLAPlusExamples/bcastByz.cfg`.
-- The second check below, commented out, uses the cfg's instance; uncomment it to run it.
-- The first check, which runs when this file is built, uses 4 processes.
--
-- The instantiation (first `{ ... }` argument) sets the module's `type`s and `param`s:
-- * `process := Fin 5`: the processes are `0..4` (cfg: `N = 5`, with `Proc == 1 .. N`).
--   Here the processes are a type of their own, so `process` must agree with `N` below.
-- * `procSet := OrdList (Fin 5)`: `OrdList` has the `TSet` instance that the `instantiate` line
--   above requires.
-- The theory (second `{ ... }` argument) sets the module's `immutable` fields:
-- * `N := 5`: the number of processes (cfg: `N = 5`).
-- * `T := 1`: the upper bound on the number of faulty processes (cfg: `T = 1`).
-- * `F := 1`: the actual number of faulty processes (cfg: `F = 1`).
--
-- Before searching, `#model_check` checks these values against the `assumption [NTF]` above,
-- which is the spec's `ASSUME NTF`.
--
-- The other settings of the cfg:
-- * `INVARIANTS FCConstraints`: `#model_check` checks every `invariant` of the module. Here
--   `Corr_cup_faulty_eq_proc`, `card_corr` and `card_faulty` are the conjuncts of `FCConstraints`.
-- * The cfg has no `CHECK_DEADLOCK`, so TLC checks for deadlocks. With `termination false`
--   above, Veil also reports every state without successors as a deadlock. Every state has a
--   successor in both specs: `UNCHANGED vars` in TLA+ and the action `Stutter` here.
-- Options:
-- * The first check names no mode, so its search starts in Lean's interpreter and moves to a
--   compiled checker once that is built.
-- * `compiled` runs the search only in a compiled checker, not in Lean's interpreter.
-- * `(seenSet := HAMTMapShard)`: the sharded map of visited states uses `HAMTMapShard`.
-- TEST ONLY
#model_check
{ process := (Fin 4),
  procSet := OrdList (Fin 4) }
{ N := 4,
  T := 1,
  F := 1 }
-- TEST ONLY

/- EVAL
#model_check compiled
{ process := (Fin 5),
  procSet := OrdList (Fin 5) }
{ N := 5,
  T := 1,
  F := 1 } (seenSet := HAMTMapShard)
-/

end BcastByz
