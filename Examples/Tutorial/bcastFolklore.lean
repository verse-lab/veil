import Veil

open Std
/-
An encoding of a parameterized model of the reliable broadcast by message diffusion [1]
with crashed failures. This broadcast algorithm is described in Fig. 4 of [1].

[1] Chandra, Tushar Deepak, and Sam Toueg. "Unreliable failure detectors for reliable
    distributed systems." Journal of the ACM (JACM) 43.2 (1996): 225-267.

A short description of the parameterized model is described in:

[2] Gmeiner, Annu, et al. "Tutorial on parameterized model checking of fault-tolerant
    distributed algorithms." International School on Formal Methods for the Design of
    Computer, Communication and Software Systems. Springer International Publishing, 2014.

Igor Konnov, Thanh Hai Tran, Josef Widder, 2016

Protocol overview:
- N processes, up to F can crash (where N > 2*T and T >= F >= 0)
- Processes can be in states: V0 (no INIT), V1 (received INIT), AC (accepted), CR (crashed)
- Correct processes broadcast ECHO messages and can crash
- A correct process accepts when it receives messages

Properties:
- Unforgeability: if no correct process broadcasts, then no correct process accepts
- Correctness: if a correct process broadcasts, then every correct process eventually accepts
- Relay: if a correct process accepts, then every correct process eventually accepts
- Reliable channel: messages sent by correct processes are eventually received by all correct processes
-/

veil module BcastFolklore

-- Type definitions
type process
type procSet
instantiate pset : TSet process procSet

-- Process control states
enum PCState = { V0, V1, AC, CR }

-- Constants
-- N: total number of processes
-- T: threshold parameter (N > 2*T)
-- F: actual number of processes that can crash (T >= F >= 0)
immutable individual N : Nat
immutable individual T : Nat
immutable individual F : Nat
immutable individual Proc : procSet

-- State variables
individual Corr : procSet              -- set of correct (non-crashed) processes
individual nCrashed : Nat              -- number of crashed processes
relation pc (p : process) (st : PCState)  -- control state of each process
individual sent : procSet              -- processes that have sent ECHO (since M = {"ECHO"})
function rcvd (receiver : process) : procSet  -- processes from which receiver has received ECHO

#gen_state

-- Ghost definitions for readability
ghost relation isCorrect (p : process) := pset.contains p Corr
ghost relation subset (s1 s2 : procSet) := ∀ p, pset.contains p s1 → pset.contains p s2

-- Initial state
-- Init ==
--   /\ nCrashed = 0
--   /\ Corr = 1 .. N (all processes)
--   /\ sent = {}
--   /\ pc \in [ Proc -> {"V0", "V1"} ]
--   /\ rcvd = [ i \in Proc |-> {} ]
after_init {
  nCrashed := 0
  Corr := Proc  -- Initially all processes are correct
  sent := pset.empty
  rcvd P := pset.empty
  -- Non-deterministically initialize some processes with V1 (received INIT), others with V0
  let (initV1 : procSet) :| true  -- Non-deterministic subset of processes that received INIT
  pc P ST := if pset.contains P initV1 then ST == V1 else ST == V0
}

-- Procedure: Receive messages
-- Receive(self) ==
--   /\ pc[self] # "CR"
--   /\ \E msgs \in SUBSET (Proc \times M):
--         /\ msgs \subseteq sent
--         /\ rcvd[self] \subseteq msgs
--         /\ rcvd' = [rcvd EXCEPT ![self] = msgs ]
procedure Receive (self : process) {
  require pc self CR == false
  -- Non-deterministically receive a superset of already received messages
  -- that is a subset of sent messages
  let newMsgs :| subset (rcvd self) newMsgs ∧ subset newMsgs sent
  rcvd self := newMsgs
}

-- UponV1(self) ==
--   /\ pc[self] = "V1"
--   /\ pc' = [pc EXCEPT ![self] = "AC"]
--   /\ sent' = sent \cup { <<self, "ECHO">> }
--   /\ nCrashed' = nCrashed
--   /\ Corr' = Corr
action UponV1 (self : process) {
  require isCorrect self
  require pc self V1
  Receive self
  pc self ST := ST == AC
  sent := pset.insert self sent
}

-- UponAccept(self) ==
--   /\ (pc[self] = "V0" \/ pc[self] = "V1")
--   /\ rcvd'[self] # {}
--   /\ pc' = [pc EXCEPT ![self] = "AC"]
--   /\ sent' = sent \cup { <<self, "ECHO">> }
--   /\ nCrashed' = nCrashed
--   /\ Corr' = Corr
action UponAccept (self : process) {
  require isCorrect self
  require pc self V0 ∨ pc self V1
  Receive self
  require pset.count (rcvd self) > 0  -- rcvd'[self] # {}
  pc self ST := ST == AC
  sent := pset.insert self sent
}

-- UponCrash(self) ==
--   /\ nCrashed < F
--   /\ pc[self] # "CR"
--   /\ nCrashed' = nCrashed + 1
--   /\ pc' = [pc EXCEPT ![self] = "CR"]
--   /\ sent' = sent
--   /\ Corr' = Corr \ { self }
action UponCrash (self : process) {
  require isCorrect self
  require nCrashed < F
  require pc self CR == false
  Receive self
  nCrashed := nCrashed + 1
  pc self ST := ST == CR
  Corr := pset.remove self Corr
}

-- Step(self) ==
--   /\ Receive(self)
--   /\ \/ UponV1(self)
--      \/ UponAccept(self)
--      \/ UponCrash(self)
--      \/ UNCHANGED << pc, sent, nCrashed, Corr >>
-- (The individual actions above already include Receive)

-- Type invariant
-- TypeOK ==
--   /\ sent \in SUBSET (Proc \times M)
--   /\ pc \in [ Proc -> {"V0", "V1", "AC", "CR"} ]
--   /\ rcvd \in [ Proc -> SUBSET (Proc \times M) ]
--   /\ nCrashed \in 0..N
--   /\ Corr \in SUBSET Proc
invariant [typeOK] N > 2 * T ∧ T >= F ∧ F >= 0 ∧ N > 0
invariant [nCrashed_bound] nCrashed >= 0 ∧ nCrashed <= N
invariant [Corr_subset_Proc] subset Corr Proc
invariant [crashed_count] pset.count Corr + nCrashed == N

-- Unforgeability: if no correct process broadcasts, then no correct process accepts
-- Unforg == (\A self \in Corr: (pc[self] /= "AC"))
invariant [unforgeability] (∀ p : process, isCorrect p → pc p V1 == false) →
                            (∀ p : process, isCorrect p → pc p AC == false)

#gen_spec

-- Model checking configuration
#model_check
{ process := (Fin 4),
  procSet := (Std.ExtTreeSet (Fin 4) compare)}
{ N := 4,
  T := 1,
  F := 1,
  Proc := (Std.ExtTreeSet.empty.insertMany (List.finRange 4))}

end BcastFolklore
