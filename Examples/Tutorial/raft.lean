import Veil
import Veil.Core.Tools.ModelChecker.TransitionSystem
import Veil.Core.Tools.ModelChecker.Interface
import Veil.Core.Tools.ModelChecker.Concrete.Checker
import Mathlib.Data.FinEnum
import Mathlib.Tactic.ProxyType
-- import Veil.Core.Tools.Checker.Concrete.Main
open Lean

open Std

veil module Raft

section VariousByEquiv

variable {α : Type u} {β : Type v} [Ord α] [Ord β] (equiv : α ≃ β)
  (hmorph : ∀ (a1 a2 : α), compare a1 a2 = compare (equiv a1) (equiv a2))

include hmorph

def Std.TransOrd.by_equiv [inst : Std.TransOrd α] : Std.TransOrd β where
  eq_swap := by
    intro b1 b2
    rw [← equiv.right_inv b1, ← equiv.right_inv b2] ; dsimp [Equiv.coe_fn_mk]
    repeat rw [← hmorph]
    apply inst.eq_swap
  isLE_trans := by
    intro b1 b2 b3
    rw [← equiv.right_inv b1, ← equiv.right_inv b2, ← equiv.right_inv b3] ; dsimp [Equiv.coe_fn_mk]
    repeat rw [← hmorph]
    apply inst.isLE_trans

def Std.LawfulEqOrd.by_equiv [inst : Std.LawfulEqOrd α] : Std.LawfulEqOrd β where
  compare_self := by
    intro b ; specialize hmorph (equiv.symm b) (equiv.symm b) ; grind
  eq_of_compare := by
    intro b1 b2
    rw [← equiv.right_inv b1, ← equiv.right_inv b2] ; dsimp [Equiv.coe_fn_mk]
    repeat rw [← hmorph]
    simp

end VariousByEquiv
-- --------------------------------- MODULE raft ---------------------------------
-- \* This is the formal specification for the Raft consensus algorithm.
-- \*
-- \* Copyright 2014 Diego Ongaro.
-- \* This work is licensed under the Creative Commons Attribution-4.0
-- \* International License https://creativecommons.org/licenses/by/4.0/

-- EXTENDS Naturals, FiniteSets, Sequences, TLC

-- \* The set of server IDs
-- CONSTANTS Server
type server
-- \* The set of requests that can go into the log
-- CONSTANTS Value
type value
-- \* Server states.
-- CONSTANTS Follower, Candidate, Leader
-- type follower
-- type candidate
-- type leader
enum states = { Follower, Candidate, Leader }
-- \* A reserved value.
-- CONSTANTS Nil

-- \* Message types:
-- CONSTANTS RequestVoteRequest, RequestVoteResponse,
--           AppendEntriesRequest, AppendEntriesResponse
-- ----
-- \* Global variables
inductive MsgType where
  | RequestVoteRequest
  | RequestVoteResponse
  | AppendEntriesRequest
  | AppendEntriesResponse
deriving Inhabited, DecidableEq, Ord, Lean.ToJson, Hashable, Repr


instance : FinEnum MsgType :=
  FinEnum.ofList
    [MsgType.RequestVoteRequest, MsgType.RequestVoteResponse, MsgType.AppendEntriesRequest, MsgType.AppendEntriesResponse]
    (by simp; intro x; cases x <;> simp )

instance : Std.TransOrd MsgType where
  eq_swap := by intro a b; cases a <;> cases b <;> decide
  isLE_trans := by intro a b c; cases a <;> cases b <;> cases c <;> decide

instance : Std.LawfulEqOrd MsgType where
  compare_self := by intro a; cases a <;> decide
  eq_of_compare := by intro a b; cases a <;> cases b <;> decide


instance [FinEnum α] : Veil.Enumeration α where
  allValues := FinEnum.toList α
  complete := FinEnum.mem_toList

-- \* A history variable used in the proof. This would not be present in an
-- \* implementation.
-- \* Keeps track of successful elections, including the initial logs of the
-- \* leader and voters' logs. Set of functions containing various things about
-- \* successful elections (see BecomeLeader).
-- VARIABLE elections
structure log (value : Type) where
  term : Nat
  value : value
deriving Inhabited, DecidableEq, Ord, Lean.ToJson, Hashable, Repr

namespace log
-- instance {α β γ : Type} [FinEnum α] [FinEnum β] [FinEnum γ] : FinEnum (Voted α β γ) :=
--   FinEnum.ofEquiv _
--     { toFun := fun v => (v.bal, v.slot, v.val)
--       invFun := fun (b, s, v) => { bal := b, slot := s, val := v }
--       left_inv := by intro v; cases v; simp
--       right_inv := by intro x; simp }


variable {α : Type}
-- instance instFinEnumLog : FinEnum (log α) :=
--   FinEnum.ofEquiv _
--     { toFun := fun v => (v.term, v.value)
--       invFun := fun (a, b) => { term := a, value := b }
--       left_inv := by intro v; cases v; simp
--       right_inv := by intro x; simp }


def logEquiv : log α ≃ (Nat × α) where
  toFun v := (v.term, v.value)
  invFun := fun (a, b) => { term := a, value := b }
  left_inv := by intro v; cases v; rfl
  right_inv := by intro p; rfl

theorem log_compare_hmorph
  [Ord α] (v1 v2 : log α) :
  compare v1 v2 = compare (logEquiv v1) (logEquiv v2) := by
  simp [Ord.compare, logEquiv, instOrdLog.ord]

instance instTransOrdForLog
  [Ord α]
  [Std.TransOrd α]
  : Std.TransOrd (log α) :=
  @Std.TransOrd.by_equiv (Nat × α) (log α) _ _ logEquiv.symm
    (fun a1 a2 => (log_compare_hmorph (logEquiv.symm a1) (logEquiv.symm a2)).symm)
    inferInstance

instance instLawfulEqOrdForLog
  [Ord α]
  [Std.LawfulEqOrd α]
  : Std.LawfulEqOrd (log α) :=
  @Std.LawfulEqOrd.by_equiv (Nat × α) (log α) _ _ logEquiv.symm
    (fun a1 a2 => (log_compare_hmorph (logEquiv.symm a1) (logEquiv.symm a2)).symm)
    inferInstance
end log

type serverSet
instantiate serversSet: TSet server serverSet

structure election (server value serverSet: Type) where
  eterm     : Nat
  eleader   : server
  elog      : List (log value) -- list of (term, value)
  evotes    : serverSet
  evoterLog : List (log value) -- list of (term, value)
deriving Inhabited, DecidableEq, Ord, Lean.ToJson, Hashable, Repr

namespace election
variable {α β γ : Type}

def electionEquiv : election α β γ ≃ (Nat × α × List (log β) × γ × List (log β)) where
  toFun e := (e.eterm, e.eleader, e.elog, e.evotes, e.evoterLog)
  invFun := fun (a, b, c, d, f) => {
    eterm     := a,
    eleader   := b,
    elog      := c,
    evotes    := d,
    evoterLog := f
  }
  left_inv := by intro v; cases v; rfl
  right_inv := by intro p; rfl

theorem election_compare_hmorph
  [Ord α] [Ord β] [Ord γ]
  (e1 e2 : election α β γ) :
  compare e1 e2 = compare (electionEquiv e1) (electionEquiv e2) := by
  simp [Ord.compare, electionEquiv, instOrdElection.ord]

instance instTransOrdForElection
  [Ord α] [Ord β] [Ord γ]
  [Std.TransOrd α]
  [Std.TransOrd β]
  [Std.TransOrd γ]
  : Std.TransOrd (election α β γ) :=
  @Std.TransOrd.by_equiv
    (Nat × α × List (log β) × γ × List (log β))
    (election α β γ)
    _ _
    electionEquiv.symm
    (fun a1 a2 => (election_compare_hmorph (electionEquiv.symm a1) (electionEquiv.symm a2)).symm)
    inferInstance


instance instLawfulEqOrdForElection
  [Ord α] [Ord β] [Ord γ]
  [Std.LawfulEqOrd α]
  [Std.LawfulEqOrd β]
  [Std.LawfulEqOrd γ]
  : Std.LawfulEqOrd (election α β γ) :=
  @Std.LawfulEqOrd.by_equiv
    (Nat × α × List (log β) × γ × List (log β))
    (election α β γ)
    _ _
    electionEquiv.symm
    (fun a1 a2 => (election_compare_hmorph (electionEquiv.symm a1) (electionEquiv.symm a2)).symm)
    inferInstance
end election

type electionSet
instantiate electionsSet: TSet (election server value serverSet) electionSet
individual elections : electionSet

-- \* A bag of records representing requests and responses sent from one server
-- \* to another. TLAPS doesn't support the Bags module, so this is a function
-- \* mapping Message to Nat.
-- VARIABLE messages
structure Message (value server : Type) where
  mtype         : MsgType
  mterm         : Nat
  mlastLogTerm  : Nat
  mlastLogIndex : Nat
  mprevLogIndex : Nat
  mprevLogTerm  : Nat
  mentries      : List (log value) -- list of (term, value)
  mlog          : List (log value) -- list of (term, value)
  mcommitIndex  : Nat
  msource       : server
  mdest         : server
  mvoteGranted  : Bool
  msuccess      : Bool
  mmatchIndex   : Nat
deriving Inhabited, DecidableEq, Ord, Lean.ToJson, Hashable, Repr


namespace Message
variable {α β : Type}
#check Veil.FieldRepresentation
def messageEquiv : Message α β ≃
  ( MsgType × Nat × Nat × Nat × Nat × Nat × List (log α) × List (log α)
    × Nat × β × β × Bool × Bool × Nat ) where
  toFun m := (
    m.mtype, m.mterm, m.mlastLogTerm, m.mlastLogIndex, m.mprevLogIndex,
    m.mprevLogTerm, m.mentries, m.mlog, m.mcommitIndex,
    m.msource, m.mdest, m.mvoteGranted, m.msuccess, m.mmatchIndex)
  invFun := fun (a, b, c, d, e, f, g, h, i, j, k, l, m, n) => {
    mtype         := a,
    mterm         := b,
    mlastLogTerm  := c,
    mlastLogIndex := d,
    mprevLogIndex := e,
    mprevLogTerm  := f,
    mentries      := g,
    mlog          := h,
    mcommitIndex  := i,
    msource       := j,
    mdest         := k,
    mvoteGranted  := l,
    msuccess      := m,
    mmatchIndex   := n
  }
  left_inv := by intro v; cases v; rfl
  right_inv := by intro p; rfl

theorem message_compare_hmorph
  [Ord α] [Ord β]
  (m1 m2 : Message α β) :
  compare m1 m2 = compare (messageEquiv m1) (messageEquiv m2) := by
  simp [Ord.compare, messageEquiv, instOrdMessage.ord]

-- set_option synthInstance.maxSize 2000
-- set_option trace.Meta.synthInstance true
instance instTransOrdForMessage
  [Ord α] [Ord β]
  [Std.TransOrd α]
  [Std.TransOrd β]
  : Std.TransOrd (Message α β) :=
  @Std.TransOrd.by_equiv
    ( MsgType × Nat × Nat × Nat × Nat × Nat × List (log α) × List (log α)
      × Nat × β × β × Bool × Bool × Nat )
    (Message α β)
    _ _
    messageEquiv.symm
    (fun a1 a2 => (message_compare_hmorph (messageEquiv.symm a1) (messageEquiv.symm a2)).symm)
    inferInstance

instance instLawfulEqOrdForMessage
  [Ord α]
  [Ord β]
  [Std.LawfulEqOrd α]
  [Std.LawfulEqOrd β]
  : Std.LawfulEqOrd (Message α β) :=
  @Std.LawfulEqOrd.by_equiv
    ( MsgType × Nat × Nat × Nat × Nat × Nat × List (log α) × List (log α)
      × Nat × β × β × Bool × Bool × Nat )
    (Message α β)
    _ _
    messageEquiv.symm
    (fun a1 a2 => (message_compare_hmorph (messageEquiv.symm a1) (messageEquiv.symm a2)).symm)
    inferInstance
end Message


type msetMsg
type setLog
instantiate mSet: TMultiset (Message value server) msetMsg
individual messages : msetMsg

-- \* A history variable used in the proof. This would not be present in an
-- \* implementation.
-- \* Keeps track of every log ever in the system (set of logs).
-- VARIABLE allLogs
instantiate logSet: TSet (log value) setLog
individual allLogs : setLog

-- \* The following variables are all per server (functions with domain Server).

-- \* The server's term number.
-- VARIABLE currentTerm
function currentTerm : server → Nat

-- \* The server's state (Follower, Candidate, or Leader).
-- VARIABLE state
relation serverState : server → states → Bool
-- \* The candidate the server voted for in its current term, or
-- \* Nil if it hasn't voted for any.
-- VARIABLE votedFor
relation votedFor : server → server → Bool

-- serverVars == <<currentTerm, state, votedFor>>

-- \* A Sequence of log entries. The index into this sequence is the index of the
-- \* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
-- \* with index 1, so be careful not to use that!
-- VARIABLE log
function logs : server → List (log value)
-- \* The index of the latest entry in the log the state machine may apply.
-- VARIABLE commitIndex
individual commitIndex : Nat
-- logVars == <<log, commitIndex>>


-- \* The following variables are used only on candidates:
-- \* The set of servers from which the candidate has received a RequestVote
-- \* response in its currentTerm.
-- VARIABLE votesResponded
function votesResponded : server → serverSet
-- \* The set of servers from which the candidate has received a vote in its
-- \* currentTerm.
-- VARIABLE votesGranted
function votesGranted : server → serverSet
-- \* A history variable used in the proof. This would not be present in an
-- \* implementation.
-- \* Function from each server that voted for this candidate in its currentTerm
-- \* to that voter's log.
-- VARIABLE voterLog
function voterLog : server → List (log value)

-- candidateVars == <<votesResponded, votesGranted, voterLog>>

-- \* The following variables are used only on leaders:
-- \* The next entry to send to each follower.
-- VARIABLE nextIndex
-- \* The latest entry that each follower has acknowledged is the same as the
-- \* leader's. This is used to calculate commitIndex on the leader.
-- VARIABLE matchIndex
function nextIndex : server → server → Nat
function matchIndex : server → server → Nat
-- leaderVars == <<nextIndex, matchIndex, elections>>

-- \* End of per server variables.
-- ----
#gen_state


-- \* All variables; used for stuttering (asserting state hasn't changed).
-- vars == <<messages, allLogs, serverVars, candidateVars, leaderVars, logVars>>

-- ----
-- \* Helpers

-- \* The set of all quorums. This just calculates simple majorities, but the only
-- \* important property is that every quorum overlaps with every other.
-- Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

-- \* The term of the last entry in a log, or 0 if the log is empty.
-- LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term
procedure LastTerm (xlog : List (log value)) {
  -- if xlog.length == 0 then default else (xlog.get! (xlog.length - 1)).term
  /-In TLA+, here return `0` not default. -/
  let res := if xlog.length ≠ 0 then xlog.getLast!.term else 0
  return res
}
-- \* Helper for Send and Reply. Given a message m and bag of messages, return a
-- \* new bag of messages with one more m in it.
-- WithMessage(m, msgs) ==
--     IF m \in DOMAIN msgs THEN
--         [msgs EXCEPT ![m] = msgs[m] + 1]
--     ELSE
--         msgs @@ (m :> 1)

-- class TMultiset (α : Type) (κ : Type) where
--   empty : κ
--   insert : α → κ → κ
--   remove : α → κ → κ
--   contains : α → κ → Bool
--   count : α → κ → Nat
--   size : κ → Nat
--   toList : κ → List α
--   empty_size : size empty = 0
--   empty_count (elem : α) : count elem empty = 0
--   empty_contains (elem : α) : contains elem empty = false
--   contains_def (elem : α) (s : κ) :
--     contains elem s = (count elem s > 0)
--   count_insert_self (elem : α) (s : κ) :
--     count elem (insert elem s) = count elem s + 1
--   count_insert_other (elem₁ elem₂ : α) (s : κ) (h : elem₁ ≠ elem₂) :
--     count elem₁ (insert elem₂ s) = count elem₁ s
--   size_insert (elem : α) (s : κ)  :
--     size (insert elem s) = size s + 1
--   count_remove_self (elem : α) (s : κ) :
--     count elem (remove elem s) = if count elem s > 0 then count elem s - 1 else 0
--   count_remove_other (elem₁ elem₂ : α) (s : κ) (h : elem₁ ≠ elem₂) :
--     count elem₁ (remove elem₂ s) = count elem₁ s
--   size_remove (elem : α) (s : κ) :
--     size (remove elem s) = if contains elem s then size s - 1 else size s
procedure WithMessage (m : Message value server) {
  messages := mSet.insert m messages
}

-- \* Helper for Discard and Reply. Given a message m and bag of messages, return
-- \* a new bag of messages with one less m in it.
-- WithoutMessage(m, msgs) ==
--     IF m \in DOMAIN msgs THEN
--         IF msgs[m] <= 1 THEN [i \in DOMAIN msgs \ {m} |-> msgs[i]]
--         ELSE [msgs EXCEPT ![m] = msgs[m] - 1]
--     ELSE
--         msgs
procedure WithoutMessage (m : Message value server) {
  messages := mSet.remove m messages
}

-- \* Add a message to the bag of messages.
-- Send(m) == messages' = WithMessage(m, messages)
procedure Send (m : Message value server) {
  WithMessage m
}

-- \* Remove a message from the bag of messages. Used when a server is done
-- \* processing a message.
-- Discard(m) == messages' = WithoutMessage(m, messages)
procedure Discard (m : Message value server) {
  WithoutMessage m
}

-- \* Combination of Send and Discard
-- Reply(response, request) ==
--     messages' = WithoutMessage(request, WithMessage(response, messages))
procedure Reply (response request : Message value server) {
  WithMessage response
  WithoutMessage request
}



-- \* Return the minimum value from a set, or undefined if the set is empty.
-- Min(s) == CHOOSE x \in s : \A y \in s : x <= y

-- \* Return the maximum value from a set, or undefined if the set is empty.
-- Max(s) == CHOOSE x \in s : \A y \in s : x >= y

-- ----
-- \* Define initial values for all variables

-- InitHistoryVars == /\ elections = {}
--                    /\ allLogs   = {}
--                    /\ voterLog  = [i \in Server |-> [j \in {} |-> <<>>]]
procedure InitHistoryVars {
  allLogs    := logSet.empty
  elections  := electionsSet.empty
  voterLog S := []
}
-- InitServerVars == /\ currentTerm = [i \in Server |-> 1]
--                   /\ state       = [i \in Server |-> Follower]
--                   /\ votedFor    = [i \in Server |-> Nil]
procedure InitServerVars {
  serverState S T := T == Follower
  currentTerm S := 1
  votedFor S R := false
}

-- InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
--                      /\ votesGranted   = [i \in Server |-> {}]
procedure InitCandidateVars {
  votesResponded S := serversSet.empty
  votesGranted S := serversSet.empty
}

-- \* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
-- \* leader does not send itself messages. It's still easier to include these
-- \* in the functions.
-- InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
--                   /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
procedure InitLeaderVars {
  nextIndex S R := 1
  matchIndex S R := 0
}
-- InitLogVars == /\ log          = [i \in Server |-> << >>]
--                /\ commitIndex  = [i \in Server |-> 0]
procedure InitLogVars {
  logs S := []
  commitIndex := 0
}
-- Init == /\ messages = [m \in {} |-> 0]
--         /\ InitHistoryVars
--         /\ InitServerVars
--         /\ InitCandidateVars
--         /\ InitLeaderVars
--         /\ InitLogVars
after_init {
  messages := mSet.empty
  InitHistoryVars
  InitServerVars
  InitCandidateVars
  InitLeaderVars
  InitLogVars
}

-- ----
-- \* Define state transitions

-- \* Server i restarts from stable storage.
-- \* It loses everything but its currentTerm, votedFor, and log.
-- Restart(i) ==
--     /\ state'          = [state EXCEPT ![i] = Follower]
--     /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
--     /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
--     /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
--     /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
--     /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
--     /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
--     /\ UNCHANGED <<messages, currentTerm, votedFor, log, elections>>
action Restart (i : server) {
  serverState i T := T == Follower
  votesResponded i := serversSet.empty
  votesGranted i := serversSet.empty
  voterLog i := []
  nextIndex i R := 1
  matchIndex i R := 0
  commitIndex := 0
}

-- \* Server i times out and starts a new election.
-- Timeout(i) == /\ state[i] \in {Follower, Candidate}
--               /\ state' = [state EXCEPT ![i] = Candidate]
--               /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
--               \* Most implementations would probably just set the local vote
--               \* atomically, but messaging localhost for it is weaker.
--               /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
--               /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
--               /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
--               /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
--               /\ UNCHANGED <<messages, leaderVars, logVars>>
action Timeout (i : server) {
  require serverState i Follower ∨ serverState i Candidate
  serverState i T := T == Candidate
  currentTerm i := currentTerm i + 1
  -- \* Most implementations would probably just set the local vote
  -- \* atomically, but messaging localhost for it is weaker.
  votedFor i R := false
  -- votesResponded i := []
  votesResponded i := serversSet.empty
  -- votesGranted i := []
  votesGranted i := serversSet.empty
  voterLog i := []
}


-- \* Candidate i sends j a RequestVote request.
-- RequestVote(i, j) ==
--     /\ state[i] = Candidate
--     /\ j \notin votesResponded[i]
--     /\ Send([mtype         |-> RequestVoteRequest,
--              mterm         |-> currentTerm[i],
--              mlastLogTerm  |-> LastTerm(log[i]),
--              mlastLogIndex |-> Len(log[i]),
--              msource       |-> i,
--              mdest         |-> j])
--     /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
action RequestVote (i : server) (j : server) {
  require serverState i Candidate
  require ¬ (serversSet.contains j (votesResponded i))
  let lastterm ← LastTerm (logs i)
  let msg : Message value server :=
    { mtype         := MsgType.RequestVoteRequest,
      mterm         := currentTerm i,
      mlastLogTerm  := lastterm,
      mlastLogIndex := List.length (logs i),
      mprevLogIndex := 0,
      mprevLogTerm  := 0,
      mentries      := [],
      mlog          := [],
      mcommitIndex  := 0,
      msource       := i,
      mdest         := j,
      mvoteGranted  := false,
      msuccess      := false,
      mmatchIndex   := 0 }
  Send msg
}


-- \* Leader i sends j an AppendEntries request containing up to 1 entry.
-- \* While implementations may want to send more than 1 at a time, this spec uses
-- \* just 1 because it minimizes atomic regions without loss of generality.
-- AppendEntries(i, j) ==
--     /\ i /= j
--     /\ state[i] = Leader
--     /\ LET prevLogIndex == nextIndex[i][j] - 1
--            prevLogTerm == IF prevLogIndex > 0 THEN
--                               log[i][prevLogIndex].term
--                           ELSE
--                               0
--            \* Send up to 1 entry, constrained by the end of the log.
--            lastEntry == Min({Len(log[i]), nextIndex[i][j]})
--            entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
--        IN Send([mtype          |-> AppendEntriesRequest,
--                 mterm          |-> currentTerm[i],
--                 mprevLogIndex  |-> prevLogIndex,
--                 mprevLogTerm   |-> prevLogTerm,
--                 mentries       |-> entries,
--                 \* mlog is used as a history variable for the proof.
--                 \* It would not exist in a real implementation.
--                 mlog           |-> log[i],
--                 mcommitIndex   |-> Min({commitIndex[i], lastEntry}),
--                 msource        |-> i,
--                 mdest          |-> j])
--     /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
-- set_option maxRecDepth 1000
action AppendEntries (i : server) (j : server) {
  require i ≠ j
  require serverState i Leader
  let prevLogIndex := nextIndex i j - 1
  let prevLogTerm : Nat :=
    if prevLogIndex > 0 then
      let log_i := (logs i : List (log value))
      let entry : log value := log_i.get!Internal (prevLogIndex - 1)
      entry.term
    else
      0
  let lastEntry := Nat.min (List.length (logs i)) (nextIndex i j)
  -- let entries := (logs i).slice (nextIndex i j - 1) lastEntry
  let entries : List (log value) := (logs i).drop (nextIndex i j - 1) |>.take (lastEntry - (nextIndex i j - 1))
  let commitIdx := Nat.min commitIndex lastEntry
  let msg : Message value server :=
    { mtype          := MsgType.AppendEntriesRequest,
      mterm          := currentTerm i,
      mlastLogTerm   := 0,
      mlastLogIndex  := 0,
      mprevLogIndex  := prevLogIndex,
      mprevLogTerm   := prevLogTerm,
      mentries       := entries,
      mlog           := [],
      mcommitIndex   := commitIdx,
      msource        := i,
      mdest          := j,
      mvoteGranted  := false,
      msuccess      := false,
      mmatchIndex   := 0 }
  -- let msg : Message value server := default
  -- Send msg
  messages := mSet.insert msg messages
}



-- \* Candidate i transitions to leader.
-- BecomeLeader(i) ==
--     /\ state[i] = Candidate
--     /\ votesGranted[i] \in Quorum
--     /\ state'      = [state EXCEPT ![i] = Leader]
--     /\ nextIndex'  = [nextIndex EXCEPT ![i] =
--                          [j \in Server |-> Len(log[i]) + 1]]
--     /\ matchIndex' = [matchIndex EXCEPT ![i] =
--                          [j \in Server |-> 0]]
--     /\ elections'  = elections \cup
--                          {[eterm     |-> currentTerm[i],
--                            eleader   |-> i,
--                            elog      |-> log[i],
--                            evotes    |-> votesGranted[i],
--                            evoterLog |-> voterLog[i]]}
-- structure election (server value : Type) where
--   eterm     : Nat
--   eleader   : server
--   elog      : List (log value) -- list of (term, value)
--   evotes    : server
--   evoterLog : List (log value) -- list of (term, value)
-- deriving Inhabited, DecidableEq, Ord, Lean.ToJson, Hashable, Repr

--     /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars>>
action BecomeLeader (i : server) {
  require serverState i Candidate
  -- require votesGranted i ∈ Quorum
  serverState i T := T == Leader
  nextIndex i R := List.length (logs i) + 1
  matchIndex i R := 0
  let newElection : election server value serverSet :=
    { eterm     := currentTerm i,
      eleader   := i,
      elog      := logs i,
      evotes    := votesGranted i,
      evoterLog := voterLog i }
  elections := electionsSet.insert newElection elections
}

-- \* Leader i receives a client request to add v to the log.
-- ClientRequest(i, v) ==
--     /\ state[i] = Leader
--     /\ LET entry == [term  |-> currentTerm[i],
--                      value |-> v]
--            newLog == Append(log[i], entry)
--        IN  log' = [log EXCEPT ![i] = newLog]
--     /\ UNCHANGED <<messages, serverVars, candidateVars,
--                    leaderVars, commitIndex>>
action ClientRequest (i : server) (v : value) {
  require serverState i Leader
  let entry : log value := { term := currentTerm i, value := v }
  let newLog := (logs i).append [entry]
  logs i := newLog
}

-- \* Leader i advances its commitIndex.
-- \* This is done as a separate step from handling AppendEntries responses,
-- \* in part to minimize atomic regions, and in part so that leaders of
-- \* single-server clusters are able to mark entries committed.
-- AdvanceCommitIndex(i) ==
--     /\ state[i] = Leader
--     /\ LET \* The set of servers that agree up through index.
--            Agree(index) == {i} \cup {k \in Server :
--                                          matchIndex[i][k] >= index}
--            \* The maximum indexes for which a quorum agrees
--            agreeIndexes == {index \in 1..Len(log[i]) :
--                                 Agree(index) \in Quorum}
--            \* New value for commitIndex'[i]
--            newCommitIndex ==
--               IF /\ agreeIndexes /= {}
--                  /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
--               THEN
--                   Max(agreeIndexes)
--               ELSE
--                   commitIndex[i]
--        IN commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
--     /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log>>


-- ----
-- \* Message handlers
-- \* i = recipient, j = sender, m = message
-- \* Server i receives a RequestVote request from server j with
-- \* m.mterm <= currentTerm[i].
-- HandleRequestVoteRequest(i, j, m) ==
--     LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
--                  \/ /\ m.mlastLogTerm = LastTerm(log[i])
--                     /\ m.mlastLogIndex >= Len(log[i])
--         grant == /\ m.mterm = currentTerm[i]
--                  /\ logOk
--                  /\ votedFor[i] \in {Nil, j}
--     IN /\ m.mterm <= currentTerm[i]
--        /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
--           \/ ~grant /\ UNCHANGED votedFor
--        /\ Reply([mtype        |-> RequestVoteResponse,
--                  mterm        |-> currentTerm[i],
--                  mvoteGranted |-> grant,
--                  \* mlog is used just for the `elections' history variable for
--                  \* the proof. It would not exist in a real implementation.
--                  mlog         |-> log[i],
--                  msource      |-> i,
--                  mdest        |-> j],
--                  m)
--        /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars>>
-- action HandleRequestVoteRequest (i : server) (j : server) (m : Message value server) {
--   let lastTerm_i ← LastTerm (logs i)
--   let logOk :=
--     (m.mlastLogTerm > lastTerm_i) ∨
--     ((m.mlastLogTerm == lastTerm_i) ∧ (m.mlastLogIndex >= List.length (logs i)))
--   let grant :=
--     (m.mterm == currentTerm i) ∧ logOk
--     -- ∧ (¬ votedFor i R ∨ votedFor i R == j)
--     ∧ (∀ P, votedFor i P → P == j)
--   require m.mterm <= currentTerm i
--   if (decide grant) then
--     votedFor i R := R == j
--   let response : Message value server :=
--     { mtype        := MsgType.RequestVoteResponse,
--       mterm        := currentTerm i,
--       mlastLogTerm := 0,
--       mlastLogIndex := 0,
--       mprevLogIndex := 0,
--       mprevLogTerm  := 0,
--       mentries      := [],
--       mlog         := logs i,
--       mcommitIndex  := 0,
--       msource      := i,
--       mdest        := j,
--       mvoteGranted := decide grant,
--       msuccess     := false,
--       mmatchIndex  := 0 }
--   Reply response m
-- }

-- \* Server i receives a RequestVote response from server j with
-- \* m.mterm = currentTerm[i].
-- HandleRequestVoteResponse(i, j, m) ==
--     \* This tallies votes even when the current state is not Candidate, but
--     \* they won't be looked at, so it doesn't matter.
--     /\ m.mterm = currentTerm[i]
--     /\ votesResponded' = [votesResponded EXCEPT ![i] =
--                               votesResponded[i] \cup {j}]
--     /\ \/ /\ m.mvoteGranted
--           /\ votesGranted' = [votesGranted EXCEPT ![i] =
--                                   votesGranted[i] \cup {j}]
--           /\ voterLog' = [voterLog EXCEPT ![i] =
--                               voterLog[i] @@ (j :> m.mlog)]
--        \/ /\ ~m.mvoteGranted
--           /\ UNCHANGED <<votesGranted, voterLog>>
--     /\ Discard(m)
--     /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars>>
procedure HandleRequestVoteResponse (i : server) (j : server) (m : Message value server) {
  require m.mterm == currentTerm i
  votesResponded i :=
    serversSet.insert j (votesResponded i)
  if m.mvoteGranted then
    votesGranted i := serversSet.insert j (votesGranted i)
    let newVoterLog := (voterLog i).append m.mlog
    voterLog i := newVoterLog
  Discard m
}


-- \* Server i receives an AppendEntries request from server j with
-- \* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
-- \* implementations could safely accept more by treating them the same as
-- \* multiple independent requests of 1 entry.
-- HandleAppendEntriesRequest(i, j, m) ==
--     LET logOk == \/ m.mprevLogIndex = 0
--                  \/ /\ m.mprevLogIndex > 0
--                     /\ m.mprevLogIndex <= Len(log[i])
--                     /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
--     IN /\ m.mterm <= currentTerm[i]
--        /\ \/ /\ \* reject request
--                 \/ m.mterm < currentTerm[i]
--                 \/ /\ m.mterm = currentTerm[i]
--                    /\ state[i] = Follower
--                    /\ \lnot logOk
--              /\ Reply([mtype           |-> AppendEntriesResponse,
--                        mterm           |-> currentTerm[i],
--                        msuccess        |-> FALSE,
--                        mmatchIndex     |-> 0,
--                        msource         |-> i,
--                        mdest           |-> j],
--                        m)
--              /\ UNCHANGED <<serverVars, logVars>>
--           \/ \* return to follower state
--              /\ m.mterm = currentTerm[i]
--              /\ state[i] = Candidate
--              /\ state' = [state EXCEPT ![i] = Follower]
--              /\ UNCHANGED <<currentTerm, votedFor, logVars, messages>>
--           \/ \* accept request
--              /\ m.mterm = currentTerm[i]
--              /\ state[i] = Follower
--              /\ logOk
--              /\ LET index == m.mprevLogIndex + 1
--                 IN \/ \* already done with request
--                        /\ \/ m.mentries = << >>
--                           \/ /\ m.mentries /= << >>
--                              /\ Len(log[i]) >= index
--                              /\ log[i][index].term = m.mentries[1].term
--                           \* This could make our commitIndex decrease (for
--                           \* example if we process an old, duplicated request),
--                           \* but that doesn't really affect anything.
--                        /\ commitIndex' = [commitIndex EXCEPT ![i] =
--                                               m.mcommitIndex]
--                        /\ Reply([mtype           |-> AppendEntriesResponse,
--                                  mterm           |-> currentTerm[i],
--                                  msuccess        |-> TRUE,
--                                  mmatchIndex     |-> m.mprevLogIndex +
--                                                      Len(m.mentries),
--                                  msource         |-> i,
--                                  mdest           |-> j],
--                                  m)
--                        /\ UNCHANGED <<serverVars, log>>
--                    \/ \* conflict: remove 1 entry
--                        /\ m.mentries /= << >>
--                        /\ Len(log[i]) >= index
--                        /\ log[i][index].term /= m.mentries[1].term
--                        /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |->
--                                           log[i][index2]]
--                           IN log' = [log EXCEPT ![i] = new]
--                        /\ UNCHANGED <<serverVars, commitIndex, messages>>
--                    \/ \* no conflict: append entry
--                        /\ m.mentries /= << >>
--                        /\ Len(log[i]) = m.mprevLogIndex
--                        /\ log' = [log EXCEPT ![i] =
--                                       Append(log[i], m.mentries[1])]
--                        /\ UNCHANGED <<serverVars, commitIndex, messages>>
--        /\ UNCHANGED <<candidateVars, leaderVars>>

-- \* Server i receives an AppendEntries response from server j with
-- \* m.mterm = currentTerm[i].
-- HandleAppendEntriesResponse(i, j, m) ==
--     /\ m.mterm = currentTerm[i]
--     /\ \/ /\ m.msuccess \* successful
--           /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
--           /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
--        \/ /\ \lnot m.msuccess \* not successful
--           /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
--                                Max({nextIndex[i][j] - 1, 1})]
--           /\ UNCHANGED <<matchIndex>>
--     /\ Discard(m)
--     /\ UNCHANGED <<serverVars, candidateVars, logVars, elections>>
-- action HandleAppendEntriesResponse (i : server) (j : server) (m : Message value server) {
--   require m.mterm == currentTerm i
--   if m.msuccess then
--     nextIndex i j := m.mmatchIndex + 1
--     matchIndex i j := m.mmatchIndex
--   else
--     nextIndex i j := Nat.max (nextIndex i j - 1) 1
--   Discard m
-- }

-- \* Any RPC with a newer term causes the recipient to advance its term first.
-- UpdateTerm(i, j, m) ==
--     /\ m.mterm > currentTerm[i]
--     /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
--     /\ state'          = [state       EXCEPT ![i] = Follower]
--     /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
--        \* messages is unchanged so m can be processed further.
--     /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars>>
procedure UpdateTerm (i : server) (m : Message value server) {
  require m.mterm > currentTerm i
  currentTerm i := m.mterm
  serverState i T := T == Follower
  votedFor i R := false
}

-- \* Responses with stale terms are ignored.
-- DropStaleResponse(i, j, m) ==
--     /\ m.mterm < currentTerm[i]
--     /\ Discard(m)
--     /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
procedure DropStaleResponse (i : server) (m : Message value server) {
  require m.mterm < currentTerm i
  Discard m
}

-- \* Receive a message.
-- Receive(m) ==
--     LET i == m.mdest
--         j == m.msource
--     IN \* Any RPC with a newer term causes the recipient to advance
--        \* its term first. Responses with stale terms are ignored.
--        \/ UpdateTerm(i, j, m)
--        \/ /\ m.mtype = RequestVoteRequest
--           /\ HandleRequestVoteRequest(i, j, m)
--        \/ /\ m.mtype = RequestVoteResponse
--           /\ \/ DropStaleResponse(i, j, m)
--              \/ HandleRequestVoteResponse(i, j, m)
--        \/ /\ m.mtype = AppendEntriesRequest
--           /\ HandleAppendEntriesRequest(i, j, m)
--        \/ /\ m.mtype = AppendEntriesResponse
--           /\ \/ DropStaleResponse(i, j, m)
--              \/ HandleAppendEntriesResponse(i, j, m)


-- \* End of message handlers.
-- ----
-- \* Network state transitions

-- \* The network duplicates a message
-- DuplicateMessage(m) ==
--     /\ Send(m)
--     /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
procedure DuplicateMessage (m : Message value server) {
  Send m
}

-- \* The network drops a message
-- DropMessage(m) ==
--     /\ Discard(m)
--     /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
procedure DropMessage (m : Message value server) {
  Discard m
}

#gen_spec

#print Theory
open Veil.ModelChecker

#synth TransOrd (Message (Fin 1) (Fin 1))
#synth Ord (Message (Fin 1) (Fin 1))
#synth LawfulEqOrd (Message (Fin 1) (Fin 1))

set_option trace.Meta.synthInstance true
#synth TMultiset (Message (Fin 1) (Fin 1)) (TMapMultiset (Message (Fin 1) (Fin 1)))

instance : Inhabited
    (State
      (FieldConcreteType (Fin 1) (Fin 1) states_IndT (ExtTreeSet (Fin 1) compare)
        (ExtTreeSet (election (Fin 1) (Fin 1) (ExtTreeSet (Fin 1) compare)) compare)
        (TMapMultiset (Message (Fin 1) (Fin 1))) (ExtTreeSet (log (Fin 1)) compare))) where
  default := {
    messages := default,
    allLogs := default,
    serverState := default,
    currentTerm := default,
    votedFor := default,
    votesResponded := default,
    votesGranted := default,
    voterLog := default,
    nextIndex := default,
    matchIndex := default,
    logs := default,
    commitIndex := default,
    elections := default
  }
#check election
#synth Veil.Enumeration (log (Fin 2))
#synth Veil.Enumeration ExtTreeSet (election (Fin 1) (Fin 1) (ExtTreeSet (Fin 1) compare))
#synth Veil.Enumeration (election (Fin 1) (Fin 1) (ExtTreeSet (Fin 1) compare))

#print Theory
def modelCheckerResult :=
  Concrete.findReachable
  (enumerableTransitionSystem
  (Fin 1)     -- server
  (Fin 1)     -- value
  states_IndT -- states
  (ExtTreeSet (Fin 1) compare) --serverSet
  -- electionSet
  (ExtTreeSet (election (Fin 1) (Fin 1) (ExtTreeSet (Fin 1) compare)) compare)
  -- msetMsg
  (TMapMultiset (Message (Fin 1) (Fin 1)))
  (ExtTreeSet (log (Fin 1)) compare)
  {} )
  {
  «safety» := {
    name := `sent_not_empty
    property := fun th st => true
  },
  -- terminating := {
  --   name := `allDone
  --   property := fun th st => allDone th st
  -- },
  earlyTerminationConditions := [
    EarlyTerminationCondition.foundViolatingState,
    EarlyTerminationCondition.reachedDepthBound 2
    EarlyTerminationCondition.deadlockOccurred
  ]
}

-- ----
-- \* Defines how the variables may transition.
-- Next == /\ \/ \E i \in Server : Restart(i)
--            \/ \E i \in Server : Timeout(i)
--            \/ \E i,j \in Server : RequestVote(i, j)
--            \/ \E i \in Server : BecomeLeader(i)
--            \/ \E i \in Server, v \in Value : ClientRequest(i, v)
--            \/ \E i \in Server : AdvanceCommitIndex(i)
--            \/ \E i,j \in Server : AppendEntries(i, j)
--            \/ \E m \in DOMAIN messages : Receive(m)
--            \/ \E m \in DOMAIN messages : DuplicateMessage(m)
--            \/ \E m \in DOMAIN messages : DropMessage(m)
--            \* History variable that tracks every log ever:
--         /\ allLogs' = allLogs \cup {log[i] : i \in Server}

-- \* The specification must start with the initial state and transition according
-- \* to Next.
-- Spec == Init /\ [][Next]_vars

-- ===============================================================================
end Raft
