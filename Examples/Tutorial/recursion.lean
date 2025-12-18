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
-- --------------------------------- MODULE raft ---------------------------------
-- \* This is the formal specification for the Raft consensus algorithm.
-- \*
-- \* Copyright 2014 Diego Ongaro.
-- \* This work is licensed under the Creative Commons Attribution-4.0
-- \* International License https://creativecommons.org/licenses/by/4.0/

-- EXTENDS Naturals, FiniteSets, Sequences, TLC
class TMultiset (α : Type) (κ : Type) where
  empty : κ
  insert : α → κ → κ
  remove : α → κ → κ
  contains : α → κ → Bool
  count : α → κ → Nat
  size : κ → Nat
  toList : κ → List α
  empty_size : size empty = 0
  empty_count (elem : α) : count elem empty = 0
  empty_contains (elem : α) : contains elem empty = false
  contains_def (elem : α) (s : κ) :
    contains elem s = (count elem s > 0)
  count_insert_self (elem : α) (s : κ) :
    count elem (insert elem s) = count elem s + 1
  count_insert_other (elem₁ elem₂ : α) (s : κ) (h : elem₁ ≠ elem₂) :
    count elem₁ (insert elem₂ s) = count elem₁ s
  size_insert (elem : α) (s : κ)  :
    size (insert elem s) = size s + 1
  count_remove_self (elem : α) (s : κ) :
    count elem (remove elem s) = if count elem s > 0 then count elem s - 1 else 0
  count_remove_other (elem₁ elem₂ : α) (s : κ) (h : elem₁ ≠ elem₂) :
    count elem₁ (remove elem₂ s) = count elem₁ s
  size_remove (elem : α) (s : κ) :
    size (remove elem s) = if contains elem s then size s - 1 else size s


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


structure election (server value : Type) where
  eterm     : Nat
  eleader   : server
  elog      : List (log value) -- list of (term, value)
  evotes    : server
  evoterLog : server-- list of (term, value)
deriving Inhabited, DecidableEq, Ord, Lean.ToJson, Hashable, Repr

type electionSet
instantiate electionsSet: TSet (election server value) electionSet
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
  mentries      : List (Nat × value) -- list of (term, value)
  mlog          : List (Nat × value) -- list of (term, value)
  mcommitIndex  : Nat
  msource       : server
  mdest         : server
  mvoteGranted  : Bool
  msuccess      : Bool
  mmatchIndex   : Nat
deriving Inhabited, DecidableEq, Ord, Lean.ToJson, Hashable, Repr


type msetMsg
type setLog

instantiate mSet: TMultiset (Message value server) msetMsg

individual messages : msetMsg

instantiate logSet: TSet (log value) setLog
-- \* A history variable used in the proof. This would not be present in an
-- \* implementation.
-- \* Keeps track of every log ever in the system (set of logs).
-- VARIABLE allLogs
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
function votesResponded : server → List server
-- \* The set of servers from which the candidate has received a vote in its
-- \* currentTerm.
-- VARIABLE votesGranted
function votesGranted : server → List server
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
  votesResponded S := []
  votesGranted S := []
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
  votesResponded i := []
  votesGranted i := []
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
  votesResponded i := []
  votesGranted i := []
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
  require ¬ (j ∈ votesResponded i)
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
  -- let msg : Message value server :=
  --   { mtype         := MsgType.AppendEntriesRequest,
  --     mterm         := 0,
  --     mlastLogTerm  := 0,
  --     mlastLogIndex := 0,
  --     mprevLogIndex := 0,
  --     mprevLogTerm  := 0,
  --     mentries      := [],
  --     mlog          := [],
  --     mcommitIndex  := commitIdx,
  --     msource       := i,
  --     mdest         := j,
  --     mvoteGranted  := false,
  --     msuccess      := false,
  --     mmatchIndex   := 0
  --     }
  let msg : Message value server := default
  -- WithMessage msg
  -- messages := mSet.insert msg messages
  Send msg
}

#gen_spec

end Raft
