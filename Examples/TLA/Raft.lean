module

public import Veil

/-!
Adapted into Veil from a TLA+ specification of Raft: Diego Ongaro's raft.tla, revised by Jin Li
(jinlmsft) for TLC.
Copyright 2014 Diego Ongaro. Licensed under the Creative Commons Attribution-4.0 International
License, https://creativecommons.org/licenses/by/4.0/ .
Source: https://github.com/jinlmsft/raft.tla/blob/76b4efab3bbd2a935d434cd364b294c443e90371/raft.tla
TLC model: `raft.toolbox/Unique_Leader/MC.tla` and `MC.cfg` at the same commit.
`Benchmarks/TLA/Raft/` has copies of the three files.
Modified locally: translated to Veil.

The checks at the end of this file are compared with the TLC models in `Benchmarks/TLA/Raft/`:
`MC.cfg`, and the smaller instances of `MCSmall.tla` and `MCDepth.tla`.

Encoding choices:
* `messages`, a function from messages to counts whose domain only grows, is a TMap from messages
  to counts. As in the source, a message stays in its domain when its count drops to 0.
* `voterLog[i]`, a function from the servers that voted for `i` to their logs, is a TMap from
  servers to logs.
* `votedFor[i] = Nil` is `votedFor i = none`.
* `Server` is also a set constant, for `Cardinality(Server)` and `{k \in Server : ...}`.
* A log is a `List`. Its entry `k` in the source is its element `k - 1`.
* The four kinds of message records are one structure with all their fields. A message leaves the
  fields that its kind lacks at the default values `0`, `false` and `[]`.

Kept as in the source:
* In `HandleAppendEntriesRequest`, the case "already done with request" sets `commitIndex[i]` but
  also leaves `logVars`, which contains `commitIndex`, unchanged. So it can only happen when the
  request's `mcommitIndex` already equals `commitIndex[i]`.
* In `AdvanceCommitIndex`, `committedLog` stays empty when the new commit index is 1.
* In `HandleAppendEntriesRequest`, a conflict removes only the last entry of the log.
-/

-- --------------------------------- MODULE raft ---------------------------------
-- \* This is the formal specification for the Raft consensus algorithm.
-- \*
-- \* Copyright 2014 Diego Ongaro.
-- \* This work is licensed under the Creative Commons Attribution-4.0
-- \* International License https://creativecommons.org/licenses/by/4.0/

-- EXTENDS Naturals, FiniteSets, Sequences, TLC

veil module Raft

-- \* Message types:
-- CONSTANTS RequestVoteRequest, RequestVoteResponse,
--           AppendEntriesRequest, AppendEntriesResponse
@[veil_decl]
inductive MsgType where
  | RequestVoteRequest
  | RequestVoteResponse
  | AppendEntriesRequest
  | AppendEntriesResponse

-- A log entry: [term |-> ..., value |-> ...] (see `ClientRequest`).
@[veil_decl]
structure logEntry where
  term : Nat
  value : Nat

-- A message. Each kind of message is a record with some of these fields:
-- * RequestVoteRequest: mtype, mterm, mlastLogTerm, mlastLogIndex, msource, mdest.
-- * RequestVoteResponse: mtype, mterm, mvoteGranted, mlog, msource, mdest.
-- * AppendEntriesRequest: mtype, mterm, mprevLogIndex, mprevLogTerm, mentries, mlog,
--   mcommitIndex, msource, mdest.
-- * AppendEntriesResponse: mtype, mterm, msuccess, mmatchIndex, msource, mdest.
@[veil_decl]
structure Message (server : Type) where
  mtype : MsgType
  mterm : Nat
  msource : server
  mdest : server
  mlastLogTerm : Nat := 0
  mlastLogIndex : Nat := 0
  mvoteGranted : Bool := false
  mlog : List logEntry := []
  mprevLogIndex : Nat := 0
  mprevLogTerm : Nat := 0
  mentries : List logEntry := []
  mcommitIndex : Nat := 0
  msuccess : Bool := false
  mmatchIndex : Nat := 0

-- An element of `elections` (see `BecomeLeader`).
@[veil_decl]
structure Election (server serverSet voterLogMap : Type) where
  eterm : Nat
  eleader : server
  elog : List logEntry
  evotes : serverSet
  evoterLog : voterLogMap

-- \* The term of the last entry in a log, or 0 if the log is empty.
-- LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term
def LastTerm (xlog : List logEntry) : Nat :=
  if h : xlog.length = 0 then 0 else xlog[xlog.length - 1].term

-- \* The set of server IDs
-- CONSTANTS Server
type server
type serverSet
instantiate sSet : TSet server serverSet
-- `Server` as a value, for `Cardinality(Server)` and `{k \in Server : ...}`.
immutable individual Server : serverSet

-- \* Server states.
-- CONSTANTS Follower, Candidate, Leader
enum serverStates = {Follower, Candidate, Leader}

-- \* A reserved value.
-- CONSTANTS Nil
-- (`votedFor i = none` stands for `votedFor[i] = Nil`.)

-- \* Maximum number of client requests
-- CONSTANTS MaxClientRequests
immutable individual MaxClientRequests : Nat

type MessageMap
type VoterLogMap
type ElectionSet
type LogSet
instantiate msgMap : TMap (Message server) Nat MessageMap
instantiate vlMap : TMap server (List logEntry) VoterLogMap
instantiate eSet : TSet (Election server serverSet VoterLogMap) ElectionSet
instantiate lSet : TSet (List logEntry) LogSet

-- ----
-- \* Global variables

-- \* A bag of records representing requests and responses sent from one server
-- \* to another. TLAPS doesn't support the Bags module, so this is a function
-- \* mapping Message to Nat.
-- VARIABLE messages
individual messages : MessageMap

-- \* A history variable used in the proof. This would not be present in an
-- \* implementation.
-- \* Keeps track of successful elections, including the initial logs of the
-- \* leader and voters' logs. Set of functions containing various things about
-- \* successful elections (see BecomeLeader).
-- VARIABLE elections
individual elections : ElectionSet

-- \* A history variable used in the proof. This would not be present in an
-- \* implementation.
-- \* Keeps track of every log ever in the system (set of logs).
-- VARIABLE allLogs
individual allLogs : LogSet

-- ----
-- \* The following variables are all per server (functions with domain Server).

-- \* The server's term number.
-- VARIABLE currentTerm
function currentTerm : server → Nat
-- \* The server's state (Follower, Candidate, or Leader).
-- VARIABLE state
function state : server → serverStates
-- \* The candidate the server voted for in its current term, or
-- \* Nil if it hasn't voted for any.
-- VARIABLE votedFor
function votedFor : server → Option server
-- serverVars == <<currentTerm, state, votedFor>>

-- \* The set of requests that can go into the log
-- VARIABLE clientRequests
individual clientRequests : Nat

-- \* A Sequence of log entries. The index into this sequence is the index of the
-- \* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
-- \* with index 1, so be careful not to use that!
-- VARIABLE log
function log : server → List logEntry
-- \* The index of the latest entry in the log the state machine may apply.
-- VARIABLE commitIndex
function commitIndex : server → Nat
-- \* The index that gets committed
-- VARIABLE committedLog
individual committedLog : List logEntry
-- \* Does the commited Index decrease
-- VARIABLE committedLogDecrease
individual committedLogDecrease : Bool
-- logVars == <<log, commitIndex, clientRequests, committedLog, committedLogDecrease >>

-- \* The following variables are used only on candidates:
-- \* The set of servers from which the candidate has received a RequestVote
-- \* response in its currentTerm.
-- VARIABLE votesSent
function votesSent : server → Bool
-- \* The set of servers from which the candidate has received a vote in its
-- \* currentTerm.
-- VARIABLE votesGranted
function votesGranted : server → serverSet
-- \* A history variable used in the proof. This would not be present in an
-- \* implementation.
-- \* Function from each server that voted for this candidate in its currentTerm
-- \* to that voter's log.
-- VARIABLE voterLog
function voterLog : server → VoterLogMap
-- candidateVars == <<votesSent, votesGranted, voterLog>>

-- \* The following variables are used only on leaders:
-- \* The next entry to send to each follower.
-- VARIABLE nextIndex
function nextIndex : server → server → Nat
-- \* The latest entry that each follower has acknowledged is the same as the
-- \* leader's. This is used to calculate commitIndex on the leader.
-- VARIABLE matchIndex
function matchIndex : server → server → Nat
-- leaderVars == <<nextIndex, matchIndex, elections>>

-- \* End of per server variables.

set_option veil.deferVCGeneration true

veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

-- `Server` contains every server.
assumption [server_complete] ∀ s : server, s ∈ Server

-- ----
-- \* Helpers

-- \* The set of all quorums. This just calculates simple majorities, but the only
-- \* important property is that every quorum overlaps with every other.
-- Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}
-- The spec only tests membership in `Quorum`: `InQuorum s` stands for `s \in Quorum`.
theory ghost relation InQuorum (s : serverSet) := sSet.count s * 2 > sSet.count Server

-- \* Helper for Send and Reply. Given a message m and bag of messages, return a
-- \* new bag of messages with one more m in it.
-- WithMessage(m, msgs) ==
--     IF m \in DOMAIN msgs THEN
--         [msgs EXCEPT ![m] = IF msgs[m] < 2 THEN msgs[m] + 1 ELSE 2 ]
--     ELSE
--         msgs @@ (m :> 1)
theory ghost function WithMessage (m : Message server) (msgs : MessageMap) : MessageMap :=
  match msgMap.lookup m msgs with
  | some n => msgMap.insert m (if n < 2 then n + 1 else 2) msgs
  | none => msgMap.insert m 1 msgs

-- \* Helper for Discard and Reply. Given a message m and bag of messages, return
-- \* a new bag of messages with one less m in it.
-- WithoutMessage(m, msgs) ==
--     IF m \in DOMAIN msgs THEN
--         [msgs EXCEPT ![m] = IF msgs[m] > 0 THEN msgs[m] - 1 ELSE 0 ]
--     ELSE
--         msgs
theory ghost function WithoutMessage (m : Message server) (msgs : MessageMap) : MessageMap :=
  match msgMap.lookup m msgs with
  | some n => msgMap.insert m (if n > 0 then n - 1 else 0) msgs
  | none => msgs

-- ValidMessage(msgs) ==
--     { m \in DOMAIN messages : msgs[m] > 0 }
-- SingleMessage(msgs) ==
--     { m \in DOMAIN messages : msgs[m] = 1 }
-- (`Receive`, `DuplicateMessage` and `DropMessage` choose from these sets.)

-- \* Add a message to the bag of messages.
-- Send(m) == messages' = WithMessage(m, messages)
procedure Send (m : Message server) {
  messages := WithMessage m messages
}

-- \* Remove a message from the bag of messages. Used when a server is done
-- \* processing a message.
-- Discard(m) == messages' = WithoutMessage(m, messages)
procedure Discard (m : Message server) {
  messages := WithoutMessage m messages
}

-- \* Combination of Send and Discard
-- Reply(response, request) ==
--     messages' = WithoutMessage(request, WithMessage(response, messages))
procedure Reply (response request : Message server) {
  messages := WithoutMessage request (WithMessage response messages)
}

-- \* Return the minimum value from a set, or undefined if the set is empty.
-- Min(s) == CHOOSE x \in s : \A y \in s : x <= y
-- \* Return the maximum value from a set, or undefined if the set is empty.
-- Max(s) == CHOOSE x \in s : \A y \in s : x >= y
-- (`min` and `max` for sets of two elements, `List.max?` for `agreeIndexes`.)

-- The conjunct `allLogs' = allLogs \cup {log[i] : i \in Server}` of `Next` (see below), which
-- every step takes. Every action calls this first, so it reads the logs before the step.
procedure UpdateAllLogs {
  let logs : LogSet := TSet.map Server (fun i => log i)
  allLogs := lSet.union allLogs logs
}

-- ----
-- \* Define initial values for all variables

-- InitHistoryVars == /\ elections = {}
--                    /\ allLogs   = {}
--                    /\ voterLog  = [i \in Server |-> [j \in {} |-> <<>>]]
procedure InitHistoryVars {
  elections := eSet.empty
  allLogs := lSet.empty
  voterLog I := vlMap.empty
}

-- InitServerVars == /\ currentTerm = [i \in Server |-> 1]
--                   /\ state       = [i \in Server |-> Follower]
--                   /\ votedFor    = [i \in Server |-> Nil]
procedure InitServerVars {
  currentTerm I := 1
  state I := Follower
  votedFor I := none
}

-- InitCandidateVars == /\ votesSent = [i \in Server |-> FALSE ]
--                      /\ votesGranted   = [i \in Server |-> {}]
procedure InitCandidateVars {
  votesSent I := false
  votesGranted I := sSet.empty
}

-- \* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
-- \* leader does not send itself messages. It's still easier to include these
-- \* in the functions.
-- InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
--                   /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
procedure InitLeaderVars {
  nextIndex I J := 1
  matchIndex I J := 0
}

-- InitLogVars == /\ log          = [i \in Server |-> << >>]
--                /\ commitIndex  = [i \in Server |-> 0]
--                /\ clientRequests = 1
--                /\ committedLog = << >>
--                /\ committedLogDecrease = FALSE
procedure InitLogVars {
  log I := []
  commitIndex I := 0
  clientRequests := 1
  committedLog := []
  committedLogDecrease := false
}

-- Init == /\ messages = [m \in {} |-> 0]
--         /\ InitHistoryVars
--         /\ InitServerVars
--         /\ InitCandidateVars
--         /\ InitLeaderVars
--         /\ InitLogVars
after_init {
  messages := msgMap.empty
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
--     /\ votesSent'      = [votesSent EXCEPT ![i] = FALSE ]
--     /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
--     /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
--     /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
--     /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
--     /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
--     /\ UNCHANGED <<messages, currentTerm, votedFor, log, elections, clientRequests, committedLog, committedLogDecrease>>
action Restart (i : server) {
  UpdateAllLogs
  state i := Follower
  votesSent i := false
  votesGranted i := sSet.empty
  voterLog i := vlMap.empty
  nextIndex i J := 1
  matchIndex i J := 0
  commitIndex i := 0
}

-- \* Server i times out and starts a new election.
-- Timeout(i) == /\ state[i] \in {Follower, Candidate}
--               /\ state' = [state EXCEPT ![i] = Candidate]
--               /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
--               \* Most implementations would probably just set the local vote
--               \* atomically, but messaging localhost for it is weaker.
--               /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
--               /\ votesSent' = [votesSent EXCEPT ![i] = FALSE ]
--               /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
--               /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
--               /\ UNCHANGED <<messages, leaderVars, logVars>>
action Timeout (i : server) {
  UpdateAllLogs
  require state i = Follower ∨ state i = Candidate
  state i := Candidate
  currentTerm i := currentTerm i + 1
  votedFor i := none
  votesSent i := false
  votesGranted i := sSet.empty
  voterLog i := vlMap.empty
}

-- \* Candidate i sends j a RequestVote request.
-- RequestVote(i,j) ==
--     /\ state[i] = Candidate
--     /\ Send([mtype         |-> RequestVoteRequest,
--              mterm         |-> currentTerm[i],
--              mlastLogTerm  |-> LastTerm(log[i]),
--              mlastLogIndex |-> Len(log[i]),
--              msource       |-> i,
--              mdest         |-> j])
--     /\ UNCHANGED <<serverVars, votesGranted, voterLog, leaderVars, logVars, votesSent>>
action RequestVote (i : server) (j : server) {
  UpdateAllLogs
  require state i = Candidate
  Send { mtype         := .RequestVoteRequest,
         mterm         := currentTerm i,
         mlastLogTerm  := LastTerm (log i),
         mlastLogIndex := (log i).length,
         msource       := i,
         mdest         := j }
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
action AppendEntries (i : server) (j : server) {
  UpdateAllLogs
  require i ≠ j
  require state i = Leader
  -- `log[i]`, kept in a local so that the proof `h` below is about it.
  let logI := log i
  let prevLogIndex := nextIndex i j - 1
  -- TLC reports an error if `log[i]` has no entry `prevLogIndex`.
  assert h : prevLogIndex ≤ logI.length
  let prevLogTerm := if h0 : prevLogIndex > 0 then logI[prevLogIndex - 1].term else 0
  let lastEntry := min logI.length (nextIndex i j)
  -- SubSeq(log[i], nextIndex[i][j], lastEntry)
  let entries := (logI.drop (nextIndex i j - 1)).take (lastEntry + 1 - nextIndex i j)
  Send { mtype         := .AppendEntriesRequest,
         mterm         := currentTerm i,
         mprevLogIndex := prevLogIndex,
         mprevLogTerm  := prevLogTerm,
         mentries      := entries,
         mlog          := logI,
         mcommitIndex  := min (commitIndex i) lastEntry,
         msource       := i,
         mdest         := j }
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
--     /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars>>
action BecomeLeader (i : server) {
  UpdateAllLogs
  require state i = Candidate
  require InQuorum (votesGranted i)
  state i := Leader
  nextIndex i J := (log i).length + 1
  matchIndex i J := 0
  let election : Election server serverSet VoterLogMap :=
    { eterm     := currentTerm i,
      eleader   := i,
      elog      := log i,
      evotes    := votesGranted i,
      evoterLog := voterLog i }
  elections := eSet.insert election elections
}

-- \* Leader i receives a client request to add v to the log.
-- ClientRequest(i) ==
--     /\ state[i] = Leader
--     /\ clientRequests < MaxClientRequests
--     /\ LET entry == [term  |-> currentTerm[i],
--                      value |-> clientRequests]
--            newLog == Append(log[i], entry)
--        IN  /\ log' = [log EXCEPT ![i] = newLog]
--            \* Make sure that each request is unique, reduce state space to be explored
--            /\ clientRequests' = clientRequests + 1
--     /\ UNCHANGED <<messages, serverVars, candidateVars,
--                    leaderVars, commitIndex, committedLog, committedLogDecrease>>
action ClientRequest (i : server) {
  UpdateAllLogs
  require state i = Leader
  require clientRequests < MaxClientRequests
  let entry : logEntry := { term := currentTerm i, value := clientRequests }
  let newLog := log i ++ [entry]
  log i := newLog
  clientRequests := clientRequests + 1
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
--            newCommittedLog ==
--               IF newCommitIndex > 1 THEN
--                   [ j \in 1..newCommitIndex |-> log[i][j] ]
--               ELSE
--                    << >>
--        IN /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
--           /\ committedLogDecrease' = \/ ( newCommitIndex < Len(committedLog) )
--                                      \/ \E j \in 1..Len(committedLog) : committedLog[j] /= newCommittedLog[j]
--           /\ committedLog' = newCommittedLog
--     /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, clientRequests>>
action AdvanceCommitIndex (i : server) {
  UpdateAllLogs
  require state i = Leader
  let Agree := fun (index : Nat) =>
    sSet.insert i (sSet.filter Server (fun k => matchIndex i k ≥ index))
  let agreeIndexes := (List.range' 1 (log i).length).filter (fun index => InQuorum (Agree index))
  let newCommitIndex :=
    match agreeIndexes.max? with
    | some maxIndex =>
      if (log i)[maxIndex - 1]?.map (·.term) = some (currentTerm i) then maxIndex
      else commitIndex i
    | none => commitIndex i
  -- TLC reports an error if `log[i]` has fewer than `newCommitIndex` entries here.
  assert newCommitIndex ≤ 1 ∨ newCommitIndex ≤ (log i).length
  let newCommittedLog := if newCommitIndex > 1 then (log i).take newCommitIndex else []
  -- Computed before `committedLog` changes, since it reads the old value.
  let decrease := decide (newCommitIndex < committedLog.length ∨
    ∃ j, j < committedLog.length ∧ committedLog[j]? ≠ newCommittedLog[j]?)
  commitIndex i := newCommitIndex
  committedLogDecrease := decrease
  committedLog := newCommittedLog
}

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
procedure HandleRequestVoteRequest (i j : server) (m : Message server) {
  let logOk := decide (m.mlastLogTerm > LastTerm (log i) ∨
    (m.mlastLogTerm = LastTerm (log i) ∧ m.mlastLogIndex ≥ (log i).length))
  let grant := decide (m.mterm = currentTerm i ∧ logOk ∧
    (votedFor i = none ∨ votedFor i = some j))
  assume m.mterm ≤ currentTerm i
  if grant then
    votedFor i := some j
  Reply { mtype        := .RequestVoteResponse,
          mterm        := currentTerm i,
          mvoteGranted := grant,
          mlog         := log i,
          msource      := i,
          mdest        := j } m
}

-- \* Server i receives a RequestVote response from server j with
-- \* m.mterm = currentTerm[i].
-- HandleRequestVoteResponse(i, j, m) ==
--     \* This tallies votes even when the current state is not Candidate, but
--     \* they won't be looked at, so it doesn't matter.
--     /\ m.mterm = currentTerm[i]
--     /\ \/ /\ m.mvoteGranted
--           /\ votesGranted' = [votesGranted EXCEPT ![i] =
--                                   votesGranted[i] \cup {j}]
--           /\ voterLog' = [voterLog EXCEPT ![i] =
--                               voterLog[i] @@ (j :> m.mlog)]
--           /\ UNCHANGED <<votesSent>>
--        \/ /\ ~m.mvoteGranted
--           /\ UNCHANGED <<votesSent, votesGranted, voterLog>>
--     /\ Discard(m)
--     /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars>>
procedure HandleRequestVoteResponse (i j : server) (m : Message server) {
  assume m.mterm = currentTerm i
  if m.mvoteGranted then
    votesGranted i := sSet.insert j (votesGranted i)
    -- `@@` keeps the value of `voterLog[i][j]` when `j` is already in its domain.
    if ¬ vlMap.contains j (voterLog i) then
      voterLog i := vlMap.insert j m.mlog (voterLog i)
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
--                        /\ UNCHANGED <<serverVars, logVars>>
--                    \/ \* conflict: remove 1 entry
--                        /\ m.mentries /= << >>
--                        /\ Len(log[i]) >= index
--                        /\ log[i][index].term /= m.mentries[1].term
--                        /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |->
--                                           log[i][index2]]
--                           IN log' = [log EXCEPT ![i] = new]
--                        /\ UNCHANGED <<serverVars, commitIndex, messages, clientRequests, committedLog, committedLogDecrease>>
--                    \/ \* no conflict: append entry
--                        /\ m.mentries /= << >>
--                        /\ Len(log[i]) = m.mprevLogIndex
--                        /\ log' = [log EXCEPT ![i] =
--                                       Append(log[i], m.mentries[1])]
--                        /\ UNCHANGED <<serverVars, commitIndex, messages, clientRequests, committedLog, committedLogDecrease>>
--        /\ UNCHANGED <<candidateVars, leaderVars>>
procedure HandleAppendEntriesRequest (i j : server) (m : Message server) {
  let logOk := decide (m.mprevLogIndex = 0 ∨
    (m.mprevLogIndex > 0 ∧ m.mprevLogIndex ≤ (log i).length ∧
      (log i)[m.mprevLogIndex - 1]?.map (·.term) = some m.mprevLogTerm))
  assume m.mterm ≤ currentTerm i
  -- The guards of the three disjuncts exclude each other, so they are tried in turn.
  if m.mterm < currentTerm i ∨ (m.mterm = currentTerm i ∧ state i = Follower ∧ ¬ logOk) then
    -- reject request
    Reply { mtype       := .AppendEntriesResponse,
            mterm       := currentTerm i,
            msuccess    := false,
            mmatchIndex := 0,
            msource     := i,
            mdest       := j } m
  else if m.mterm = currentTerm i ∧ state i = Candidate then
    -- return to follower state
    state i := Follower
  else if m.mterm = currentTerm i ∧ state i = Follower ∧ logOk then
    -- accept request
    let index := m.mprevLogIndex + 1
    -- `firstTerm` is `m.mentries[1].term`, read only when `m.mentries /= << >>`.
    let firstTerm := m.mentries.head?.map (·.term)
    if m.mentries = [] ∨ (m.mentries ≠ [] ∧ (log i).length ≥ index ∧
        (log i)[index - 1]?.map (·.term) = firstTerm) then
      -- already done with request
      -- `UNCHANGED <<serverVars, logVars>>` below includes `commitIndex`. Together with
      -- `commitIndex' = [commitIndex EXCEPT ![i] = m.mcommitIndex]`, it holds only when
      -- `m.mcommitIndex = commitIndex[i]`, so this step never changes `commitIndex`.
      assume m.mcommitIndex = commitIndex i
      commitIndex i := m.mcommitIndex
      Reply { mtype       := .AppendEntriesResponse,
              mterm       := currentTerm i,
              msuccess    := true,
              mmatchIndex := m.mprevLogIndex + m.mentries.length,
              msource     := i,
              mdest       := j } m
    else if m.mentries ≠ [] ∧ (log i).length ≥ index ∧
        (log i)[index - 1]?.map (·.term) ≠ firstTerm then
      -- conflict: remove 1 entry
      log i := (log i).take ((log i).length - 1)
    else if h : m.mentries ≠ [] ∧ (log i).length = m.mprevLogIndex then
      -- no conflict: append entry
      log i := log i ++ [m.mentries.head h.1]
    else
      -- None of the three applies, which `logOk` rules out: the step is disabled.
      assume False
  else
    -- None of the disjuncts applies (`i` is a leader of `m.mterm`): the step is disabled.
    assume False
}

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
procedure HandleAppendEntriesResponse (i j : server) (m : Message server) {
  assume m.mterm = currentTerm i
  if m.msuccess then
    nextIndex i j := m.mmatchIndex + 1
    matchIndex i j := m.mmatchIndex
  else
    nextIndex i j := max (nextIndex i j - 1) 1
  Discard m
}

-- \* Any RPC with a newer term causes the recipient to advance its term first.
-- UpdateTerm(i, j, m) ==
--     /\ m.mterm > currentTerm[i]
--     /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
--     /\ state'          = [state       EXCEPT ![i] = Follower]
--     /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
--        \* messages is unchanged so m can be processed further.
--     /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars>>
-- (The source does not use `j` either.)
set_option linter.unusedVariables false in
procedure UpdateTerm (i j : server) (m : Message server) {
  assume m.mterm > currentTerm i
  currentTerm i := m.mterm
  state i := Follower
  votedFor i := none
}

-- \* Responses with stale terms are ignored.
-- DropStaleResponse(i, j, m) ==
--     /\ m.mterm < currentTerm[i]
--     /\ Discard(m)
--     /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
-- (The source does not use `j` either.)
set_option linter.unusedVariables false in
procedure DropStaleResponse (i j : server) (m : Message server) {
  assume m.mterm < currentTerm i
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
action Receive {
  UpdateAllLogs
  -- `\E m \in ValidMessage(messages) : Receive(m)`, from `Next`.
  let m : { m // m ∈ msgMap.keys messages } :| (msgMap.lookup m.val messages).getD 0 > 0
  let m := m.val
  let i := m.mdest
  let j := m.msource
  -- The disjuncts exclude each other: `UpdateTerm` needs `m.mterm > currentTerm[i]`, the
  -- others `m.mterm <= currentTerm[i]` and their message type. So they are tried in turn.
  if m.mterm > currentTerm i then
    UpdateTerm i j m
  else if m.mtype = .RequestVoteRequest then
    HandleRequestVoteRequest i j m
  else if m.mtype = .RequestVoteResponse then
    if m.mterm < currentTerm i then
      DropStaleResponse i j m
    else
      HandleRequestVoteResponse i j m
  else if m.mtype = .AppendEntriesRequest then
    HandleAppendEntriesRequest i j m
  else
    -- `m.mtype = AppendEntriesResponse`
    if m.mterm < currentTerm i then
      DropStaleResponse i j m
    else
      HandleAppendEntriesResponse i j m
}

-- \* End of message handlers.
-- ----
-- \* Network state transitions

-- \* The network duplicates a message
-- DuplicateMessage(m) ==
--     /\ Send(m)
--     /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
action DuplicateMessage {
  UpdateAllLogs
  -- `\E m \in SingleMessage(messages) : DuplicateMessage(m)`, from `Next`.
  let m : { m // m ∈ msgMap.keys messages } :| (msgMap.lookup m.val messages).getD 0 = 1
  Send m.val
}

-- \* The network drops a message
-- DropMessage(m) ==
--     /\ Discard(m)
--     /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
action DropMessage {
  UpdateAllLogs
  -- `\E m \in ValidMessage(messages) : DropMessage(m)`, from `Next`.
  let m : { m // m ∈ msgMap.keys messages } :| (msgMap.lookup m.val messages).getD 0 > 0
  Discard m.val
}

-- ----
-- \* Defines how the variables may transition.
-- Next == /\ \/ \E i \in Server : Restart(i)
--            \/ \E i \in Server : Timeout(i)
--            \/ \E i, j \in Server : RequestVote(i, j)
--            \/ \E i \in Server : BecomeLeader(i)
--            \/ \E i \in Server : ClientRequest(i)
--            \/ \E i \in Server : AdvanceCommitIndex(i)
--            \/ \E i,j \in Server : AppendEntries(i, j)
--            \/ \E m \in ValidMessage(messages) : Receive(m)
--            \/ \E m \in SingleMessage(messages) : DuplicateMessage(m)
--            \/ \E m \in ValidMessage(messages) : DropMessage(m)
--            \* History variable that tracks every log ever:
--         /\ allLogs' = allLogs \cup {log[i] : i \in Server}
-- Each disjunct is the action of the same name above. The quantifiers over `Server` are its
-- parameters; the ones over messages are a choice at its start. Every action begins with
-- `UpdateAllLogs`, the last conjunct.

-- \* The specification must start with the initial state and transition according
-- \* to Next.
-- Spec == Init /\ [][Next]_vars

-- \* The following are a set of verification by jinlmsft@hotmail.com
-- BothLeader( i, j ) ==
--     /\ i /= j
--     /\ currentTerm[i] = currentTerm[j]
--     /\ state[i] = Leader
--     /\ state[j] = Leader
ghost relation BothLeader (i j : server) :=
  i ≠ j ∧ currentTerm i = currentTerm j ∧ state i = Leader ∧ state j = Leader

-- MoreThanOneLeader ==
--     \E i, j \in Server :  BothLeader( i, j )
ghost relation MoreThanOneLeader := ∃ i j, BothLeader i j

-- The invariants of MC.cfg. MC.tla defines them as
-- inv_1469115765494404000 == \lnot MoreThanOneLeader
-- inv_1469115765504405000 == \lnot committedLogDecrease
invariant [NotMoreThanOneLeader] ¬ MoreThanOneLeader
invariant [NotCommittedLogDecrease] ¬ committedLogDecrease

-- The constraint of the upstream MC.cfg. MC.tla defines it as
-- constr_1469115765473402000 == \A i \in Server: currentTerm[i] < 3
state_constraint [TermBound] ∀ i, currentTerm i < 3

-- MC.cfg has no `CHECK_DEADLOCK`, so TLC checks for deadlocks.
termination false

#gen_spec
#gen_executable

-- TLC checks this spec with `MC.cfg` on `MC.tla`. The second check below uses the cfg's instance.
-- Neither TLC nor this check finishes in a few minutes: TLC had found 26.6 million states, with
-- 16.6 million left to expand, after 5 minutes. A run of this check was stopped after about 5
-- minutes, because of its memory use.
-- The first check uses the smaller instance of `S1M3.cfg`, which TLC runs on `MCSmall.tla`:
-- 1 server and `MaxClientRequests = 3`. It finds no violation, in as many distinct states as TLC
-- (1,306).
-- All checks of this file are commented out, so that building it does not run them; uncomment one
-- to run it. Lean then runs it when it elaborates this file. In VS Code, the result appears in the
-- InfoView while the cursor is on `#model_check`. From the project root,
-- `lake env lean Examples/TLA/Raft.lean` prints it.
--
-- The instantiation (first `{ ... }` argument) sets the module's `type`s and `param`s:
-- * `server := Fin 3`: the servers are `0`, `1` and `2` (cfg: `Server <- const_1469115765452400000`,
--   which `MC.tla` defines as `{"s1","s2","s3"}`). The first check has one server, `0`
--   (`S1M3.cfg`: `Server <- S1`, where `S1 == {"s1"}`).
-- * `serverStates := serverStates_IndT`: the type that Veil generates for the `enum` above
--   (cfg: `Follower = Follower`, `Candidate = Candidate`, `Leader = Leader`).
-- * `serverSet := OrdList _`, `ElectionSet := OrdList _`, `LogSet := OrdList _`: `OrdList` has the
--   `TSet` instances that the `instantiate` lines above require.
-- * `MessageMap := Std.ExtTreeMap _ _`, `VoterLogMap := Std.ExtTreeMap _ _`: `Std.ExtTreeMap` has
--   the `TMap` instances that they require.
-- The theory (second `{ ... }` argument) sets the module's `immutable` fields:
-- * `Server := OrdList.ofList (List.finRange 3)`: the set of all servers. Before searching,
--   `#model_check` checks it against the `assumption [server_complete]` above.
-- * `MaxClientRequests := 2`: one client request (cfg: `MaxClientRequests <-
--   const_1469115765463401000`, which `MC.tla` defines as `2`). The first check has two
--   (`S1M3.cfg`: `MaxClientRequests = 3`).
--
-- The other settings of the cfg:
-- * `Nil = Nil`: a model value for "no vote". Here `votedFor` has type `server → Option server`,
--   where `none` stands for it.
-- * `RequestVoteRequest = RequestVoteRequest`, ...: model values for the message types. Here they
--   are the constructors of `MsgType`.
-- * `CONSTRAINT constr_1469115765473402000`, which `MC.tla` defines as
--   `\A i \in Server: currentTerm[i] < 3`: the `state_constraint [TermBound]` above. Unlike TLC,
--   Veil does not check the invariants in the states that the constraint drops.
-- * `SPECIFICATION spec_1469115765483403000`, which `MC.tla` defines as `Spec`: the spec of this
--   module.
-- * `INVARIANT inv_1469115765494404000 inv_1469115765504405000`, which `MC.tla` defines as
--   `\lnot MoreThanOneLeader` and `\lnot committedLogDecrease`: the invariants
--   `[NotMoreThanOneLeader]` and `[NotCommittedLogDecrease]` above.
-- * The cfg has no `CHECK_DEADLOCK`, so TLC checks for deadlocks. With `termination false` above,
--   Veil also reports every state without successors as a deadlock. The constraint never drops all
--   the successors of a state, since `Restart` does not change terms.
-- Options:
-- * `compiled` runs the search only in a compiled checker, not in Lean's interpreter.
-- * `interpreted` runs the search only in Lean's interpreter, without compiling a checker.
-- #model_check interpreted
--   { server := Fin 1, serverSet := OrdList _, serverStates := serverStates_IndT,
--     MessageMap := Std.ExtTreeMap _ _, VoterLogMap := Std.ExtTreeMap _ _,
--     ElectionSet := OrdList _, LogSet := OrdList _ }
--   { Server := OrdList.ofList (List.finRange 1), MaxClientRequests := 3 }

/- EVAL
#model_check compiled
  { server := Fin 3, serverSet := OrdList _, serverStates := serverStates_IndT,
    MessageMap := Std.ExtTreeMap _ _, VoterLogMap := Std.ExtTreeMap _ _,
    ElectionSet := OrdList _, LogSet := OrdList _ }
  { Server := OrdList.ofList (List.finRange 3), MaxClientRequests := 2 }
-/

-- The checks below, commented out, take longer; uncomment them to run them. None finds a violation.
-- * The first two use the instances of `S1M2.cfg` and `S2M1.cfg`, and explore as many distinct
--   states as TLC: 226 and 3,264,508.
-- * The next two use 2 servers and one client request, where neither TLC nor Veil finishes in a few
--   minutes, so they stop at a depth. They find 980,776 and 3,789,642 states, as many as TLC finds
--   with `S2M2-L19.cfg` and `S2M2-L22.cfg` on `MCDepth.tla`. Those keep the states at most 18 or
--   21 steps from the initial state.
-- * The last one uses the instance of `MC.cfg` and stops at a depth. It finds 3,672,854 states, as
--   many as TLC finds with `S3M2-L13.cfg` on `MCDepth.tla`, which keeps the states at most 12 steps
--   from the initial state.
-- Options:
-- * The checks name no mode, so their search starts in Lean's interpreter and moves to a compiled
--   checker once that is built.
-- * `(maxDepth := 17)`, `(maxDepth := 20)` and `(maxDepth := 11)` stop the search when it has
--   expanded every state at most that many steps from the initial state. So it finds the states
--   at most one step further.

-- #model_check
--   { server := Fin 1, serverSet := OrdList _, serverStates := serverStates_IndT,
--     MessageMap := Std.ExtTreeMap _ _, VoterLogMap := Std.ExtTreeMap _ _,
--     ElectionSet := OrdList _, LogSet := OrdList _ }
--   { Server := OrdList.ofList (List.finRange 1), MaxClientRequests := 2 }

-- #model_check
--   { server := Fin 2, serverSet := OrdList _, serverStates := serverStates_IndT,
--     MessageMap := Std.ExtTreeMap _ _, VoterLogMap := Std.ExtTreeMap _ _,
--     ElectionSet := OrdList _, LogSet := OrdList _ }
--   { Server := OrdList.ofList (List.finRange 2), MaxClientRequests := 1 }

-- #model_check
--   { server := Fin 2, serverSet := OrdList _, serverStates := serverStates_IndT,
--     MessageMap := Std.ExtTreeMap _ _, VoterLogMap := Std.ExtTreeMap _ _,
--     ElectionSet := OrdList _, LogSet := OrdList _ }
--   { Server := OrdList.ofList (List.finRange 2), MaxClientRequests := 2 } (maxDepth := 17)

-- #model_check
--   { server := Fin 2, serverSet := OrdList _, serverStates := serverStates_IndT,
--     MessageMap := Std.ExtTreeMap _ _, VoterLogMap := Std.ExtTreeMap _ _,
--     ElectionSet := OrdList _, LogSet := OrdList _ }
--   { Server := OrdList.ofList (List.finRange 2), MaxClientRequests := 2 } (maxDepth := 20)

-- #model_check
--   { server := Fin 3, serverSet := OrdList _, serverStates := serverStates_IndT,
--     MessageMap := Std.ExtTreeMap _ _, VoterLogMap := Std.ExtTreeMap _ _,
--     ElectionSet := OrdList _, LogSet := OrdList _ }
--   { Server := OrdList.ofList (List.finRange 3), MaxClientRequests := 2 } (maxDepth := 11)

end Raft

-- ===============================================================================

-- \* Changelog:
-- \*
-- \* 2014-12-02:
-- \* - Fix AppendEntries to only send one entry at a time, as originally
-- \*   intended. Since SubSeq is inclusive, the upper bound of the range should
-- \*   have been nextIndex, not nextIndex + 1. Thanks to Igor Kovalenko for
-- \*   reporting the issue.
-- \* - Change matchIndex' to matchIndex (without the apostrophe) in
-- \*   AdvanceCommitIndex. This apostrophe was not intentional and perhaps
-- \*   confusing, though it makes no practical difference (matchIndex' equals
-- \*   matchIndex). Thanks to Hugues Evrard for reporting the issue.
-- \*
-- \* 2014-07-06:
-- \* - Version from PhD dissertation
