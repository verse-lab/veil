import Veil
-- --------------------------------- MODULE raft ---------------------------------
-- \* This is the formal specification for the Raft consensus algorithm.
-- \*
-- \* Copyright 2014 Diego Ongaro.
-- \* This work is licensed under the Creative Commons Attribution-4.0
-- \* International License https://creativecommons.org/licenses/by/4.0/
veil module raft_executable
-- EXTENDS Naturals, FiniteSets, Sequences, TLC

-- \* The set of server IDs
-- CONSTANTS Server
type server
type serverSet
instantiate sSet: TSet server serverSet
-- \* Server states.
-- CONSTANTS Follower, Candidate, Leader
enum serverStates = {Follower, Candidate, Leader}
-- \* A reserved value.
-- CONSTANTS Nil
immutable individual Nil : Nat
-- \* Message types:
-- CONSTANTS RequestVoteRequest, RequestVoteResponse,
--           AppendEntriesRequest, AppendEntriesResponse
@[veil_decl]
inductive MsgType
| RequestVoteRequest
| RequestVoteResponse
| AppendEntriesRequest
| AppendEntriesResponse
deriving instance Veil.Enumeration for MsgType

-- Log entry structure
-- In TLA+: log entries are records with [term |-> ..., value |-> ...]
type value

@[veil_decl]
structure logEntry (value : Type) where
  term : Nat
  value : Nat

type logSet
instantiate lSet: TSet (logEntry value) logSet

-- Unified Message structure containing all fields from all message types
-- Different message types use different subsets of these fields
@[veil_decl]
structure Message (value server : Type) where
  -- Common fields
  mtype         : MsgType
  mterm         : Nat
  msource       : server
  mdest         : server
  -- RequestVoteRequest fields
  mlastLogTerm  : Nat
  mlastLogIndex : Nat
  -- RequestVoteResponse fields
  mvoteGranted  : Bool
  mlog          : List (logEntry value)  -- history variable for proof
  -- AppendEntriesRequest fields
  mprevLogIndex : Nat
  mprevLogTerm  : Nat
  mentries      : List (logEntry value)
  mcommitIndex  : Nat
  -- AppendEntriesResponse fields
  msuccess      : Bool
  mmatchIndex   : Nat

type msetMsg
instantiate mSet: TMultiset (Message value server) msetMsg


-- Election structure (history variable for proof)
-- In TLA+: elections' = elections ∪ {[eterm |-> ..., eleader |-> ..., ...]}
-- Tracks successful elections with leader's log and voters' information
@[veil_decl]
structure Election (server value serverSet : Type) where
  eterm     : Nat                      -- term number of the election
  eleader   : server                   -- the elected leader
  elog      : List (logEntry value)    -- leader's log at election time
  evotes    : serverSet                -- set of servers that voted for the leader
  evoterLog : List (logEntry value)    -- voters' logs (simplified from server → log mapping)

type electionSet
instantiate eSet: TSet (Election server value serverSet) electionSet

-- \* Maximum number of client requests
-- CONSTANTS MaxClientRequests
immutable individual MaxClientRequests : Nat

-- ----
-- \* Global variables

-- \* A bag of records representing requests and responses sent from one server
-- \* to another. TLAPS doesn't support the Bags module, so this is a function
-- \* mapping Message to Nat.
-- VARIABLE messages
individual messages : msetMsg

-- \* A history variable used in the proof. This would not be present in an
-- \* implementation.
-- \* Keeps track of successful elections, including the initial logs of the
-- \* leader and voters' logs. Set of functions containing various things about
-- \* successful elections (see BecomeLeader).
-- VARIABLE elections
individual elections : electionSet

-- \* A history variable used in the proof. This would not be present in an
-- \* implementation.
-- \* Keeps track of every log ever in the system (set of logs).
-- VARIABLE allLogs
individual allLogs : logSet

-- ----
-- \* The following variables are all per server (functions with domain Server).

-- \* The server's term number.
-- VARIABLE currentTerm
function currentTerm : server → Nat
-- \* The server's state (Follower, Candidate, or Leader).
-- VARIABLE state
relation pcState : server → serverStates → Bool
-- \* The candidate the server voted for in its current term, or
-- \* Nil if it hasn't voted for any.
-- VARIABLE votedFor
relation votedFor : server → server → Bool
-- serverVars == <<currentTerm, state, votedFor>>

-- \* The set of requests that can go into the log
-- VARIABLE clientRequests
individual clientRequests : Nat
-- \* A Sequence of log entries. The index into this sequence is the index of the
-- \* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
-- \* with index 1, so be careful not to use that!
-- VARIABLE log
function logs : server → List (logEntry value)
-- \* The index of the latest entry in the log the state machine may apply.
-- VARIABLE commitIndex
function commitIndex : server → Nat
-- \* The index that gets committed
-- VARIABLE committedLog
individual committedLog : List (logEntry value)
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
function voterLog : server → server → List (logEntry value)
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
-- ----
immutable individual fixServer : server
immutable individual SIZE : Nat

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

procedure LastTerm (xlog : List (logEntry value)) {
  -- if xlog.length == 0 then default else (xlog.get! (xlog.length - 1)).term
  /-In TLA+, here return `0` not default. -/
  let res := if xlog.length = 0 then 0 else xlog.getLast!.term
  return res
}

-- \* Helper for Send and Reply. Given a message m and bag of messages, return a
-- \* new bag of messages with one more m in it.
-- WithMessage(m, msgs) ==
--     IF m \in DOMAIN msgs THEN
--         [msgs EXCEPT ![m] = IF msgs[m] < 2 THEN msgs[m] + 1 ELSE 2 ]
--     ELSE
--         msgs @@ (m :> 1)
procedure WithMessage (m : Message value server) {
  if mSet.contains m messages then
    let count := mSet.count m messages
    if count < 2 then
      messages := mSet.insert m messages
  else
    messages := mSet.insert m messages
}

-- \* Helper for Discard and Reply. Given a message m and bag of messages, return
-- \* a new bag of messages with one less m in it.
-- WithoutMessage(m, msgs) ==
--     IF m \in DOMAIN msgs THEN
--         [msgs EXCEPT ![m] = IF msgs[m] > 0 THEN msgs[m] - 1 ELSE 0 ]
--     ELSE
--         msgs
procedure WithoutMessage (m : Message value server) {
  messages := mSet.remove m messages
}

-- ValidMessage(msgs) ==
--     { m \in DOMAIN messages : msgs[m] > 0 }

-- SingleMessage(msgs) ==
--     { m \in DOMAIN messages : msgs[m] = 1 }

-- \* Add a message to the bag of messages.
-- Send(m) == messages' = WithMessage(m, messages)
procedure Send (m : Message value server) {
  if mSet.contains m messages then
    let count := mSet.count m messages
    if count < 2 then
      messages := mSet.insert m messages
  else
    messages := mSet.insert m messages
}

-- \* Remove a message from the bag of messages. Used when a server is done
-- \* processing a message.
-- Discard(m) == messages' = WithoutMessage(m, messages)
procedure Discard (m : Message value server) {
  messages := mSet.remove m messages
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
  allLogs    := lSet.empty
  elections  := eSet.empty
  voterLog I J := []
}

-- InitServerVars == /\ currentTerm = [i \in Server |-> 1]
--                   /\ state       = [i \in Server |-> Follower]
--                   /\ votedFor    = [i \in Server |-> Nil]
procedure InitServerVars {
  currentTerm I := 1
  pcState I S := decide $ S = Follower
  votedFor I J := false
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
  logs I := []
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
--     /\ votesSent'      = [votesSent EXCEPT ![i] = FALSE ]
--     /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
--     /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
--     /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
--     /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
--     /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
--     /\ UNCHANGED <<messages, currentTerm, votedFor, log, elections, clientRequests, committedLog, committedLogDecrease>>
action Restart (i : server) {
  pcState i T := T == Follower
  votesSent i := false
  votesGranted i := sSet.empty
  voterLog i J := []
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
  require pcState i Follower ∨ pcState i Candidate
  pcState i T := T == Candidate
  currentTerm i := currentTerm i + 1
  votedFor i J := false
  votesSent i := false
  votesGranted i := sSet.empty
  voterLog i J := []
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
  require pcState i Candidate
  let lastterm ← LastTerm (logs i)
  let msg : Message value server :=
    { mtype         := .RequestVoteRequest,
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
action AppendEntries (i : server) (j : server) {
  require (i ≠ j)
  require pcState i Leader

  let prevLogIndex := nextIndex i j - 1
  let prevLogTerm :=
    if prevLogIndex > 0 then
      match (logs i)[(prevLogIndex - 1)]? with
      | some entry => entry.term
      | none => 0
    else
      0

  -- Send up to 1 entry, constrained by the end of the log
  let logLen := (logs i).length
  let nextIdx := nextIndex i j
  let lastEntry := Nat.min logLen nextIdx

  -- Extract entries from nextIndex to lastEntry
  let entries :=
    if nextIdx ≤ lastEntry then
      List.take (lastEntry - nextIdx + 1) (List.drop (nextIdx - 1) (logs i))
    else
      []

  let msg : Message value server := {
    mtype         := .AppendEntriesRequest,
    mterm         := currentTerm i,
    mprevLogIndex := prevLogIndex,
    mprevLogTerm  := prevLogTerm,
    mentries      := entries,
    mlog          := logs i,  -- history variable for proof
    mcommitIndex  := min (commitIndex i) lastEntry,
    msource       := i,
    mdest         := j,
    -- Unused fields for AppendEntriesRequest
    mlastLogTerm  := 0,
    mlastLogIndex := 0,
    mvoteGranted  := false,
    msuccess      := false,
    mmatchIndex   := 0
  }

  Send msg
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
  require pcState i Candidate
  -- Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}
  -- require sSet.count (votesGranted i) * 2 > SIZE
  pcState i T := T == Leader
  nextIndex i R := List.length (logs i) + 1
  matchIndex i R := 0
  let newElection : Election server value serverSet :=
    { eterm     := currentTerm i,
      eleader   := i,
      elog      := logs i,
      evotes    := votesGranted i,
      evoterLog := voterLog i fixServer }
  elections := eSet.insert newElection elections
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
  require pcState i Leader
  require clientRequests < MaxClientRequests
  let entry : logEntry value :=
    { term  := currentTerm i,
      value := clientRequests }
  let newLog := logs i |>.append [entry]
  logs i := newLog
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

-- Helper procedure: Agree(index) returns set of servers that agree up through index
procedure Agree (i : server) (index : Nat) {
  let serverMax :| ∀s, matchIndex i s ≥ index → sSet.contains s serverMax
  let agreeSet := sSet.insert i serverMax
  return agreeSet
}

ghost relation isQuorum (sset : serverSet) (size : Nat) :=
  sSet.count sset * 2 > size

procedure agreeIndexes (i : server) {
  let logLength := List.length (logs i)
  let indices := (List.range (logLength + 1)).drop 1  -- [1, 2, ..., logLength]
  let agreeIndexs ← indices.filterM (fun idx => do
    let agreeSet ← Agree i idx
    pure <| isQuorum agreeSet SIZE
  )
  return agreeIndexs
}

action AdvanceCommitIndex (i : server) {
  require pcState i Leader
  let Indexs ← agreeIndexes i

  -- Compute newCommitIndex
  let newCommitIndex :=
    match Indexs.max? with
    | none => commitIndex i  -- agreeIndexes is empty
    | some maxIndex =>
        if h : maxIndex > 0 ∧ maxIndex ≤ (logs i).length then
          let entry := (logs i)[maxIndex - 1]
          if entry.term = currentTerm i then maxIndex else commitIndex i
        else
          commitIndex i

  -- Update committedLog
  let newCommittedLog := if newCommitIndex > 0 then
    (logs i).take newCommitIndex
  else
    []

  -- Check if committedLog decreases
  let decrease := (newCommitIndex < committedLog.length) ||
    (List.range (min newCommitIndex committedLog.length)).any (fun j =>
      if h : j < committedLog.length ∧ j < newCommittedLog.length then
        decide (committedLog[j] ≠ newCommittedLog[j])
      else
        false
    )
  commitIndex i := newCommitIndex
  committedLog := newCommittedLog
  committedLogDecrease := decrease
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

ghost relation logOk (m : Message value server) (i : server) (lastTerm_i : Nat) :=
  (m.mlastLogTerm > lastTerm_i) ∨
  ((m.mlastLogTerm = lastTerm_i) ∧ (m.mlastLogIndex ≥ List.length (logs i)))

ghost relation grant (m : Message value server) (i j : server) (lastTerm_i : Nat) :=
  (m.mterm = currentTerm i) ∧ logOk m i lastTerm_i
  ∧ (∀ P, votedFor i P → P = j)

procedure HandleRequestVoteRequest (i : server) (j : server) (m : Message value server) {
  let lastTerm_i ← LastTerm (logs i)
  -- require m.mterm ≤ currentTerm i
  assume m.mterm ≤ currentTerm i
  let isGrant := grant m i j lastTerm_i
  if decide isGrant then
    votedFor i R := R == j
  let response : Message value server :=
    { mtype         := .RequestVoteResponse,
      mterm         := currentTerm i,
      mlastLogTerm  := 0,
      mlastLogIndex := 0,
      mprevLogIndex := 0,
      mprevLogTerm  := 0,
      mentries      := [],
      mlog          := logs i,
      mcommitIndex  := 0,
      msource       := i,
      mdest         := j,
      mvoteGranted  := decide isGrant,
      msuccess      := false,
      mmatchIndex   := 0 }
  Reply response m
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

procedure HandleRequestVoteResponse (i : server) (j : server) (m : Message value server) {
  -- require m.mterm = currentTerm i
  assume m.mterm = currentTerm i
  if m.mvoteGranted then
    votesGranted i := sSet.insert j (votesGranted i)
    voterLog i j := m.mlog
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
procedure HandleAppendEntriesRequest (i : server) (j : server) (m : Message value server) {
  -- require m.mterm ≤ currentTerm i
  assume m.mterm ≤ currentTerm i

  -- Check if log is ok: prevLogIndex matches
  let logOk :=
    m.mprevLogIndex = 0 ||
    (m.mprevLogIndex > 0 &&
     m.mprevLogIndex ≤ (logs i).length &&
     match (logs i)[(m.mprevLogIndex - 1)]? with
     | some entry => entry.term = m.mprevLogTerm
     | none => false)

  -- Branch 1: Reject request
  if m.mterm < currentTerm i || (m.mterm = currentTerm i && pcState i Follower && !logOk) then
    let response : Message value server := {
      mtype         := .AppendEntriesResponse,
      mterm         := currentTerm i,
      msuccess      := false,
      mmatchIndex   := 0,
      msource       := i,
      mdest         := j,
      -- Unused fields
      mprevLogIndex := 0,
      mprevLogTerm  := 0,
      mentries      := [],
      mlog          := [],
      mcommitIndex  := 0,
      mlastLogTerm  := 0,
      mlastLogIndex := 0,
      mvoteGranted  := false
    }
    Reply response m
  -- Branch 2: Return to follower state (if candidate)
  else
    if m.mterm = currentTerm i && pcState i Candidate then
      pcState i T := T == Follower
    -- Branch 3: Accept request (follower with logOk)
    else
      if m.mterm = currentTerm i && pcState i Follower && logOk then
        let index := m.mprevLogIndex + 1
        let logLen := (logs i).length
        -- Sub-case 3a: Already done with request (empty entries or entry already matches)
        if m.mentries.isEmpty ||
            (logLen ≥ index &&
            match (logs i)[(index - 1)]? with
            | some entry => match m.mentries.head? with
                            | some firstEntry => entry.term = firstEntry.term
                            | none => false
            | none => false) then
          commitIndex i := m.mcommitIndex
          let response : Message value server := {
            mtype         := .AppendEntriesResponse,
            mterm         := currentTerm i,
            msuccess      := true,
            mmatchIndex   := m.mprevLogIndex + m.mentries.length,
            msource       := i,
            mdest         := j,
            -- Unused fields
            mprevLogIndex := 0,
            mprevLogTerm  := 0,
            mentries      := [],
            mlog          := [],
            mcommitIndex  := 0,
            mlastLogTerm  := 0,
            mlastLogIndex := 0,
            mvoteGranted  := false
          }
          Reply response m
    -- -- Sub-case 3b: Conflict - remove 1 entry
        else
          if !m.mentries.isEmpty && logLen ≥ index &&
                  match (logs i)[(index - 1)]? with
                  | some entry => match m.mentries.head? with
                                  | some firstEntry => entry.term ≠ firstEntry.term
                                  | none => false
                  | none => false then
            -- Remove last entry from log
            logs i := (logs i).take (logLen - 1)
          -- Sub-case 3c: No conflict - append entry
          else
            if !m.mentries.isEmpty && logLen = m.mprevLogIndex then
              let newEntry := match m.mentries.head? with
                              | some firstEntry => [firstEntry]
                              | none => []
              logs i := (logs i) ++ newEntry
              -- match m.mentries.head? with
              -- | some firstEntry =>
              --     logs i := (logs i) ++ [firstEntry]
              -- | none => pure ()
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
procedure HandleAppendEntriesResponse (i : server) (j : server) (m : Message value server) {
  -- require m.mterm = currentTerm i
  assume m.mterm = currentTerm i
  if m.msuccess then
    nextIndex i j := m.mmatchIndex + 1
    matchIndex i j := m.mmatchIndex
  else
    nextIndex i j := Nat.max (nextIndex i j - 1) 1
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
procedure UpdateTerm (i : server) (j : server) (m : Message value server) {
  -- require m.mterm > currentTerm i
  assume m.mterm > currentTerm i
  currentTerm i := m.mterm
  pcState i T := T == Follower
  votedFor i R := false
}

-- \* Responses with stale terms are ignored.
-- DropStaleResponse(i, j, m) ==
--     /\ m.mterm < currentTerm[i]
--     /\ Discard(m)
--     /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
procedure DropStaleResponse (i : server) (j : server) (m : Message value server) {
  -- require m.mterm < currentTerm i
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
action Receive_UpdateTerm {
  let m :| mSet.contains m messages
  let i := m.mdest
  let j := m.msource
  if m.mterm > currentTerm i then
    UpdateTerm i j m
}

action Receive_RequestVoteRequest {
  let m :| mSet.contains m messages
  let i := m.mdest
  let j := m.msource
  if m.mtype = .RequestVoteRequest then
    HandleRequestVoteRequest i j m
}

action Receive_RequestVoteResponse {
  let m :| mSet.contains m messages
  let i := m.mdest
  let j := m.msource
  if m.mtype = .RequestVoteResponse then
    if m.mterm < currentTerm i then
      DropStaleResponse i j m
    else
      HandleRequestVoteResponse i j m
}

action Receive_AppendEntriesRequest {
  let m :| mSet.contains m messages
  let i := m.mdest
  let j := m.msource
  if m.mtype = .AppendEntriesRequest then
    HandleAppendEntriesRequest i j m
}

action Receive_AppendEntriesResponse {
  let m :| mSet.contains m messages
  let i := m.mdest
  let j := m.msource
  if m.mtype = .AppendEntriesResponse then
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
-- ValidMessage(msgs) ==
--     { m \in DOMAIN messages : msgs[m] > 0 }
ghost relation isValidMessage (m : Message value server) :=
  mSet.contains m messages

ghost relation isSingleMessage (m : Message value server) :=
  mSet.count m messages = 1

-- SingleMessage(msgs) ==
--     { m \in DOMAIN messages : msgs[m] = 1 }
action DuplicateMessage {
  -- let m :| mSet.count m messages == 1
  let m :| mSet.contains m messages
  Send m
}

-- \* The network drops a message
-- DropMessage(m) ==
--     /\ Discard(m)
--     /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
action DropMessage {
  let m :| mSet.contains m messages
  if mSet.count m messages = 1 then
    Discard m
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

-- \* The specification must start with the initial state and transition according
-- \* to Next.
-- Spec == Init /\ [][Next]_vars

-- \* The following are a set of verification by jinlmsft@hotmail.com
-- BothLeader( i, j ) ==
--     /\ i /= j
--     /\ currentTerm[i] = currentTerm[j]
--     /\ state[i] = Leader
--     /\ state[j] = Leader

-- MoreThanOneLeader ==
--     \E i, j \in Server :  BothLeader( i, j )

-- Invariant: limit message count to keep state space manageable
invariant [message_count_limit] mSet.size messages < 3


set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 200000
set_option maxHeartbeats 10000000

#gen_spec
open Std
set_option veil.violationIsError false in
#model_check interpreted
  {
    server := Fin 3,
    value := Fin 2,
    serverStates := serverStates_IndT,
    serverSet := ExtTreeSet (Fin 3) compare,
    electionSet := ExtTreeSet (Election (Fin 3) (Fin 2) (ExtTreeSet (Fin 3) compare)) compare,
    msetMsg := TMapMultiset (Message (Fin 2) (Fin 3)),
    logSet := ExtTreeSet (logEntry (Fin 2)) compare
  }
  {
    SIZE := 3,
    MaxClientRequests := 2,
    Nil := 0,
    fixServer := 0
  }

end raft_executable








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
