module

public import Veil

/-!
Upstream license: MIT; see Benchmarks/TLA/LeaseGuard/LICENSE.
Copyright (c) 2024 Murat Demirbas
Source: https://github.com/muratdem/RaftLeaderLeases/blob/c773c123bdbbf9aeb18031feddd6b291317faf5e/TLA/mcLeaseGuard.tla
Modified locally: translated and adapted to Veil.

Finite safety translation of leaseGuard, retaining all eight source variables.
Source:
https://github.com/muratdem/RaftLeaderLeases/blob/c773c123bdbbf9aeb18031feddd6b291317faf5e/TLA/leaseGuard.tla
Terms, indexes and timestamps retain Int values, including the -1 no-entry
timestamp. Lists shift only their storage indexes from 1-based to 0-based.
Committed records form a canonical set. No SYMMETRY or ClockAbstractionView
is used; StateConstraint retains its source pruning semantics. There
is no fairness in the source Spec.
-/

veil module LeaseGuard

type server
type key
type ServerSet
type CommitSet

enum Role = {follower, leader}

@[veil_decl]
structure Entry (key : Type) where
  term : Int
  key : key
  index : Int
  timestamp : Int

@[veil_decl]
structure FollowerIndex where
  term : Int
  index : Int

@[veil_decl]
structure CommitRecord (key : Type) where
  committedInTerm : Int
  entry : Entry key

instantiate servers : TSet server ServerSet
instantiate commits : TSet (CommitRecord key) CommitSet
immutable individual AllServers : ServerSet
immutable individual Delta : Int
immutable individual MaxTerm : Int
immutable individual MaxLogLen : Nat
immutable individual MaxClock : Int

function currentTerm : server → Int
function state : server → Role
function log : server → List (Entry key)
function matchIndex : server → server → FollowerIndex
function commitIndex : server → Int
individual clock : Int
individual committed : CommitSet
function latestRead : key → Entry key

set_option veil.deferVCGeneration true

veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

assumption [ServerDomain] ∀ s : server, s ∈ AllServers

def NoEntry {key : Type} (k : key) : Entry key :=
  { term := 0, key := k, index := 0, timestamp := -1 }

def LastTerm {key : Type} (entries : List (Entry key)) : Int :=
  (entries.getLast?.map (·.term)).getD 0

def IsPrefix {key : Type} [DecidableEq key] (s t : List (Entry key)) : Bool :=
  s.length ≤ t.length && s == t.take s.length

-- MaxCommitted's maximal entry is unique on states satisfying the source
-- StateMachineSafety; several CommitRecords may contain that same entry.
def MaxCommittedEntry {key : Type} [DecidableEq key]
    (records : List (CommitRecord key)) (k : key) : Entry key :=
  records.foldl (fun latest record =>
    if record.entry.key = k ∧ record.entry.index > latest.index
    then record.entry else latest) (NoEntry k)

ghost function MaxCommitted (k : key) :=
  MaxCommittedEntry (commits.toList committed) k

ghost function LastCommitted (k : key) (i : server) :=
  ((log i).zipIdx).foldl (fun latest pair =>
    let index : Int := pair.2 + 1
    if index ≤ commitIndex i ∧ pair.1.key = k then index else latest) (0 : Int)

ghost function LastInPriorTerm (k : key) (i : server) :=
  ((log i).zipIdx).foldl (fun latest pair =>
    if pair.1.term < currentTerm i ∧ pair.1.key = k
    then (pair.2 + 1 : Int) else latest) (0 : Int)

-- Quorums(Server) == {i \in SUBSET Server : Cardinality(i) * 2 > Cardinality(Server)}
theory ghost relation IsQuorum (q : ServerSet) :=
  TSet.isSubset q AllServers ∧ servers.count q * 2 > servers.count AllServers

-- InLog(e, i) == log[i][e.index] = e; the index guard keeps toNat exact.
ghost relation InLog (e : Entry key) (i : server) :=
  e.index > 0 ∧ (log i)[e.index.toNat - 1]? = some e

ghost relation CanVoteForOplog (i j : server) (term : Int) :=
  currentTerm i < term ∧
  (LastTerm (log j) > LastTerm (log i) ∨
    (LastTerm (log j) = LastTerm (log i) ∧ (log j).length ≥ (log i).length))

after_init {
  currentTerm S := 0
  state S := follower
  log S := []
  matchIndex S T := { term := 0, index := 0 }
  commitIndex S := 0
  clock := 0
  committed := commits.empty
  latestRead K := NoEntry K
}

-- ClientWrite uses clock' in the new entry and old log length in matchIndex.
action ClientWrite (i : server) (k : key) {
  require state i = leader
  let newIndex : Int := (log i).length + 1
  clock := clock + 1
  log i := log i ++ [{ term := currentTerm i, key := k, index := newIndex, timestamp := clock }]
  matchIndex i i := { term := currentTerm i, index := newIndex }
}

action ClientRead (i : server) (k : key) {
  require state i = leader
  require (log i).length > 0 ∧ commitIndex i > 0
  -- Source indexing is partial. An invalid index must fail visibly rather than
  -- silently disable the action or supply a fictitious lease. These assertions
  -- never fire in the checked instances.
  let leaseEntry := (log i)[(commitIndex i).toNat - 1]?
  assert leaseEntry.isSome
  let entry := leaseEntry.getD (NoEntry k)
  require entry.timestamp + Delta ≥ clock
  require currentTerm i ≠ entry.term → LastCommitted k i = LastInPriorTerm k i
  let cInd := LastCommitted k i
  let read := if cInd = 0 then some (NoEntry k) else (log i)[cInd.toNat - 1]?
  assert read.isSome
  latestRead k := read.getD (NoEntry k)
}

action GetEntries (i j : server) {
  require state i = follower
  require (log j).length > (log i).length
  require currentTerm j ≥ currentTerm i
  require (log i).isEmpty ∨ (log j)[(log i).length - 1]? = (log i).getLast?
  let oldTerm := currentTerm i
  let oldLength := (log i).length
  -- The length guard guarantees the source's newEntryIndex exists.
  let newEntry := ((log j)[oldLength]?).getD default
  currentTerm i := currentTerm j
  log i := log i ++ [newEntry]
  -- This deliberately uses oldTerm, not currentTerm i after the assignment.
  matchIndex j i := { term := oldTerm, index := oldLength + 1 }
  if commitIndex i < commitIndex j then
    commitIndex i := min (commitIndex j) (oldLength + 1 : Int)
}

action RollbackEntries (i j : server) {
  require state i = follower
  require LastTerm (log i) < LastTerm (log j)
  require ¬ IsPrefix (log i) (log j)
  let newLength : Int := ((log i).length : Int) - 1
  matchIndex i i := { term := currentTerm i, index := newLength }
  log i := (log i).dropLast
  currentTerm i := max (currentTerm i) (currentTerm j)
}

-- Next quantifies \E Q \in Quorums(Server) : BecomeLeader(s, Q).
action BecomeLeader (i : server) (voteQuorum : ServerSet) {
  require IsQuorum voteQuorum
  let term := currentTerm i + 1
  require i ∈ voteQuorum
  require ∀ v : { s // s ∈ voteQuorum }, CanVoteForOplog v.val i term
  currentTerm S := if S ∈ voteQuorum then term else currentTerm S
  matchIndex i S := { term := 0, index := 0 }
  state S := if S = i then leader else if S ∈ voteQuorum then follower else state S
}

action CommitEntry (i : server) {
  require state i = leader
  require (log i).length > 0
  require ∀ entry ∈ log i, entry.term ≠ currentTerm i → entry.timestamp + Delta < clock
  require commitIndex i < ((log i).length : Int)
  let offset : { n // n ∈ List.range (log i).length } :|
    commitIndex i < (offset.val + 1 : Int)
  let newIndex : Int := offset.val + 1
  let topEntry := ((log i)[offset.val]?).getD default
  require topEntry.term = currentTerm i
  -- \E q \in Quorums(Server) : \A s \in q : ... is a condition, not a choice.
  require ∃ q : { q // TSet.isSubset q AllServers }, IsQuorum q.val ∧
    ∀ s : { v // v ∈ q.val },
      (matchIndex i s.val).index ≥ newIndex ∧ (matchIndex i s.val).term = currentTerm i
  -- Source range is Max({1, old commitIndex})..newIndex, including the old
  -- committed entry when commitIndex >= 1. Snapshot before updating it.
  let start := max 1 (commitIndex i)
  let newRecords := ((log i).zipIdx).filterMap (fun pair =>
    if start ≤ (pair.2 + 1 : Int) ∧ (pair.2 + 1 : Int) ≤ newIndex
    then some { committedInTerm := currentTerm i, entry := pair.1 } else none)
  let newCommitted := commits.union committed (commits.ofList newRecords)
  committed := newCommitted
  commitIndex i := newIndex
  -- MaxCommitted reads committed', exactly as in the source.
  latestRead K := MaxCommittedEntry (commits.toList newCommitted) K
}

action UpdateTerms (i j : server) {
  require currentTerm i > currentTerm j
  currentTerm j := currentTerm i
  state j := follower
}

-- No log-length/term guard is added to the original UpdateCommitIndex.
action UpdateCommitIndex (i j : server) {
  require state i = follower ∧ state j = leader
  require commitIndex i < commitIndex j
  commitIndex i := commitIndex j
}

action Tick {
  clock := clock + 1
}

-- TypeOK's Int, record, enum, function and set clauses are field types.
-- \A index \in DOMAIN log[s] : log[s][index].index = index; zipIdx is 0-based.
invariant [EntryIndexes] ∀ s : server,
  ∀ pair ∈ (log s).zipIdx, pair.1.index = (pair.2 + 1 : Int)

invariant [OneLeaderPerTerm] ∀ s t : server,
  state s = leader → state t = leader → currentTerm s = currentTerm t → s = t

invariant [LeaderCompleteness] ∀ s : server, state s = leader →
  ∀ r : { r // r ∈ committed }, r.val.committedInTerm < currentTerm s → InLog r.val.entry s

invariant [StateMachineSafety]
  ∀ c1 c2 : { c // c ∈ committed }, c1.val.entry.index = c2.val.entry.index →
    c1.val.entry = c2.val.entry

invariant [LinearizableReads] ∀ k : key, latestRead k = MaxCommitted k

state_constraint [StateConstraint]
  ∀ s : server, currentTerm s ≤ MaxTerm ∧ (log s).length ≤ MaxLogLen ∧ clock ≤ MaxClock

#gen_spec
#gen_executable

/- EVAL
#model_check compiled
  { server := Fin 3, key := Fin 1, ServerSet := OrdList (Fin 3),
    CommitSet := OrdList (CommitRecord (Fin 1)) }
  { AllServers := OrdList.ofList (List.finRange 3), Delta := 3,
    MaxTerm := 2, MaxLogLen := 2, MaxClock := 7 }
  (seenSet := HAMTMapShard)
-/

-- #model_check compiled
--   { server := Fin 3, key := Fin 2, ServerSet := OrdList (Fin 3),
--     CommitSet := OrdList (CommitRecord (Fin 2)) }
--   { AllServers := OrdList.ofList (List.finRange 3), Delta := 3,
--     MaxTerm := 1, MaxLogLen := 1, MaxClock := 3 }
--   (fingerprintType := UInt64) (sequential := true)

end LeaseGuard
