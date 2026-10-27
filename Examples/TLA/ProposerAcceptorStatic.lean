module

public import Veil

/-!
Upstream license: Apache-2.0; see Benchmarks/TLA/ProposerAcceptorStatic/LICENSE.
Copyright 2022 - 2024 Neon Inc.
Attribution notice: Benchmarks/TLA/ProposerAcceptorStatic/NOTICE.
Source: https://github.com/neondatabase/neon/blob/fa504217c61bbcaf5c512d75830564541f917f8f/safekeeper/spec/MCProposerAcceptorStatic.tla
Modified locally: translated and adapted to Veil.

Translation of Neon's static proposer/acceptor safety model.
Source (Apache-2.0):
https://github.com/neondatabase/neon/blob/fa504217c61bbcaf5c512d75830564541f917f8f/safekeeper/spec/ProposerAcceptorStatic.tla
The six proposer record fields are flattened into functions. Partial votes use
Option Vote; NULL nextSendLsn uses Option Nat; elected_history stays a partial map.
LSNs retain their 1-based source values; WAL lists use index lsn-1.
CONSTANT acceptors is the type acceptor where the source uses it as a domain, and
the set constant acceptors where it uses it as a set (SUBSET, Cardinality).
MaxVoteAcc is deterministic: it scans acceptors in AcceptorSet's order, which for
OrdList (Fin 3) is TLC's model-value order (a1,a2,a3); among equal maximal votes
the first acceptor wins, including the later donor-term guard. Quorum selection
remains nondeterministic over every allowed subset.
The MC wrapper's bounds are state constraints; symmetry and display ALIAS are off.
-/

veil module ProposerAcceptorStatic

type proposer
type acceptor
type AcceptorSet
type CommittedSet
type ElectedMap
param maxTerm : Nat
param maxEntries : Nat

enum Phase = {campaign, leader}

@[veil_decl]
structure TermLsn where
  term : Nat
  lsn : Nat

@[veil_decl]
structure VoteRecord where
  termHistory : List TermLsn
  flushLsn : Nat

@[veil_decl]
structure AcceptorState where
  term : Nat
  termHistory : List TermLsn
  wal : List Nat

instantiate acSet : TSet acceptor AcceptorSet
instantiate commits : TSet TermLsn CommittedSet
instantiate elections : TMap Nat Nat ElectedMap

immutable individual acceptors : AcceptorSet

function propPhase : proposer → Phase
function propTerm : proposer → Nat
function propVotes : proposer → acceptor → Option VoteRecord
function propHistory : proposer → List TermLsn
function propWal : proposer → List Nat
function nextSendLsn : proposer → acceptor → Option Nat
function acc_state : acceptor → AcceptorState
individual committed : CommittedSet
individual elected_history : ElectedMap

set_option veil.deferVCGeneration true

veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

assumption [acceptors_complete] ∀ a : acceptor, a ∈ acceptors

def LastLogTerm (th : List TermLsn) : Nat :=
  (th.getLast?.getD default).term

-- Strict lexicographic comparison; keep the earlier candidate on ties.
def BetterVote (v old : VoteRecord) : Bool :=
  LastLogTerm v.termHistory > LastLogTerm old.termHistory ∨
    (LastLogTerm v.termHistory = LastLogTerm old.termHistory ∧ v.flushLsn > old.flushLsn)

def MaxVote {acceptor : Type} (votes : List (acceptor × VoteRecord)) :
    Option (acceptor × VoteRecord) :=
  votes.foldl (fun best candidate =>
    match best with
    | none => some candidate
    | some old => if BetterVote candidate.2 old.2 then some candidate else best) none

-- Same-position common history entries, selecting the last common index.
-- Every reachable leader/acceptor history includes the initial <0,1> entry.
def FindHighestCommonPoint (propTh accTh : List TermLsn) (flush : Nat) : TermLsn :=
  let common := (propTh.zip accTh).zipIdx.filter (fun entry => entry.1.1.term == entry.1.2.term)
  let i := (common.getLast?.map (·.2)).getD 0
  let accEnd := if i + 1 = accTh.length then flush else (accTh.getD (i + 1) default).lsn
  let propEnd := if i + 1 = propTh.length then flush else (propTh.getD (i + 1) default).lsn
  { term := (propTh.getD i default).term, lsn := min accEnd propEnd }

-- members is always acceptors in the static spec.
theory ghost relation FormsQuorum (s : AcceptorSet) :=
  acSet.count (acSet.intersection s acceptors) ≥ acSet.count acceptors / 2 + 1

theory ghost relation FormsMinQuorum (s : AcceptorSet) :=
  acSet.count (acSet.intersection s acceptors) = acSet.count acceptors / 2 + 1

ghost function FlushLsn (a : acceptor) := (acc_state a).wal.length + 1

ghost function AcceptorTermHistory (a : acceptor) :=
  (acc_state a).termHistory.filter (fun entry => entry.lsn ≤ FlushLsn a)

ghost function OrderedVotes (p : proposer) :=
  (acSet.toList acceptors).filterMap (fun a => (propVotes p a).map (fun vote => (a, vote)))

after_init {
  propPhase P := campaign
  propTerm P := 1
  propVotes P A := none
  propHistory P := []
  propWal P := []
  nextSendLsn P A := none
  acc_state A := { term := 0, termHistory := [{ term := 0, lsn := 1 }], wal := [] }
  committed := commits.empty
  elected_history := elections.empty
}

-- RestartProposer: choose any quorum, new term is its maximum accepted term + 1.
action RestartProposer (p : proposer) {
  let q : { q // TSet.isSubset q acceptors } :| FormsQuorum q.val
  let newTerm := (acSet.toList q.val).foldl (fun highest a => max highest (acc_state a).term) 0 + 1
  propPhase p := campaign
  propTerm p := newTerm
  propVotes p A := none
  propHistory p := []
  propWal p := []
  nextSendLsn p A := none
}

-- Vote's term update does not change the old WAL/history used in the vote.
action Vote (p : proposer) (a : acceptor) {
  require propPhase p = campaign
  require (acc_state a).term < propTerm p
  let vote := { termHistory := AcceptorTermHistory a, flushLsn := FlushLsn a : VoteRecord }
  acc_state a := { acc_state a with term := propTerm p }
  propVotes p a := some vote
}

action BecomeLeader (p : proposer) {
  require propPhase p = campaign
  require FormsQuorum (acSet.filter acceptors (fun a => (propVotes p a).isSome))
  let votes := OrderedVotes p
  -- votes is nonempty because a quorum is nonempty; defaults are unreachable here.
  let donor := (MaxVote votes).getD default
  require (acc_state donor.1).term = propTerm p
  let history := donor.2.termHistory ++ [{ term := propTerm p, lsn := donor.2.flushLsn }]
  propPhase p := leader
  propHistory p := history
  propWal p := (acc_state donor.1).wal
  let previous := (elections.lookup (propTerm p) elected_history).getD 0
  elected_history := elections.insert (propTerm p) (previous + 1) elected_history
}

action UpdateTerm (p : proposer) (a : acceptor) {
  require propPhase p = leader
  require (acc_state a).term < propTerm p
  acc_state a := { acc_state a with term := propTerm p }
}

action TruncateWal (p : proposer) (a : acceptor) {
  require propPhase p = leader
  require (acc_state a).term = propTerm p
  let hcp := FindHighestCommonPoint (propHistory p) (AcceptorTermHistory a) (FlushLsn a)
  let old := acc_state a
  acc_state a := { old with termHistory := propHistory p, wal := old.wal.take (hcp.lsn - 1) }
  nextSendLsn p a := some hcp.lsn
}

action NewEntry (p : proposer) {
  require propPhase p = leader
  propWal p := propWal p ++ [propTerm p]
}

action AppendEntry (p : proposer) (a : acceptor) {
  require propPhase p = leader
  require (acc_state a).term = propTerm p
  require (nextSendLsn p a).isSome
  let sendLsn := (nextSendLsn p a).getD 0
  require sendLsn ≤ (propWal p).length
  -- Reachable hcp/send LSNs are positive, so this is source WAL[sendLsn].
  let entry := (propWal p).getD (sendLsn - 1) 0
  nextSendLsn p a := some (sendLsn + 1)
  acc_state a := { acc_state a with wal := (acc_state a).wal ++ [entry] }
}

action CommitEntries (p : proposer) {
  require propPhase p = leader
  let chosen : { q // TSet.isSubset q acceptors } :| FormsMinQuorum chosen.val
  let q := chosen.val
  require ∀ a : acceptor, a ∈ q →
    (acc_state a).term = propTerm p ∧ (nextSendLsn p a).isSome
  let positions := (acSet.toList q).map (fun a => FlushLsn a)
  let commitLsn := positions.foldl min (positions.getD 0 0)
  require commitLsn ≥ ((propHistory p).getLast?.getD default).lsn
  -- The matching quorum's WAL prefix is within the current proposer's WAL.
  let entries := ((propWal p).take (commitLsn - 1)).zipIdx.map
    (fun entry => { term := entry.1, lsn := entry.2 + 1 : TermLsn })
  committed := commits.union committed (commits.ofList entries)
}

-- TypeOk's record domains, partial-map domains, enums and Nat fields are typed.
invariant [ElectionSafetyFull]
  ∀ t ∈ elections.keys elected_history, (elections.lookup t elected_history).getD 0 ≤ 1

invariant [LogIsMonotonic]
  ∀ a : acceptor, (acc_state a).wal.Pairwise (fun earlier later => earlier ≤ later)

invariant [LogSafety]
  ∀ c1 c2 : { c // c ∈ committed }, c1.val.lsn = c2.val.lsn → c1.val = c2.val

-- Keep the source's selected property, which its comments say is not valid
-- for every larger configuration (the selected model has only three acceptors).
invariant [CommittedNotTruncated]
  ∀ p : proposer, ∀ a : acceptor,
    propPhase p = leader ∧ propTerm p = (acc_state a).term →
      let hcp := FindHighestCommonPoint (propHistory p) (AcceptorTermHistory a) (FlushLsn a)
      ∀ entry ∈ (acc_state a).wal.zipIdx, hcp.lsn ≤ entry.2 + 1 →
        { term := entry.1, lsn := entry.2 + 1 : TermLsn } ∉ committed

-- MCProposerAcceptorStatic constrains proposers, not acceptors or counters.
state_constraint [StateConstraint]
  ∀ p : proposer, propTerm p ≤ maxTerm ∧ (propWal p).length ≤ maxEntries

#gen_spec
#gen_executable

-- The check below uses the instance of the TLC model
-- `Benchmarks/TLA/ProposerAcceptorStatic/ProposerAcceptorStatic.cfg`, which TLC runs on
-- `MCProposerAcceptorStatic.tla`. It is commented out; uncomment it to run it.
--
-- The instantiation (first `{ ... }` argument) sets the module's `type`s and `param`s:
-- * `proposer := Fin 2`: the proposers are `0`, `1` (cfg: `proposers = {p1, p2}`).
-- * `acceptor := Fin 3`: the acceptors are `0`, `1`, `2` (cfg: `acceptors = {a1, a2, a3}`).
-- * `AcceptorSet := OrdList _`, `CommittedSet := OrdList _`: `OrdList` has the `TSet` instances
--   that the `instantiate` lines above require.
-- * `ElectedMap := Std.ExtTreeMap _ _`: `Std.ExtTreeMap` has the `TMap` instance that the
--   `instantiate` line above requires.
-- * `maxTerm := 2`, `maxEntries := 3`: the state constraint bounds each proposer's term by 2 and
--   its log length by 3 (cfg: `max_term = 2`, `max_entries = 3`).
-- The theory (second `{ ... }` argument) sets the module's `immutable` fields:
-- * `acceptors := OrdList.ofList (List.finRange 3)`: the set of all acceptors, for where the
--   spec uses `acceptors` as a value. The `assumption [acceptors_complete]` above checks that it
--   contains every acceptor.
--
-- The other settings of the cfg:
-- * `NULL = NULL`: a model value for a missing value. Here `none` stands for it.
-- * `CONSTRAINT StateConstraint`: the `state_constraint [StateConstraint]` above. Unlike TLC,
--   Veil does not check the invariants in the states that the constraint drops.
-- * `INVARIANT TypeOk ElectionSafetyFull ... CommittedNotTruncated`: `#model_check` checks every
--   `invariant` of the module, which here has the same names except `TypeOk`. Lean's types
--   ensure `TypeOk`.
-- * `CHECK_DEADLOCK FALSE`: this module has no `termination` clause, so Veil reports no
--   deadlocks either.
-- Options:
-- * `compiled` runs the search only in a compiled checker, not in Lean's interpreter.
-- * `(seenSet := HAMTMapShard)`: the sharded map of visited states uses `HAMTMapShard`.
/- EVAL
#model_check compiled
  { proposer := Fin 2, acceptor := Fin 3, AcceptorSet := OrdList _,
    CommittedSet := OrdList _, ElectedMap := Std.ExtTreeMap _ _,
    maxTerm := 2, maxEntries := 3 }
  { acceptors := OrdList.ofList (List.finRange 3) }
  (seenSet := HAMTMapShard)
-/

-- -- Boundary: keep both proposers and three acceptors, restrict to term/log 1.
-- #model_check
--   { proposer := Fin 2, acceptor := Fin 3, AcceptorSet := OrdList (Fin 3),
--     CommittedSet := OrdList TermLsn, ElectedMap := Std.ExtTreeMap Nat Nat,
--     maxTerm := 1, maxEntries := 1 }
--   { acceptors := OrdList.ofList (List.finRange 3) }

end ProposerAcceptorStatic
