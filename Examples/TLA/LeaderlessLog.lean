module

public import Veil

/-!
Upstream license: Apache-2.0; see Benchmarks/TLA/LeaderlessLog/LICENSE.
Copyright 2026 StreamNative, Inc.
Modified locally: translated and adapted to Veil.

Safety translation of Ursa's leaderless log, including sparse batches and both
sequential compaction rounds.
Source:
https://github.com/openlakestream/leaderless-log-protocol/blob/df7a398718dc3b6f726514ba4b99b0e5ae6aa521/tlaplus/LeaderlessLog.tla
OffsetTy's value i denotes TLA+ offset i+1. All numeric state keeps source values,
including writerOffset=0 as NONE. Range arithmetic in predicates uses Int.
CoveringEntryOffset's unique minimum is unused by ReadEntry's update; that action
only tests whether a covering entry exists, exactly as its source IF does.
Fairness and the three temporal properties are outside this safety check.
-/

veil module LeaderlessLog

type writer
param maxOffset : Nat
param maxBatch : Nat
abbrev OffsetTy (n : Nat) := Fin n

enum EntryType = {eWAL, eCompacted, eEmpty}
enum LogState = {lsOpen, lsFenced}
enum WriterState = {wIdle, wWritingWAL, wAssigningOffset, wDone, wFailed}
enum CompactorState = {cIdle, cWritingIndex, cDeletingOld, cUpdatingCursor, cDone}
enum ReaderResult = {rNone, rOK, rError}

@[veil_decl]
structure Entry (EntryType : Type) where
  kind : EntryType
  msgCount : Nat

immutable individual CompactRangeStart : Nat
immutable individual CompactRangeEnd : Nat
immutable individual CompactRange2Start : Nat
immutable individual CompactRange2End : Nat

function logIndex : OffsetTy maxOffset → Entry EntryType
individual sequenceCounter : Nat
individual logState : LogState
individual compactionCursor : Nat
function writerState : writer → WriterState
function writerOffset : writer → Nat
function writerBatchSize : writer → Nat
individual compactorState : CompactorState
function readerResult : writer → ReaderResult
individual compactRound : Nat

set_option veil.deferVCGeneration true

veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

assumption [range1_start] CompactRangeStart ≥ 1
assumption [range1_end] CompactRangeEnd ≥ CompactRangeStart
assumption [range1_limit] CompactRangeEnd < maxOffset
assumption [batch_positive] maxBatch ≥ 1
assumption [range2_start] CompactRange2Start ≥ CompactRangeEnd + 1
assumption [range2_end] CompactRange2End ≥ CompactRange2Start
assumption [range2_limit] CompactRange2End ≤ maxOffset

ghost function CurRangeStart := if compactRound = 1 then CompactRangeStart else CompactRange2Start
ghost function CurRangeEnd := if compactRound = 1 then CompactRangeEnd else CompactRange2End

-- o - msgCount + 1 is integer arithmetic in the source.
ghost relation HasCoveringEntry (off : Nat) :=
  ∃ o : OffsetTy maxOffset,
    o.val + 1 ≥ off ∧ (logIndex o).kind ≠ eEmpty ∧
      ((o.val + 1 : Nat) : Int) - ((logIndex o).msgCount : Int) + 1 ≤ (off : Int)

ghost relation HasCoveringWALEntry (off : Nat) :=
  ∃ o : OffsetTy maxOffset,
    o.val + 1 ≥ off ∧ (logIndex o).kind = eWAL ∧
      ((o.val + 1 : Nat) : Int) - ((logIndex o).msgCount : Int) + 1 ≤ (off : Int)

-- Exactly the three enabling conjuncts of source AssignOffset(w).
ghost relation CanAssignOffset (w : writer) :=
  writerState w = wAssigningOffset ∧ logState = lsOpen ∧
    sequenceCounter + writerBatchSize w - 1 ≤ maxOffset

after_init {
  logIndex O := { kind := eEmpty, msgCount := 0 }
  sequenceCounter := 1
  logState := lsOpen
  compactionCursor := 1
  writerState WW := wIdle
  writerOffset WW := 0
  writerBatchSize WW := 0
  compactorState := cIdle
  readerResult WW := rNone
  compactRound := 1
}

action StartAppend (w : writer) {
  require writerState w = wIdle
  require logState = lsOpen
  let count : { n // n ∈ List.range' 1 maxBatch } :| true
  writerBatchSize w := count.val
  writerState w := wWritingWAL
}

action WALWriteSuccess (w : writer) {
  require writerState w = wWritingWAL
  writerState w := wAssigningOffset
}

action WALWriteFail (w : writer) {
  require writerState w = wWritingWAL
  writerState w := wFailed
}

action AssignOffset (w : writer) {
  require CanAssignOffset w
  let count := writerBatchSize w
  let endOff := sequenceCounter + count - 1
  sequenceCounter := endOff + 1
  -- The source's [logIndex EXCEPT ![endOff] = ...], written pointwise.
  logIndex O := if O.val + 1 = endOff then { kind := eWAL, msgCount := count } else logIndex O
  writerOffset w := endOff
  writerState w := wDone
}

action AssignOffsetFenced (w : writer) {
  require writerState w = wAssigningOffset
  require logState = lsFenced
  writerState w := wFailed
}

action AssignOffsetExhausted (w : writer) {
  require writerState w = wAssigningOffset
  require logState = lsOpen
  require sequenceCounter + writerBatchSize w - 1 > maxOffset
  writerState w := wFailed
}

action AppendComplete (w : writer) {
  require writerState w = wDone ∨ writerState w = wFailed
  writerState w := wIdle
  writerOffset w := 0
  writerBatchSize w := 0
}

action CompactStart {
  require compactorState = cIdle
  require compactRound = 1 ∨ compactRound = 2
  require ∀ o : OffsetTy maxOffset,
    CurRangeStart ≤ o.val + 1 ∧ o.val + 1 ≤ CurRangeEnd → HasCoveringWALEntry (o.val + 1)
  require ∀ o : OffsetTy maxOffset,
    CurRangeStart ≤ o.val + 1 ∧ o.val + 1 ≤ CurRangeEnd ∧ (logIndex o).kind ≠ eEmpty →
      ((o.val + 1 : Nat) : Int) - ((logIndex o).msgCount : Int) + 1 ≥ (CurRangeStart : Int)
  compactorState := cWritingIndex
}

action CompactWriteCompactedIndex {
  require compactorState = cWritingIndex
  logIndex O := if O.val + 1 = CurRangeEnd then
    { kind := eCompacted, msgCount := CurRangeEnd - CurRangeStart + 1 } else logIndex O
  compactorState := cDeletingOld
}

action CompactDeleteOldEntries {
  require compactorState = cDeletingOld
  logIndex O := if CurRangeStart ≤ O.val + 1 ∧ O.val + 1 < CurRangeEnd then
    { kind := eEmpty, msgCount := 0 } else logIndex O
  compactorState := cUpdatingCursor
}

action CompactUpdateCursor {
  require compactorState = cUpdatingCursor
  compactionCursor := CurRangeEnd + 1
  compactorState := cDone
}

action CompactReset {
  require compactorState = cDone
  compactorState := cIdle
  compactRound := 2
}

action CompactorCrash {
  require compactorState = cWritingIndex ∨ compactorState = cDeletingOld ∨
    compactorState = cUpdatingCursor
  compactorState := cIdle
}

action FenceLog {
  require logState = lsOpen
  logState := lsFenced
}

action UnfenceLog {
  require logState = lsFenced
  logState := lsOpen
}

action ReadEntry (w : writer) (o : OffsetTy maxOffset) {
  require writerState w = wIdle
  require o.val + 1 < sequenceCounter
  readerResult w := if HasCoveringEntry (o.val + 1) then rOK else rError
}

-- The numeric bounds in TypeOK remain invariants, not enabling conditions.
invariant [TypeOK]
  (∀ o : OffsetTy maxOffset, (logIndex o).msgCount ≤ maxOffset) ∧
  (1 ≤ sequenceCounter ∧ sequenceCounter ≤ maxOffset + 1) ∧
  (1 ≤ compactionCursor ∧ compactionCursor ≤ maxOffset + 1) ∧
  (∀ w : writer, writerOffset w ≤ maxOffset ∧ writerBatchSize w ≤ maxBatch) ∧
  (compactRound = 1 ∨ compactRound = 2)

invariant [MonotonicOffsets] sequenceCounter ≥ 1

invariant [FencedRejectsAppends]
  logState = lsFenced → ∀ w : writer, ¬ CanAssignOffset w

invariant [CompactionPreservesData]
  compactorState = cDeletingOld ∨ compactorState = cUpdatingCursor ∨ compactorState = cDone →
    ∀ o : OffsetTy maxOffset, o.val + 1 = CurRangeEnd → (logIndex o).kind = eCompacted

invariant [NoPhantomEntries]
  compactorState = cUpdatingCursor ∨ compactorState = cDone →
    ∀ o : OffsetTy maxOffset, CurRangeStart ≤ o.val + 1 ∧ o.val + 1 < CurRangeEnd →
      (logIndex o).kind = eEmpty

invariant [CursorConsistency] compactionCursor ≤ sequenceCounter

invariant [NoOverlappingRanges]
  ∀ o1 o2 : OffsetTy maxOffset,
    o1 ≠ o2 ∧ (logIndex o1).kind = eWAL ∧ (logIndex o2).kind = eWAL →
      ((o1.val + 1 : Nat) : Int) <
        ((o2.val + 1 : Nat) : Int) - ((logIndex o2).msgCount : Int) + 1 ∨
      ((o2.val + 1 : Nat) : Int) <
        ((o1.val + 1 : Nat) : Int) - ((logIndex o1).msgCount : Int) + 1

invariant [NoReaderError] ∀ w : writer, readerResult w ≠ rError

invariant [SequentialCompactionSafety]
  compactRound = 2 → ∀ o : OffsetTy maxOffset,
    o.val + 1 = CompactRangeEnd → (logIndex o).kind = eCompacted

termination false

#gen_spec
#gen_executable

-- The check below uses the instance of the TLC model
-- `Benchmarks/TLA/LeaderlessLog/LeaderlessLog.cfg`. It is commented out; uncomment it to run it.
--
-- The instantiation (first `{ ... }` argument) sets the module's `type`s and `param`s:
-- * `writer := Fin 2`: the writers are `0`, `1` (cfg: `Writers = {w1, w2}`, where `w1 = w1` and
--   `w2 = w2` make them model values).
-- * `maxOffset := 13`: the offsets are `1..13` (cfg: `MaxOffset = 13`).
-- * `maxBatch := 2`: a write's batch size is at most 2 (cfg: `MaxBatch = 2`).
-- The theory (second `{ ... }` argument) sets the module's `immutable` fields:
-- * `CompactRangeStart := 1`, `CompactRangeEnd := 3`: the first compaction round compacts
--   offsets `1..3` (cfg: `CompactRangeStart = 1`, `CompactRangeEnd = 3`).
-- * `CompactRange2Start := 4`, `CompactRange2End := 5`: the second round compacts offsets
--   `4..5` (cfg: `CompactRange2Start = 4`, `CompactRange2End = 5`).
--
-- Before searching, `#model_check` checks these values against the `assumption`s above, which
-- are the spec's `ASSUME`s.
--
-- The other settings of the cfg:
-- * `INVARIANTS TypeOK MonotonicOffsets ... SequentialCompactionSafety`: `#model_check` checks
--   every `invariant` of the module, which here has the same nine names.
-- * The cfg has no `CHECK_DEADLOCK`, so TLC checks for deadlocks. With `termination false`
--   above, Veil also reports every state without successors as a deadlock.
-- Options:
-- * `compiled` runs the search only in a compiled checker, not in Lean's interpreter.
-- * `(seenSet := HAMTMapShard)`: the sharded map of visited states uses `HAMTMapShard`.
/- EVAL
#model_check compiled { writer := Fin 2, maxOffset := 13, maxBatch := 2 }
  { CompactRangeStart := 1, CompactRangeEnd := 3, CompactRange2Start := 4, CompactRange2End := 5 }
  (seenSet := HAMTMapShard)
-/

-- -- Boundary: dense single-record batches, with both compaction rounds retained.
-- #model_check { writer := Fin 2, maxOffset := 5, maxBatch := 1 }
--   { CompactRangeStart := 1, CompactRangeEnd := 3, CompactRange2Start := 4, CompactRange2End := 5 }

end LeaderlessLog
