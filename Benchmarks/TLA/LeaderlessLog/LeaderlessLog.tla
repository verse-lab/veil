\* Upstream license: Apache-2.0; see LICENSE.
\* Copyright 2026 StreamNative, Inc.
\* Source: https://github.com/openlakestream/leaderless-log-protocol/blob/df7a398718dc3b6f726514ba4b99b0e5ae6aa521/tlaplus/LeaderlessLog.tla
\* Modified locally: added provenance notices.
--------------------------- MODULE LeaderlessLog ---------------------------
(***************************************************************************)
(* Leaderless Log Protocol — TLA+ Implementation                           *)
(*                                                                         *)
(* Canonical spec: ../1-leaderless-log-protocol.md                        *)
(*                                                                         *)
(* Models the writer append → compaction index update → reader read       *)
(* lifecycle in a coordination-delegated leaderless architecture.          *)
(*                                                                         *)
(* Supports multi-record entries: each write covers 1..MaxBatch records.   *)
(* Index entries are stored at end-offsets with a msgCount field.           *)
(* Readers use ceiling lookup to find the covering entry for an offset.    *)
(*                                                                         *)
(* Supports sequential compaction: two non-overlapping compaction rounds   *)
(* verify that the protocol handles multiple compaction cycles correctly.  *)
(* Round 1 compacts [CompactRangeStart, CompactRangeEnd]; upon completion  *)
(* the compactor advances to round 2 and compacts                          *)
(* [CompactRange2Start, CompactRange2End].                                 *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Constants                                                               *)
(***************************************************************************)
CONSTANTS
    Writers,            \* Set of writer process IDs, e.g., {w1, w2}
    MaxOffset,          \* Upper bound on offsets for model checking
    CompactRangeStart,  \* First offset in compaction range (round 1)
    CompactRangeEnd,    \* Last offset in compaction range (round 1)
    CompactRange2Start, \* First offset in compaction range (round 2)
    CompactRange2End,   \* Last offset in compaction range (round 2)
    MaxBatch            \* Max records per write (1 = dense/legacy, >1 = sparse)

ASSUME CompactRangeStart >= 1
ASSUME CompactRangeEnd >= CompactRangeStart
ASSUME CompactRangeEnd < MaxOffset
ASSUME MaxBatch >= 1
\* Round 2 range must be non-overlapping and strictly after round 1
ASSUME CompactRange2Start >= CompactRangeEnd + 1
ASSUME CompactRange2End >= CompactRange2Start
ASSUME CompactRange2End <= MaxOffset

(***************************************************************************)
(* Type definitions                                                        *)
(***************************************************************************)
EntryTypes == {"WAL", "COMPACTED", "EMPTY"}
LogStates == {"OPEN", "FENCED"}
WriterStates == {"IDLE", "WRITING_WAL", "ASSIGNING_OFFSET", "DONE", "FAILED"}
CompactorStates == {"IDLE", "WRITING_COMPACTED_INDEX", "DELETING_OLD", "UPDATING_CURSOR", "DONE"}
ReaderResults == {"NONE", "OK", "ERROR"}

(***************************************************************************)
(* Variables                                                               *)
(***************************************************************************)
VARIABLES
    logIndex,               \* [1..MaxOffset -> [type |-> EntryTypes, msgCount |-> Nat]]
    sequenceCounter,        \* Nat — next offset to assign (monotonic via AtomicIncrement)
    logState,               \* LogStates
    compactionCursor,       \* Nat — first offset not yet compacted
    writerState,            \* [Writers -> WriterStates]
    writerOffset,           \* [Writers -> Nat \cup {0}]  (0 = NONE)
    writerBatchSize,        \* [Writers -> 0..MaxBatch] batch size for current write
    compactorState,         \* CompactorStates
    readerResult,           \* [Writers -> ReaderResults]
    compactRound            \* 1 or 2: which sequential compaction round

vars == <<logIndex, sequenceCounter, logState, compactionCursor,
          writerState, writerOffset, writerBatchSize,
          compactorState, readerResult, compactRound>>

(***************************************************************************)
(* Helper: EMPTY entry record                                             *)
(***************************************************************************)
EmptyEntry == [type |-> "EMPTY", msgCount |-> 0]

(***************************************************************************)
(* Helper: Current compaction range based on round                        *)
(* Round 1 uses [CompactRangeStart, CompactRangeEnd].                     *)
(* Round 2 uses [CompactRange2Start, CompactRange2End].                   *)
(***************************************************************************)
CurRangeStart == IF compactRound = 1 THEN CompactRangeStart ELSE CompactRange2Start
CurRangeEnd == IF compactRound = 1 THEN CompactRangeEnd ELSE CompactRange2End

(***************************************************************************)
(* Helper: Ceiling lookup — does a non-EMPTY entry cover offset off?      *)
(***************************************************************************)
HasCoveringEntry(off) ==
    \E o \in off..MaxOffset :
        /\ logIndex[o].type # "EMPTY"
        /\ o - logIndex[o].msgCount + 1 <= off

(***************************************************************************)
(* Helper: Find the covering entry's end-offset (ceiling lookup)          *)
(* Returns the smallest o >= off with a non-EMPTY entry that covers off.  *)
(***************************************************************************)
CoveringEntryOffset(off) ==
    CHOOSE o \in off..MaxOffset :
        /\ logIndex[o].type # "EMPTY"
        /\ o - logIndex[o].msgCount + 1 <= off
        /\ \A o2 \in off..(o-1) :
               \/ logIndex[o2].type = "EMPTY"
               \/ o2 - logIndex[o2].msgCount + 1 > off

(***************************************************************************)
(* Helper: Does a WAL entry cover offset off?                             *)
(***************************************************************************)
HasCoveringWALEntry(off) ==
    \E o \in off..MaxOffset :
        /\ logIndex[o].type = "WAL"
        /\ o - logIndex[o].msgCount + 1 <= off

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
    /\ logIndex = [o \in 1..MaxOffset |-> EmptyEntry]
    /\ sequenceCounter = 1
    /\ logState = "OPEN"
    /\ compactionCursor = 1
    /\ writerState = [w \in Writers |-> "IDLE"]
    /\ writerOffset = [w \in Writers |-> 0]
    /\ writerBatchSize = [w \in Writers |-> 0]
    /\ compactorState = "IDLE"
    /\ readerResult = [w \in Writers |-> "NONE"]
    /\ compactRound = 1

(***************************************************************************)
(* Action 1: StartAppend(w)                                               *)
(* Writer w begins append to log.                                          *)
(* Guard: writer is idle and log is OPEN.                                  *)
(* Non-deterministically chooses batch size count in 1..MaxBatch.          *)
(***************************************************************************)
StartAppend(w) ==
    /\ writerState[w] = "IDLE"
    /\ logState = "OPEN"
    /\ \E count \in 1..MaxBatch :
        /\ writerBatchSize' = [writerBatchSize EXCEPT ![w] = count]
        /\ writerState' = [writerState EXCEPT ![w] = "WRITING_WAL"]
        /\ UNCHANGED <<logIndex, sequenceCounter, logState, compactionCursor,
                       writerOffset, compactorState, readerResult, compactRound>>

(***************************************************************************)
(* Action 2: WALWrite(w) — success path                                   *)
(* WAL write succeeds, advance to offset assignment.                       *)
(***************************************************************************)
WALWriteSuccess(w) ==
    /\ writerState[w] = "WRITING_WAL"
    /\ writerState' = [writerState EXCEPT ![w] = "ASSIGNING_OFFSET"]
    /\ UNCHANGED <<logIndex, sequenceCounter, logState, compactionCursor,
                   writerOffset, writerBatchSize, compactorState,
                   readerResult, compactRound>>

(***************************************************************************)
(* Action 2: WALWrite(w) — failure path                                   *)
(* WAL write fails non-deterministically.                                  *)
(***************************************************************************)
WALWriteFail(w) ==
    /\ writerState[w] = "WRITING_WAL"
    /\ writerState' = [writerState EXCEPT ![w] = "FAILED"]
    /\ UNCHANGED <<logIndex, sequenceCounter, logState, compactionCursor,
                   writerOffset, writerBatchSize, compactorState,
                   readerResult, compactRound>>

(***************************************************************************)
(* Action 3: AssignOffset(w)                                              *)
(* Atomically: re-check log state, increment sequence counter by count,   *)
(* write WAL index entry at endOff with msgCount.                          *)
(* Models AtomicIncrement on the coordination store's sequence counter.   *)
(***************************************************************************)
AssignOffset(w) ==
    /\ writerState[w] = "ASSIGNING_OFFSET"
    /\ LET off == sequenceCounter
           count == writerBatchSize[w]
           endOff == off + count - 1
       IN
       /\ logState = "OPEN"
       /\ endOff <= MaxOffset
       /\ sequenceCounter' = endOff + 1
       /\ logIndex' = [logIndex EXCEPT ![endOff] =
              [type |-> "WAL", msgCount |-> count]]
       /\ writerOffset' = [writerOffset EXCEPT ![w] = endOff]
       /\ writerState' = [writerState EXCEPT ![w] = "DONE"]
    /\ UNCHANGED <<logState, compactionCursor,
                   writerBatchSize, compactorState, readerResult, compactRound>>

(***************************************************************************)
(* Action 3b: AssignOffset fails because log got fenced                   *)
(***************************************************************************)
AssignOffsetFenced(w) ==
    /\ writerState[w] = "ASSIGNING_OFFSET"
    /\ logState = "FENCED"
    /\ writerState' = [writerState EXCEPT ![w] = "FAILED"]
    /\ UNCHANGED <<logIndex, sequenceCounter, logState, compactionCursor,
                   writerOffset, writerBatchSize, compactorState,
                   readerResult, compactRound>>

(***************************************************************************)
(* Action 3c: AssignOffset fails because MaxOffset exhausted              *)
(* Models the finite offset space — in the real system offsets are         *)
(* unbounded, but the model uses a finite MaxOffset. Without this action, *)
(* a writer in ASSIGNING_OFFSET has no enabled transition when            *)
(* sequenceCounter + batchSize > MaxOffset, causing spurious deadlock.    *)
(***************************************************************************)
AssignOffsetExhausted(w) ==
    /\ writerState[w] = "ASSIGNING_OFFSET"
    /\ logState = "OPEN"
    /\ LET endOff == sequenceCounter + writerBatchSize[w] - 1
       IN endOff > MaxOffset
    /\ writerState' = [writerState EXCEPT ![w] = "FAILED"]
    /\ UNCHANGED <<logIndex, sequenceCounter, logState, compactionCursor,
                   writerOffset, writerBatchSize, compactorState,
                   readerResult, compactRound>>

(***************************************************************************)
(* Action 4: AppendComplete(w)                                            *)
(* Writer returns to IDLE after completing or failing an append.           *)
(***************************************************************************)
AppendComplete(w) ==
    /\ writerState[w] \in {"DONE", "FAILED"}
    /\ writerState' = [writerState EXCEPT ![w] = "IDLE"]
    /\ writerOffset' = [writerOffset EXCEPT ![w] = 0]
    /\ writerBatchSize' = [writerBatchSize EXCEPT ![w] = 0]
    /\ UNCHANGED <<logIndex, sequenceCounter, logState, compactionCursor,
                   compactorState, readerResult, compactRound>>

(***************************************************************************)
(* Action 5: CompactStart                                                 *)
(* Compactor begins processing the current round's compaction range.       *)
(* Guard: compactor idle, round is 1 or 2, all offsets in range covered   *)
(* by WAL entries, and all non-EMPTY entries fully contained in range.     *)
(***************************************************************************)
CompactStart ==
    /\ compactorState = "IDLE"
    /\ compactRound \in {1, 2}
    \* Every offset in the current range must be covered by a WAL entry
    /\ \A off \in CurRangeStart..CurRangeEnd :
           HasCoveringWALEntry(off)
    \* Every non-EMPTY entry in the range must start at or after CurRangeStart
    \* (no entry straddles the start boundary)
    /\ \A o \in CurRangeStart..CurRangeEnd :
           logIndex[o].type # "EMPTY" =>
               o - logIndex[o].msgCount + 1 >= CurRangeStart
    /\ compactorState' = "WRITING_COMPACTED_INDEX"
    /\ UNCHANGED <<logIndex, sequenceCounter, logState, compactionCursor,
                   writerState, writerOffset, writerBatchSize,
                   readerResult, compactRound>>

(***************************************************************************)
(* Action 6: CompactWriteCompactedIndex                                   *)
(* Overwrite end offset's index entry with COMPACTED type covering the    *)
(* entire compaction range for the current round.                          *)
(***************************************************************************)
CompactWriteCompactedIndex ==
    /\ compactorState = "WRITING_COMPACTED_INDEX"
    /\ logIndex' = [logIndex EXCEPT ![CurRangeEnd] =
           [type |-> "COMPACTED", msgCount |-> CurRangeEnd - CurRangeStart + 1]]
    /\ compactorState' = "DELETING_OLD"
    /\ UNCHANGED <<sequenceCounter, logState, compactionCursor,
                   writerState, writerOffset, writerBatchSize,
                   readerResult, compactRound>>

(***************************************************************************)
(* Action 7: CompactDeleteOldEntries                                      *)
(* Delete all non-EMPTY entries in [CurRangeStart, CurRangeEnd-1].        *)
(***************************************************************************)
CompactDeleteOldEntries ==
    /\ compactorState = "DELETING_OLD"
    /\ logIndex' = [o \in 1..MaxOffset |->
           IF o >= CurRangeStart /\ o <= CurRangeEnd - 1
           THEN EmptyEntry
           ELSE logIndex[o]]
    /\ compactorState' = "UPDATING_CURSOR"
    /\ UNCHANGED <<sequenceCounter, logState, compactionCursor,
                   writerState, writerOffset, writerBatchSize,
                   readerResult, compactRound>>

(***************************************************************************)
(* Action 8: CompactUpdateCursor                                          *)
(* Set compactionCursor = CurRangeEnd + 1.                                *)
(***************************************************************************)
CompactUpdateCursor ==
    /\ compactorState = "UPDATING_CURSOR"
    /\ compactionCursor' = CurRangeEnd + 1
    /\ compactorState' = "DONE"
    /\ UNCHANGED <<logIndex, sequenceCounter, logState,
                   writerState, writerOffset, writerBatchSize,
                   readerResult, compactRound>>

(***************************************************************************)
(* Action 9: CompactReset                                                 *)
(* Compactor returns to IDLE and advances to round 2.                     *)
(* If already in round 2, stays at round 2 (CompactStart will not fire    *)
(* again because the range is already COMPACTED, not WAL).                *)
(***************************************************************************)
CompactReset ==
    /\ compactorState = "DONE"
    /\ compactorState' = "IDLE"
    /\ compactRound' = 2   \* Advance to round 2 (idempotent if already 2)
    /\ UNCHANGED <<logIndex, sequenceCounter, logState, compactionCursor,
                   writerState, writerOffset, writerBatchSize,
                   readerResult>>

(***************************************************************************)
(* Action 9b: CompactorCrash                                              *)
(* Compactor crashes during any intermediate compaction step.              *)
(* Resets compactor to IDLE without undoing committed index changes.       *)
(* Does NOT advance compactRound — the crashed round can be retried       *)
(* (if its preconditions still hold) or left incomplete.                   *)
(***************************************************************************)
CompactorCrash ==
    /\ compactorState \in {"WRITING_COMPACTED_INDEX", "DELETING_OLD", "UPDATING_CURSOR"}
    /\ compactorState' = "IDLE"
    /\ UNCHANGED <<logIndex, sequenceCounter, logState, compactionCursor,
                   writerState, writerOffset, writerBatchSize,
                   readerResult, compactRound>>

(***************************************************************************)
(* Action 10: FenceLog                                                    *)
(***************************************************************************)
FenceLog ==
    /\ logState = "OPEN"
    /\ logState' = "FENCED"
    /\ UNCHANGED <<logIndex, sequenceCounter, compactionCursor,
                   writerState, writerOffset, writerBatchSize,
                   compactorState, readerResult, compactRound>>

(***************************************************************************)
(* Action 11: UnfenceLog                                                  *)
(***************************************************************************)
UnfenceLog ==
    /\ logState = "FENCED"
    /\ logState' = "OPEN"
    /\ UNCHANGED <<logIndex, sequenceCounter, compactionCursor,
                   writerState, writerOffset, writerBatchSize,
                   compactorState, readerResult, compactRound>>

(***************************************************************************)
(* Action 12: ReadEntry(w, off)                                           *)
(* Uses ceiling lookup to find covering entry for requested offset.        *)
(* Both WAL and COMPACTED entries are readable — compaction reorganizes    *)
(* data into PARQUET files but does not delete it. The ML layer            *)
(* dispatches on fileType (RAW → WAL reader, PARQUET → lakehouse reader). *)
(* If no covering entry exists (offset was deleted mid-compaction),        *)
(* result is ERROR.                                                        *)
(***************************************************************************)
ReadEntry(w, off) ==
    /\ writerState[w] = "IDLE"
    /\ off >= 1
    /\ off < sequenceCounter
    /\ IF HasCoveringEntry(off)
       THEN LET o == CoveringEntryOffset(off)
            IN readerResult' = [readerResult EXCEPT ![w] = "OK"]
       ELSE readerResult' = [readerResult EXCEPT ![w] = "ERROR"]
    /\ UNCHANGED <<logIndex, sequenceCounter, logState, compactionCursor,
                   writerState, writerOffset, writerBatchSize,
                   compactorState, compactRound>>

(***************************************************************************)
(* Next-state relation                                                     *)
(***************************************************************************)
Next ==
    \/ \E w \in Writers : StartAppend(w)
    \/ \E w \in Writers : WALWriteSuccess(w)
    \/ \E w \in Writers : WALWriteFail(w)
    \/ \E w \in Writers : AssignOffset(w)
    \/ \E w \in Writers : AssignOffsetFenced(w)
    \/ \E w \in Writers : AssignOffsetExhausted(w)
    \/ \E w \in Writers : AppendComplete(w)
    \/ CompactStart
    \/ CompactWriteCompactedIndex
    \/ CompactDeleteOldEntries
    \/ CompactUpdateCursor
    \/ CompactReset
    \/ CompactorCrash
    \/ FenceLog
    \/ UnfenceLog
    \/ \E w \in Writers, off \in 1..MaxOffset : ReadEntry(w, off)

(***************************************************************************)
(* Fairness                                                                *)
(***************************************************************************)
Fairness ==
    /\ \A w \in Writers : WF_vars(StartAppend(w))
    /\ \A w \in Writers : WF_vars(WALWriteSuccess(w))
    \* AssignOffset and its failure variants use strong fairness (SF):
    \* FenceLog/UnfenceLog have no fairness and can oscillate, toggling
    \* enablement of AssignOffset vs AssignOffsetFenced each step. WF
    \* requires continuous enablement and cannot guarantee progress under
    \* this oscillation. SF requires only infinitely-often enablement.
    \* This matches the real system where the coordination store call is
    \* atomic — the writer completes during any finite OPEN/FENCED window.
    /\ \A w \in Writers : SF_vars(AssignOffset(w))
    /\ \A w \in Writers : SF_vars(AssignOffsetFenced(w))
    /\ \A w \in Writers : SF_vars(AssignOffsetExhausted(w))
    /\ \A w \in Writers : WF_vars(AppendComplete(w))
    /\ WF_vars(CompactStart)
    /\ WF_vars(CompactWriteCompactedIndex)
    /\ WF_vars(CompactDeleteOldEntries)
    /\ WF_vars(CompactUpdateCursor)
    /\ WF_vars(CompactReset)
    \* No fairness for CompactorCrash — crashes are not guaranteed to happen,
    \* same as FenceLog/UnfenceLog. This lets TLC explore both crashing
    \* and non-crashing behaviors.
    /\ \A w \in Writers, off \in 1..MaxOffset : WF_vars(ReadEntry(w, off))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety Properties                                                       *)
(***************************************************************************)

\* S1: No two distinct WAL entries share the same offset.
\* Trivially true by construction: logIndex is a function from offsets to
\* entries, so each offset maps to exactly one entry. The check below is
\* a subset of TypeOK. Retained for spec-doc traceability.
NoOffsetDuplicates ==
    \A o \in 1..MaxOffset :
        logIndex[o].type \in EntryTypes

\* S2: sequenceCounter is always positive (lower bound check).
\* True monotonicity (sequenceCounter' >= sequenceCounter) is structurally
\* guaranteed by AssignOffset which only increments, but we verify the
\* invariant that it never drops below 1.
MonotonicOffsets ==
    sequenceCounter >= 1

\* S3: Fenced log rejects appends
\* If logState = FENCED, then AssignOffset(w) is not enabled for any writer.
\* Uses ENABLED to match the canonical spec (action enablement, not state).
\* A writer may be in ASSIGNING_OFFSET when fenced (it entered before the
\* fence), but AssignOffset cannot fire — it will take the AssignOffsetFenced
\* path instead.
FencedRejectsAppends ==
    logState = "FENCED" =>
        \A w \in Writers : ~ENABLED AssignOffset(w)

\* S4: After compaction writes COMPACTED index, the entry exists
\* Uses CurRangeEnd to track the active compaction round.
CompactionPreservesData ==
    compactorState \in {"DELETING_OLD", "UPDATING_CURSOR", "DONE"} =>
        logIndex[CurRangeEnd].type = "COMPACTED"

\* S5: After deleting old entries, no WAL entries in [CurRangeStart, CurRangeEnd-1]
NoPhantomEntries ==
    compactorState \in {"UPDATING_CURSOR", "DONE"} =>
        \A off \in CurRangeStart..(CurRangeEnd - 1) :
            logIndex[off].type = "EMPTY"

\* S6: Cursor never exceeds next assignable offset
CursorConsistency ==
    compactionCursor <= sequenceCounter

\* S7: No two WAL entries cover overlapping offset ranges.
\* Entry at o covers offsets [o - msgCount + 1, o]. Two WAL entries at o1, o2
\* don't overlap iff o1 < start(o2) or o2 < start(o1).
\* This is the core safety guarantee: AtomicIncrement ensures non-overlapping
\* offset assignment. WAL-COMPACTED overlap is intentionally allowed during
\* compaction's write-before-delete (the COMPACTED entry is written before
\* old WAL entries are deleted, ensuring no data loss). After CompactorCrash
\* the overlap may persist permanently, which is harmless for readers.
NoOverlappingRanges ==
    \A o1 \in 1..MaxOffset :
        \A o2 \in 1..MaxOffset :
            (o1 # o2 /\ logIndex[o1].type = "WAL" /\ logIndex[o2].type = "WAL") =>
                LET start1 == o1 - logIndex[o1].msgCount + 1
                    start2 == o2 - logIndex[o2].msgCount + 1
                IN \/ o1 < start2    \* o1's range ends before o2's range starts
                   \/ o2 < start1    \* o2's range ends before o1's range starts

\* S8: No reader ever gets ERROR — the 3-step ordering (write COMPACTED
\* before delete) guarantees that CeilingGet always finds a covering entry.
\* This is strictly stronger than L3's vacuously true leads-to.
NoReaderError ==
    \A w \in Writers : readerResult[w] # "ERROR"

\* S9: Sequential compaction safety — after round 1 completes (compactRound
\* advances to 2), round 1's COMPACTED entry is preserved. Round 2's
\* compaction operates on a disjoint, higher range and never overwrites
\* round 1's index entries. This verifies the compositionality argument:
\* compaction rounds are independent.
SequentialCompactionSafety ==
    compactRound = 2 => logIndex[CompactRangeEnd].type = "COMPACTED"

(***************************************************************************)
(* Liveness Properties                                                     *)
(***************************************************************************)

\* L1: Append progress — a writing writer eventually completes
AppendProgress ==
    \A w \in Writers :
        writerState[w] = "WRITING_WAL" ~>
            (writerState[w] = "DONE" \/ writerState[w] = "FAILED")

\* L2: Compaction eventually completes or crashes (crash → IDLE → retry).
\* With CompactorCrash modeled, the compactor may not reach DONE in a
\* single attempt. But it always makes progress: either it completes
\* (DONE) or crashes back to IDLE where CompactStart can retry.
CompactionCompletes ==
    compactorState = "WRITING_COMPACTED_INDEX" ~>
        (compactorState = "DONE" \/ compactorState = "IDLE")

\* L3: Reader eventually succeeds
\* A reader that encounters an ERROR (e.g., offset in mid-compaction gap)
\* will eventually get an OK result on a subsequent read. This verifies
\* that compaction completes and restores readability.
ReaderEventuallySucceeds ==
    \A w \in Writers :
        readerResult[w] = "ERROR" ~> readerResult[w] = "OK"

(***************************************************************************)
(* Type invariant (for debugging)                                          *)
(***************************************************************************)
TypeOK ==
    /\ \A o \in 1..MaxOffset :
           /\ logIndex[o].type \in EntryTypes
           /\ logIndex[o].msgCount \in 0..MaxOffset
    /\ sequenceCounter \in 1..(MaxOffset + 1)
    /\ logState \in LogStates
    /\ compactionCursor \in 1..(MaxOffset + 1)
    /\ \A w \in Writers : writerState[w] \in WriterStates
    /\ \A w \in Writers : writerOffset[w] \in 0..MaxOffset
    /\ \A w \in Writers : writerBatchSize[w] \in 0..MaxBatch
    /\ compactorState \in CompactorStates
    /\ \A w \in Writers : readerResult[w] \in ReaderResults
    /\ compactRound \in {1, 2}

=============================================================================
