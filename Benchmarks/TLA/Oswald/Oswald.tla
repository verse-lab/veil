\* Upstream license: MIT; see LICENSE.
\* Copyright (c) 2026 Jack Vanlightly
\* Source: https://github.com/Vanlightly/s3-wal-collection/blob/0a08df719f7512a85c15cd36b4dfdcc193e9ac0e/oswald/Oswald.tla
\* Modified locally: added provenance notices.
----------------------------- MODULE Oswald -----------------------------
(*
OSWALD (Object Storage Write-Ahead Log Device)
Already has a P model at github.com/nvartolomei/oswald

This spec uses a sequence of appended values as the state-machine
state (and thus the snapshots) rather than a set of per-writer counters.
Using the term snapshot for this state, the safety properties largely enforce that the observed sequence of values
in each LSN is growing (snapshots of lower LSNs are prefixes of snapshots
at higher LSNs). 
Note that LSNs are 1-based in this spec.
*)

EXTENDS Naturals, Integers, FiniteSets, Sequences, SequencesExt, TLC

CONSTANTS Writers,
          GarbageCollectors,
          Values

CONSTANTS SNAPSHOT_RECOVERY, CATCHUP_RECOVERY, 
          VALIDATE, UPDATE_MANIFEST, READY, DELETE

CONSTANTS NIL

WritableLsns == 0..Cardinality(Values)

\* Storage variables
VARIABLES manifest,         \* Manifest on S3
          chunk,            \* Sequence of chunks on S3
          snapshot          \* Snapshots on S3
\* Writer variables
VARIABLES wState,           \* Writer state
          wManifestVersion, \* The version of the manifest the writer has seen
          wSafeLsn,         \* The LSN used to detect when it's position has fallen behind GC
          wNextLsn,         \* The next LSN to read/write
          wMachineData,     \* The writer's state machine data (a sequence of Values)
          wSnapshottedLsns, \* The LSNs at which the writer has written a snapshot
          wPendingApply     \* Chunks which have been read/written but not yet validated
\* Garbage collector variables
VARIABLES gcState,          \* Garbage collector state
          gcWm              \* Garbage collection watermark
\* Auxilliary variables for property checking
VARIABLES auxUsedValues,    \* The values which have been proposed
          auxObsSnapshots   \* The snapshots which have been observed

storeVars == <<manifest, chunk, snapshot>>
writerVars == <<wState, wManifestVersion, wSafeLsn, wNextLsn, 
                wMachineData, wSnapshottedLsns, wPendingApply>>
gcVars == <<gcState, gcWm>>
auxVars == <<auxUsedValues, auxObsSnapshots>>
vars == <<storeVars, writerVars, gcVars, auxVars>>

Symmetry ==
      Permutations(Writers)
          \union Permutations(GarbageCollectors)
          \union Permutations(Values)

\***********************************************************************
\* ACTIONS
\***********************************************************************

SnapshotRecovery(w) ==
    /\ wState[w] = SNAPSHOT_RECOVERY
    /\ wManifestVersion' = [wManifestVersion EXCEPT ![w] = manifest.version]
    /\ wSafeLsn' = [wSafeLsn EXCEPT ![w] = manifest.snapshotLsn]
    /\ wNextLsn' = [wNextLsn EXCEPT ![w] = manifest.snapshotLsn + 1]
    /\ wMachineData' = [wMachineData EXCEPT ![w] = 
                            IF manifest.snapshotLsn = 0 THEN <<>>
                            ELSE snapshot[manifest.snapshotLsn]]
    /\ wPendingApply' = [wPendingApply EXCEPT ![w] = <<>>] 
    /\ wState' = [wState EXCEPT ![w] = CATCHUP_RECOVERY]
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wSnapshottedLsns>>

CatchupRecovery(w) ==
    /\ wState[w] = CATCHUP_RECOVERY
    /\ LET read == IF wNextLsn[w] \in DOMAIN chunk
                   THEN chunk[wNextLsn[w]] ELSE NIL
       IN \/ /\ read /= NIL
             /\ wPendingApply' = [wPendingApply EXCEPT ![w] = Append(@, read)]
             /\ wNextLsn' = [wNextLsn EXCEPT ![w] = @ + 1]
             /\ UNCHANGED <<wState>>
          \/ /\ read = NIL
             /\ wState' = [wState EXCEPT ![w] = VALIDATE]
             /\ UNCHANGED <<wNextLsn, wPendingApply>>
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wMachineData, wSafeLsn, 
                  wSnapshottedLsns, wManifestVersion>>

ObserveSnapshot(w) ==
    LET lsn  == wNextLsn[w] - 1
        snap == wMachineData[w] \o wPendingApply[w]
    IN /\ auxObsSnapshots' = [auxObsSnapshots EXCEPT ![lsn] = @ \union {snap}]
       /\ UNCHANGED auxUsedValues

Validate(w) ==
    /\ wState[w] = VALIDATE
    /\ IF /\ wManifestVersion[w] /= manifest.version
          /\ wSafeLsn[w] <= manifest.gcWatermark
       THEN /\ wState' = [wState EXCEPT ![w] = SNAPSHOT_RECOVERY]
            /\ wPendingApply' = [wPendingApply EXCEPT ![w] = <<>>]
            /\ UNCHANGED <<wSafeLsn, wMachineData, auxVars>>
       ELSE /\ wState' = [wState EXCEPT ![w] = READY]
            /\ wSafeLsn' = [wSafeLsn EXCEPT ![w] = wNextLsn[w]]
            /\ wMachineData' = [wMachineData EXCEPT ![w] = @ \o wPendingApply[w]]
            /\ wPendingApply' = [wPendingApply EXCEPT ![w] = <<>>]
            /\ ObserveSnapshot(w)
    /\ UNCHANGED <<storeVars, gcVars, wNextLsn, wManifestVersion, wSnapshottedLsns>>

AppendChunk(w, v) ==
    /\ wState[w] = READY
    /\ wPendingApply[w] = <<>>
    /\ v \notin auxUsedValues
    /\ \/ /\ wNextLsn[w] \notin DOMAIN chunk
          /\ chunk' = chunk @@ (wNextLsn[w] :> v)
          /\ wNextLsn' = [wNextLsn EXCEPT ![w] = @ + 1]
          /\ wPendingApply' = [wPendingApply EXCEPT ![w] = <<v>>]
          /\ wState' = [wState EXCEPT ![w] = VALIDATE]
          /\ auxUsedValues' = auxUsedValues \union {v}
       \/ /\ wNextLsn[w] \in DOMAIN chunk
          /\ wState' = [wState EXCEPT ![w] = CATCHUP_RECOVERY]
          /\ UNCHANGED <<chunk, wNextLsn, wPendingApply, auxUsedValues>>
    /\ UNCHANGED <<manifest, snapshot, wMachineData, wManifestVersion, 
                   wSafeLsn, wSnapshottedLsns, gcVars, auxObsSnapshots>>

WriteSnapshot(w) ==
    /\ wState[w] = READY
    /\ wPendingApply[w] = <<>>
    /\ wNextLsn[w] > 1 \* at one, it means that the writer has read/written nothing
    /\ LET lsn == wNextLsn[w] - 1 IN
        /\ lsn \notin DOMAIN snapshot
        /\ lsn \notin wSnapshottedLsns[w] 
        /\ snapshot' = snapshot @@ (lsn :> wMachineData[w])
        /\ wState' = [wState EXCEPT ![w] = UPDATE_MANIFEST]
        /\ wSnapshottedLsns' = [wSnapshottedLsns EXCEPT ![w] = @ \union {lsn}]
    /\ UNCHANGED <<chunk, manifest, wManifestVersion, wSafeLsn, 
                   wNextLsn, wMachineData, wPendingApply, gcVars, auxVars>>

UpdateManifest(w) ==
    /\ wState[w] = UPDATE_MANIFEST
    /\ LET currManifest == manifest
           lsn          == wNextLsn[w] - 1
           newVersion   == currManifest.version + 1
       IN
            /\ IF currManifest.snapshotLsn < lsn
               THEN manifest' = [manifest EXCEPT !.snapshotLsn = lsn,
                                                 !.version = newVersion]
               ELSE UNCHANGED manifest
            /\ wState' = [wState EXCEPT ![w] = READY]                
    /\ UNCHANGED <<snapshot, chunk, wSafeLsn, wNextLsn, wManifestVersion,
                   wMachineData, wSnapshottedLsns, wPendingApply, gcVars, auxVars>>

AdvanceGcWatermark(gc) ==
    /\ \/ gcState[gc] = READY
       \* or we're deleting artifacts and there's nothing left to delete
       \/ /\ gcState[gc] = DELETE
          /\ ~\E lsn \in DOMAIN chunk : lsn <= gcWm[gc]
          /\ ~\E lsn \in DOMAIN snapshot : lsn <= gcWm[gc]
    /\ manifest.snapshotLsn /= manifest.gcWatermark
    /\ manifest' = [manifest EXCEPT !.gcWatermark = manifest.snapshotLsn,
                                    !.version = @ + 1]
    /\ gcState' = [gcState EXCEPT ![gc] = DELETE]
    /\ gcWm' = [gcWm EXCEPT ![gc] = manifest.snapshotLsn]
    /\ UNCHANGED <<chunk, snapshot, writerVars, auxVars>>

DeleteChunk(gc) ==
    /\ gcState[gc] = DELETE
    /\ \E lsn \in DOMAIN chunk :
        /\ lsn <= gcWm[gc]
        /\ chunk' = [l \in (DOMAIN chunk \ {lsn}) |-> chunk[l]]
        /\ UNCHANGED <<manifest, snapshot, writerVars, gcVars, auxVars>>

DeleteSnapshot(gc) ==
    /\ gcState[gc] = DELETE
    /\ \E lsn \in DOMAIN snapshot :
        /\ lsn < gcWm[gc]
        /\ snapshot' = [l \in (DOMAIN snapshot \ {lsn}) |-> snapshot[l]]
        /\ UNCHANGED <<chunk, manifest, writerVars, gcVars, auxVars>>

\***********************************************************************
\* INVARIANTS
\***********************************************************************

TypeOK ==
    /\ manifest \in [snapshotLsn: Nat, gcWatermark: Nat, version: Nat]
    /\ \A lsn \in DOMAIN chunk :
        /\ lsn \in WritableLsns
        /\ chunk[lsn] \in Values
    /\ \A lsn \in DOMAIN snapshot :
        /\ lsn \in WritableLsns
        /\ snapshot[lsn] \in Seq(Values)
    /\ wState \in [Writers -> {SNAPSHOT_RECOVERY, CATCHUP_RECOVERY, VALIDATE,
                               READY, UPDATE_MANIFEST}]
    /\ wManifestVersion \in [Writers -> Nat]
    /\ wSafeLsn \in [Writers -> Nat]
    /\ wNextLsn \in [Writers -> Nat]
    /\ wMachineData \in [Writers -> Seq(Values)]
    /\ wSnapshottedLsns \in [Writers -> SUBSET WritableLsns]
    /\ wPendingApply \in [Writers -> Seq(Values)]
    /\ gcState \in [GarbageCollectors -> {READY, DELETE}]
    /\ gcWm \in [GarbageCollectors -> Nat]
    /\ auxUsedValues \in SUBSET Values
    /\ \A lsn \in WritableLsns :
        \A element \in auxObsSnapshots[lsn] :
            element \in Seq(Values)

\***********************************************************************
\* INVARIANTS
\***********************************************************************

SeqPrefixOf(s1, s2) ==
    /\ Len(s1) <= Len(s2)
    /\ \A pos \in DOMAIN s1 :
            s1[pos] = s2[pos]

WriterLsn(w) == wNextLsn[w] - 1            

\* INV: ConsistentWriterSnapshots
\* Every ready writer holds a validated snapshot for its last applied LSN;
\* ready writers therefore agree on one prefix-consistent log history.
ConsistentWriterSnapshots ==
    \* A ready writer's snapshot ends at nextLsn - 1 and has been observed.
    /\ \A w \in Writers :
        wState[w] = READY =>
            /\ Len(wMachineData[w]) = WriterLsn(w)
            /\ wMachineData[w] \in auxObsSnapshots[WriterLsn(w)]

    \* Ready writers are mutually prefix-consistent.
    /\ \A w1, w2 \in Writers :
        (/\ wState[w1] = READY
         /\ wState[w2] = READY
         /\ WriterLsn(w1) <= WriterLsn(w2))
            => SeqPrefixOf(wMachineData[w1], wMachineData[w2])

\* INV: ConsistentObservedSnapshots
\* Validated snapshots form one immutable history: each LSN identifies a single
\* snapshot of that length, and every earlier snapshot prefixes every later one.
ConsistentObservedSnapshots ==
    \* There cannot be different observed snapshots at the same LSN
    /\ \A lsn \in WritableLsns :
        Cardinality(auxObsSnapshots[lsn]) <= 1
    \* An observed snapshot has the same number of elements as its LSN
    \* as each LSN appends a new value to the sequence
    /\ \A lsn \in WritableLsns :
        \A snap \in auxObsSnapshots[lsn] :
            Len(snap) = lsn
    \* Every earlier observation is a prefix of every later observation
    /\ \A earlier, later \in WritableLsns :
        earlier <= later =>
            \A earlierSnap \in auxObsSnapshots[earlier] :
                \A laterSnap \in auxObsSnapshots[later] :
                    SeqPrefixOf(earlierSnap, laterSnap)

\***********************************************************************
\* LIVENESS
\***********************************************************************

AllValuesAttempted ==
    <>[](auxUsedValues = Values)
    
WritersReachReady ==
    \A w \in Writers :
        []<>(wState[w] = READY)

GcCompletes ==
    <>[](snapshot.snapshotLsn = snapshot.gcWatermark)

\***********************************************************************
\* INIT and NEXT
\***********************************************************************

Init ==
    /\ manifest = [snapshotLsn |-> 0, gcWatermark |-> 0, version |-> 0]
    /\ chunk = <<>>
    /\ snapshot = <<>>
    /\ wState = [w \in Writers |-> SNAPSHOT_RECOVERY]
    /\ wManifestVersion = [w \in Writers |-> 0]
    /\ wSafeLsn= [w \in Writers |-> 0]
    /\ wNextLsn = [w \in Writers |-> 1]
    /\ wMachineData = [w \in Writers |-> <<>>]
    /\ wSnapshottedLsns = [w \in Writers |-> {}]
    /\ wPendingApply = [w \in Writers |-> <<>>]
    /\ gcState = [gc \in GarbageCollectors |-> READY]
    /\ gcWm = [gc \in GarbageCollectors |-> 0]
    /\ auxUsedValues = {}
    /\ auxObsSnapshots = [lsn \in WritableLsns |-> {}]

Next ==
    \/ \E w \in Writers :
        \/ SnapshotRecovery(w)
        \/ CatchupRecovery(w)
        \/ Validate(w)
        \/ \E v \in Values : AppendChunk(w, v)
        \/ WriteSnapshot(w)
        \/ UpdateManifest(w)
    \/ \E gc \in GarbageCollectors :
        \/ AdvanceGcWatermark(gc)
        \/ DeleteChunk(gc)
        \/ DeleteSnapshot(gc)

Fairness ==
    /\ \A w \in Writers :
        /\ WF_vars(SnapshotRecovery(w))
        /\ WF_vars(CatchupRecovery(w))
        /\ WF_vars(Validate(w))
        /\ \A v \in Values : WF_vars(AppendChunk(w, v))
        /\ WF_vars(WriteSnapshot(w))
        /\ WF_vars(UpdateManifest(w))
    /\ \A gc \in GarbageCollectors :
        /\ WF_vars(AdvanceGcWatermark(gc))
        /\ WF_vars(DeleteChunk(gc))
        /\ WF_vars(DeleteSnapshot(gc))

Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Fairness
=============================================================================|