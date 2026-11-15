\* Local benchmark harness for LeaderlessLog; see LICENSE for the source model.
------------------------- MODULE BenchLeaderlessLog -------------------------
EXTENDS LeaderlessLog

\* The conjuncts of TypeOK that the types of the Veil translation do not ensure, as its
\* invariant [TypeOK] checks them.
TypeOKBounds ==
    /\ \A o \in 1..MaxOffset : logIndex[o].msgCount <= MaxOffset
    /\ sequenceCounter \in 1..(MaxOffset + 1)
    /\ compactionCursor \in 1..(MaxOffset + 1)
    /\ \A w \in Writers : writerOffset[w] <= MaxOffset /\ writerBatchSize[w] <= MaxBatch
    /\ compactRound \in {1, 2}
=============================================================================
