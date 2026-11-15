\* Local benchmark harness for ParallelCommits; see LICENSE for the source model.
------------------------- MODULE BenchParallelCommits -------------------------
EXTENDS ParallelCommits

\* The numeric bounds of TypeInvariants checked by Veil's invariant [TypeInvariants].
\* The types of the Veil translation ensure the remaining conjuncts.
TypeOKBounds ==
    /\ record.epoch <= MAX_ATTEMPTS
    /\ record.ts <= MAX_ATTEMPTS
    /\ \A k \in KEYS:
        /\ intent_writes[k].epoch <= MAX_ATTEMPTS
        /\ intent_writes[k].ts <= MAX_ATTEMPTS
        /\ tscache[k] <= MAX_ATTEMPTS
=============================================================================
