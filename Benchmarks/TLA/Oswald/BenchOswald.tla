\* Local benchmark harness for Oswald; see LICENSE for the source model.
---------------------------- MODULE BenchOswald ----------------------------
EXTENDS Oswald

\* The conjuncts of TypeOK that the types of the Veil translation do not ensure, as its
\* invariant [TypeOK] checks them.
TypeOKBounds ==
    /\ \A lsn \in DOMAIN chunk : lsn <= Cardinality(Values)
    /\ \A lsn \in DOMAIN snapshot : lsn <= Cardinality(Values)
    /\ \A w \in Writers : \A lsn \in wSnapshottedLsns[w] : lsn <= Cardinality(Values)
=============================================================================
