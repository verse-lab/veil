\* Local benchmark harness for Paxos; see LICENSE for the source model.
---------------------------- MODULE BenchPaxos ----------------------------
EXTENDS Paxos

\* The conjunct of TypeOK that the types of the Veil translation do not ensure, which its
\* invariant [TypeOK] checks.
TypeOKBounds == \A a \in Acceptors : maxBal[a] >= maxVBal[a]
=============================================================================
