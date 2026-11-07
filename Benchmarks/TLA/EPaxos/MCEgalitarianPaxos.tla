\* Local TLC model for the Apache-2.0 EgalitarianPaxos.tla; see LICENSE.
\* The source repository has no TLC configuration. This module gives the constants and the
\* properties that the .cfg files next to it select.
------------------------- MODULE MCEgalitarianPaxos -------------------------
EXTENDS EgalitarianPaxos, TLC

CONSTANTS r1, r2, r3, r4, c1, c2

\* The sets of replicas and commands that the .cfg files choose from.
R2 == {r1, r2}
R3 == {r1, r2, r3}
R4 == {r1, r2, r3, r4}
C1 == {c1}
C2 == {c1, c2}

\* The quorums of the leader r: every set of replicas that contains r and has the size that the
\* source's ASSUME requires.
MCSlowQuorums(r) == {SQ \in SUBSET Replicas :
                       r \in SQ /\ Cardinality(SQ) = (Cardinality(Replicas) \div 2) + 1}
MCFastQuorums(r) == {FQ \in SUBSET Replicas :
                       r \in FQ /\ Cardinality(FQ) = (Cardinality(Replicas) \div 2) +
                                   ((Cardinality(Replicas) \div 2) + 1) \div 2}

\* The state predicate under the [] of the source's Consistency.
ConsistencyInv == \A i \in Instances : Cardinality(committed[i]) <= 1

\* committed[i] holds tuples <<cmd, deps, seq>>. The source's Nontriviality compares each tuple
\* with commands, so it fails at the first commit (see Nontriviality.cfg). This predicate compares
\* the command of each tuple instead.
NontrivialityCmdInv ==
    \A i \in Instances : \A C \in committed[i] : C[1] \in proposed \/ C[1] = none
=============================================================================
