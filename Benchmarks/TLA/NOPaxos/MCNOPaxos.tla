\* Local benchmark harness for the MIT-licensed NOPaxos module; see LICENSE.
\* Preserves the existing three-replica instance and source-state message bound.
----------------------------- MODULE MCNOPaxos -----------------------------
EXTENDS NOPaxos

ReplicasConst == {"n1", "n2", "n3"}
ReplicaOrderConst == <<"n1", "n2", "n3">>

MsgCountLimit == Cardinality(messages) <= 18
ConstrainedNext == MsgCountLimit /\ Next
=============================================================================
