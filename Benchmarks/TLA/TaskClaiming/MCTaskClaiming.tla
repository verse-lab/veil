\* Local benchmark harness for TaskClaiming; see LICENSE for the source model.
---------------------------- MODULE MCTaskClaiming ----------------------------
EXTENDS TaskClaiming

\* Next without the successors that violate LockVersionBound. Unlike CONSTRAINT, which still
\* checks the invariants in those successors, it drops them, as Veil's state_constraint does.
ConstrainedNext == Next /\ LockVersionBound'

\* The conjuncts of TypeOK that the types of the Veil translation do not ensure, as its
\* invariant [TypeOK] checks them.
TypeOKBounds ==
    /\ \A t \in Tasks : taskFailCount[t] <= MaxFailures
    /\ lockVersion >= 1
=============================================================================
