\* Local benchmark harness for TaskClaiming; see LICENSE for the source model.
---------------------------- MODULE MCTaskClaiming ----------------------------
EXTENDS TaskClaiming

\* Next without the successors that violate LockVersionBound. Unlike CONSTRAINT, which still
\* checks the invariants in those successors, it drops them, as Veil's state_constraint does.
ConstrainedNext == Next /\ LockVersionBound'
=============================================================================
