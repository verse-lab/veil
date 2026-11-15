\* Local benchmark harness for mcLeaseGuard; see LICENSE for the source model.
---------------------------- MODULE BenchLeaseGuard ----------------------------
EXTENDS mcLeaseGuard

\* Next without the successors that violate StateConstraint. Unlike CONSTRAINT, which still
\* checks the invariants in those successors, it drops them, as Veil's state_constraint does.
ConstrainedNext == Next /\ StateConstraint'
=============================================================================
