\* Local benchmark harness for MCProposerAcceptorStatic; see LICENSE and NOTICE for the source model.
------------------------ MODULE BenchProposerAcceptorStatic ------------------------
EXTENDS MCProposerAcceptorStatic

\* Next without the successors that violate StateConstraint. Unlike CONSTRAINT, which still
\* checks the invariants in those successors, it drops them, as Veil's state_constraint does.
ConstrainedNext == Next /\ StateConstraint'
=============================================================================
