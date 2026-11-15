\* Local finite benchmark harness for OrderedTicketSemaphore; see LICENSE for the source model.
\* Capacity is integer-valued, so <= 9 preserves the previous strict bound < 10.
---------------------- MODULE MCOrderedTicketSemaphore ----------------------
EXTENDS OrderedTicketSemaphore

BenchmarkBound == permits + taken <= 9

\* Next without the successors that violate BenchmarkBound. Unlike CONSTRAINT, which still
\* checks the invariants in those successors, it drops them, as Veil's state_constraint does.
ConstrainedNext == Next /\ BenchmarkBound'
=============================================================================
