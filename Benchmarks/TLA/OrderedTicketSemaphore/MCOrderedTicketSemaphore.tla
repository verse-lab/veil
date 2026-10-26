\* Local finite benchmark harness for OrderedTicketSemaphore; see LICENSE for the source model.
\* Capacity is integer-valued, so <= 9 preserves the previous strict bound < 10.
---------------------- MODULE MCOrderedTicketSemaphore ----------------------
EXTENDS OrderedTicketSemaphore

BenchmarkBound == permits + taken <= 9
=============================================================================
