\* Local finite benchmark harness for MultiPaxosUs.tla, which is not included in this repository;
\* MultiPaxosUs.cfg gives its source and replaces its Ballots, Slots and NewProposals with these.
---------------------------- MODULE MCMultiPaxosUs ----------------------------
EXTENDS MultiPaxosUs

CONSTANTS MaxBallot, MaxSlot

MCBallots == 0..MaxBallot
MCSlots == 0..MaxSlot

\* NewProposals means to leave out the empty set of proposals, but `\ {}` leaves out nothing; this
\* subtracts {{}}. With finitely many slots, T can then leave nothing to choose from: this proposes
\* nothing then, where CHOOSE would fail.
MCNewProposals(T) ==
  IF FreeSlots(T) = {} THEN {}
  ELSE CHOOSE D \in SUBSET [slot : FreeSlots(T), val : Values] \ {{}} :
         \A d1, d2 \in D : d1.slot = d2.slot => d1 = d2
=============================================================================
