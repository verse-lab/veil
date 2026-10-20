Supplemental simplifier-work profile (separate from the primary timings)
======================================================================

The profile uses the same model prefixes, defaults and early/local normalization
steps, but stops immediately after nextSimp and hoisting. It does not destruct
states or run the SMT backend, emit a query, or claim a SAT/UNSAT result.
The deliberate extraction-stop message is expected. A completed profile has
status profile_complete, with no translated query or solver verdict.

Each stage enables Lean's Meta.Tactic.simp.numSteps trace, sums the counters of
all completed SimpM.run calls (including the inner guarded hoister), records the
number of calls, then restores the previous trace state. A failed simp run may
not emit its counter; its phase is not reported as a complete step measurement.
Tracing changes costs, so these wall times are not mixed into the primary sweep.
The primary run instead records ordinary wall time and allocation heartbeats.

Compare both variants only at depths where the particular normalization phase
completed in both. This directly tests work reduction at common successful
inputs and distinguishes it from simply giving each transition a fresh cap.
