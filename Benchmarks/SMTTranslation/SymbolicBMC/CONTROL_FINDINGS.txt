Supplemental controls: separate from the 588-cell primary sweep

All controls retain the primary selected assertion, trusted backend and native solver limits.
The recursion-only profile changes maxRecDepth from 512 to 10000, retaining maxHeartbeats200000,
Veil simp 100000 and the 60-second extraction watchdog. No control is merged into primary statistics.

aws-recursion
  AWS_AWSFixed depth 8 early: solver_timeout [solver: solver_timeout]
    Primary default: translation_failed [embedding: recursion]
    Completed query stages: 19327 ms; solver wrapper: 10029 ms (timeout).
  AWS_AWSFixed depth 8 old: solver_timeout [solver: solver_timeout]
    Primary default: translation_failed [embedding: recursion]
    Completed query stages: 27260 ms; solver wrapper: 10024 ms (timeout).

diehard-recursion
  Puzzles_DieHard depth 32 early: solver_timeout [solver: solver_timeout]
    Primary default: translation_failed [embedding: recursion]
    Completed query stages: 8803 ms; solver wrapper: 10023 ms (timeout).
  Puzzles_DieHard depth 32 old: solver_timeout [solver: solver_timeout]
    Primary default: translation_failed [embedding: recursion]
    Completed query stages: 14147 ms; solver wrapper: 10015 ms (timeout).

epaxos-recursion
  TLA_EPaxos depth 1 early: translation_timeout [embedding: wall_timeout]
    Primary default: translation_failed [embedding: recursion]
  TLA_EPaxos depth 1 old: translation_timeout [embedding: wall_timeout]
    Primary default: translation_failed [embedding: recursion]

flood-recursion
  Synchronous_FloodSet depth 16 early: translation_failed [embedding: heartbeats]
    Primary default: translation_failed [embedding: recursion]
  Synchronous_FloodSet depth 16 old: translation_failed [hoist: heartbeats]
    Primary default: translation_failed [hoist: heartbeats]

river-seven
  Puzzles_RiverCrossing depth 7 early: sat
    Completed query stages: 491 ms; solver wrapper: 22 ms (sat).
  Puzzles_RiverCrossing depth 7 old: sat
    Completed query stages: 2102 ms; solver wrapper: 23 ms (sat).

Interpretation:
RiverCrossing is SAT at exact depth 7 in both variants. The primary sampled even depths are
UNSAT. This is why largest sampled depth is not a bound covering every shorter execution.
AWSFixed at 8 and DieHard at 32 now emit queries in both variants, but all four solves time out.
FloodSet at 16 still fails: old in hoisting, early in embedding, both on heartbeat limits.
EPaxos at 1 now exhausts the 60-second pipeline wall cap in embedding in both variants;
it has not emitted a query. The watchdog kills the entire process group and restarts
the unattempted cell, retaining completed/failed cells. Limits expose different bottlenecks.
These selected controls support temporary recursion-limit mitigation for some models,
not a general recommendation or a claim of improved complete solving.

Raw sources, stage events, logs, exact option metadata and solver replay are in each
named controls/ subdirectory. The corrected runner rejects missing event markers.
The earlier control attempt with ineffective watchdog markers was discarded; see
DATASET_PROVENANCE.txt. These are the rerun observations with enforced caps.
