Scope correction: exploratory seven-model dataset

This earlier experiment used different selected assertions and raised heartbeat
and recursion limits. Its backend helper omitted the production compatibility
wrapper. Its explicit Veil-preprocessing timings remain useful exploratory
evidence, but its backend translation/solver measurements do not establish
production pipeline behavior and must not be merged with the comprehensive
49-file default-limit sweep. Use the sibling SymbolicBMC report (worktree) or
veil-symbolic-bmc/report/index.html (download package) for that comparison.
The new sweep includes the compatibility wrapper, withoutRecover and native
cvc5 plugin, and retains a frozen inventory and per-cell provenance.

Veil #123: separate SMT outcome checks for seven examples

Final records
  final-solver/solver-results.csv is the preferred matched depth-4/8 dataset.
  It replays the exact queries emitted by the finalized preprocessing benchmark,
  with a 10-second cap. All 12 pairs with definite responses agree. Both
  MultiSigAll depth-4 queries time out; its old depth-8 query was never emitted,
  and its early depth-8 query times out. There are no conflicting SAT/UNSAT
  results or query-parser errors. This run supersedes preliminary solver times.

  deepest-solver/deepest-results.csv is a SEPARATE feasibility check, with a
  2-second cap, of each model's deepest emitted early query. It must not be mixed
  into the matched 10-second graph. TwoPhaseCommit depth32, RicartAgrawala depth32
  and FloodSet depth16 return SAT. Ring, DieHard, MultiSigAll and Peterson depth32
  return UNKNOWN:TIMEOUT. All seven encodings were accepted by cvc5; this does
  not claim that the four timed-out queries were solved. FloodSet depth32 did
  not finish hoisting, so its deepest emitted query was depth16.

  final-query-comparison.csv/json connects final benchmark queries to the
  earlier archived solver inputs: all 27 available queries match after command
  ordering and implication currying. Final old/early pairs also match after
  that normalization for all 13 comparable pairs. The missing fourteenth pair
  is MultiSigAll depth8, whose old preprocessing failed before query emission.

Reproduction
  First build Veil and its native cvc5 dependency in the desired checkout.
  From this directory, run:
    python3 run_solver_checks.py --repo /path/to/veil \
      --output /tmp/veil-solver-reproduction --depths 4 8 --solver-timeout 10

  Use a new output directory to preserve the archived investigation results.
  The scripts accept explicit paths and do not modify production files or build
  libraries. The Linux native plugin must exist at
  .lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so under the checkout.
  --models accepts any subset of the seven model names. --generate-only emits
  Lean sources; --replay-only solves queries already present in the output.
  Summaries can be regenerated with:
    python3 summarize.py --output /tmp/veil-solver-reproduction --depths 4 8

  To replay an existing finalized benchmark without elaborating models:
    python3 replay_final_queries.py --repo /path/to/veil \
      --queries /path/to/results/queries --output /tmp/veil-final-solver
  To check each model's deepest available early query separately:
    python3 replay_deepest_queries.py --repo /path/to/veil \
      --queries /path/to/results/queries \
      --extra-queries /path/to/supplement-multisig/queries \
      --output /tmp/veil-deepest-solver --solver-timeout 2
  The deepest runner preserves source paths and SHA256 hashes; it accepts
  additional directories without modifying the original benchmark artifacts.

Purpose and scope
  These checks establish whether emitted first-order queries can be handled by
  cvc5 and whether the two formulations agree on sampled examples. They are
  separate from benchmark.py's preprocessing and SMT-output timings. They do
  not prove semantic equivalence for all Veil inputs, reconstruct the trace UI,
  or produce kernel-checked verification theorems. Probe theorems intentionally
  end with sorry after inspecting their query; genuine proof regression tests
  live separately in TraceEarlyIntroduction.lean.

  Models are Ring, DieHard, TwoPhaseCommit, RicartAgrawala, MultiSigAll,
  Peterson and FloodSet. Their source paths and assertions are in models.json
  and make_solver_checks.py. Each source is cut before the first #gen_spec,
  then receives #gen_spec and matched any-N-action trace probes. No later
  model-checking or invariant-verification commands are included.

Pipelines
  Both variants spell out the old trusted preprocessing sequence: nextSimp,
  guarded existential hoisting, veil_intros, veil_destruct, dispatcher dsimp,
  smtSimp, then dispatcher dsimp. The regenerated 'early' variant first runs
  the finalized introDataPrefix helper, which stops before proposition binders.
  The exact helper is embedded in make_solver_checks.py; production veil_bmc
  changes therefore do not silently alter either measured sequence.

  The query helper follows Veil's trusted lean-smt path: collect proposition
  hypotheses, clean context, push hints, introduce, negate goal, normalize,
  embed with embedBool=false, then prepareSmtQuery and logic ALL. Smt.solve uses
  Veil's default options plus finite-model-find, nl-ext-tplanes and
  enum-inst-interleave. No domain-size bound is imposed. SAT, UNSAT and UNKNOWN
  are cvc5 responses to that actual query; UNKNOWN:TIMEOUT is not UNSAT.

  The generator disables asynchronous elaboration and removes heartbeat limits,
  with maxRecDepth=10000. The normal simp limit of 100000 steps is unchanged.
  This makes the bottleneck visible; it does not assert that every trace passes
  all default Lean resource limits.

Measurements and archived provenance
  Every model initially translates and solves its probes, then Replay.lean
  independently solves the saved SMT-LIB sequentially. isolated_solver_ms is
  elapsed Smt.solve time from that replay: parsing/checking/model retrieval are
  included, while Lean preprocessing and translation are excluded. One sample
  per query is evidence of feasibility, not a stable performance estimate.

  Replay CSV query_bytes measures the exact string passed to Smt.solve after
  removing the literal (check-sat), since solve performs that operation itself.
  It is therefore 11 bytes smaller than the copied .smt2 file and the benchmark's
  serialized-byte count. Query-provenance hashes refer to the untouched copied
  files, including (check-sat); this difference is not stale metadata.

  Archived model sources and original SOLVER_RESULT logs were generated before
  the final helper was chosen. Their 'early' variant used full initial
  veil_intros; their theorem elaboration was asynchronous. Original solver_ms
  and smt_prep_ms are therefore retained only as nonisolated diagnostics, and
  must not be used as a performance comparison. Archived Replay*.log runs were
  sequential on an otherwise idle machine. The regenerated sources use the
  final data-prefix helper and Elab.async=false throughout. The comparison in
  final-query-comparison.csv connects these archived inputs to the finalized
  benchmark, and final-solver/ holds a fresh replay of the finalized queries.

  Ring's four archived queries came from an earlier matched old/early probe.
  Those exact generated source files are retained in source-provenance/.
  ReplayRing.lean and ReplayRing.log contain its separate sequential replay.
  Ring has no original SOLVER_RESULT record in this directory.

  All other archived queries were generated by the six model sources here.
  MultiSigAll old depth 8 failed at nextSimp's maximum simplification-step limit
  before query emission. MultiSigAll old depth 4 timed out after 10 seconds;
  early depth 4 returned UNSAT in its isolated replay; early depth 8 timed out.
  A timeout versus a definite answer is not a conflicting SAT/UNSAT result.

Comparing formulas
  The CSV records exact command equality ignoring command order. For all
  available non-Ring pairs this is true. Ring instead differs by implication
  currying: (a and b) implies c versus a implies (b implies c). The second
  comparison parses these generated SMT commands and applies only that valid
  Boolean equivalence before sorting. All 13 available archived pairs match
  after this normalization; the fourteenth pair has no old query.

  Sorting commands is a comparison device, not a script rewrite. It preserves
  declaration and assertion content for these emitted scripts; declaration
  order can still affect solver heuristics and runtime. The small parser is
  intended for these generated queries, not arbitrary SMT-LIB with comments.

Artifacts
  *.lean: generated probe/replay sources (historical absolute paths retained)
  *.smt2: exact serialized queries, including check-sat
  *.log: raw Lean output and solver responses
  solver-results.csv/json: outcomes, isolated timings and query comparisons
  models.json: model paths and assertions
  source-provenance/: earlier Ring source files
  execution.json: process status/time for runs made with run_solver_checks.py
  make_solver_checks.py, run_solver_checks.py, summarize.py: portable runners
  compare_final_queries.py: compare final queries to earlier archived inputs
  replay_final_queries.py: replay the final benchmark's depth-4/8 queries
  replay_deepest_queries.py: independent short-cap deepest-query checks

  solver-results.csv is a semantic/solver feasibility artifact. The final
  repeated preprocessing graphs should use results/runs.csv and stages.csv,
  never these early nonisolated preparation timings.
