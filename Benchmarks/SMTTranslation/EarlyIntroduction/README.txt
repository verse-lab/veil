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

Veil #123: repeated multi-model early-introduction measurements

Reproduction
  1. Build Veil in the checkout/worktree: lake build Veil
  2. Run on an otherwise idle machine:
       python3 benchmark.py --repo /absolute/path/to/veil --out-dir results
  3. Install matplotlib in your Python environment and render:
       python3 plot.py --results results --out-dir figures

The scripts accept an explicit --repo because they can live outside the
checkout. All benchmark files, logs, failure markers and SMT-LIB output are
written beneath --out-dir. No production file is modified by the runner.

Models and assertions
  Ring:             ordered ring, quantified relations; exists a leader
  DieHard:          six jug actions over Nat; big = 4
  TwoPhaseCommit:   commit protocol; exists a node deciding commit
  RicartAgrawala:    mutual exclusion; exists a node holding the lock
  MultiSigAll:      five sorts / high-arity relations; exists a paid tuple
  Peterson:         finite enums; exists a critical/release program counter
  FloodSet:         higher-order delivery choices / arithmetic; decision exists

The source prefix is taken through the model declarations, followed by one
#gen_spec. Generated traces use any 2, 4, 8, 16 and 32 actions. These are
measurement scaffolds closed with sorry; they are not verification results.
Separate solver comparisons are documented in the solver-results artifacts.

Variants
  current: explicit original nextSimp -> guarded hoist -> intros/destruct ->
           dispatcher dsimp -> smtSimp -> dispatcher dsimp pipeline.
  early:   the same pipeline preceded by the data-prefix introduction helper.
           The helper stops at the first proposition binder, preserving proof
           header normalization. Its exact source is embedded in benchmark.py.

Both pipelines are explicit and remain comparable when production veil_bmc
changes. The exploratory backend uses embedBool=false but omits the production
backwards-compatibility wrapper, as qualified above. The SMT query uses logic ALL. No solver is run here.

Execution and measurement
  Elab.async=false prevents concurrent proof elaboration. One process handles
  all depths/repetitions of one model. Processes run sequentially. Each cell
  requests three repetitions; original/early order alternates across repeats
  and depths. Same-process cache effects remain possible. Median and min/max
  show observed variation, not a statistical confidence interval.

  maxHeartbeats=0 and maxRecDepth=10000 isolate the ordinary simp cap of
  100000 steps. These graphs do not assert that all depths pass every default
  Lean resource limit. Model processes have a 180-second cap; the batch has
  a 1260-second cap. Failure of a preprocessing stage skips later repetitions
  and larger depths of that variant. Skipped depths are untested.

  Stage timers exclude startup, model generation and instrumentation. The
  principal preprocessing metric sums all successful original/early stages.
  The first repetition separately measures lean-smt preprocessing, translation
  and serialization, and writes the query. Its endpoint adds those stages to
  that repetition's preprocessing time. No SMT solver time is included.
  A downstream SMT failure does not discard a completed preprocessing sample.

  Failed and interrupted samples have no completed-time value. The CSV keeps
  failure elapsed time in a distinct field; figures never plot it as completed
  work. If a model process times out after some complete repetitions, those
  repetitions are retained and the sample count is shown.

Artifacts
  results/metadata.json: commit, source/script hashes, resources and machine
  results/runs.csv:      every requested sample and status
  results/stages.csv:    exact stage timings and query byte/command counts
  results/sources/:     generated standalone Lean sources
  results/logs/:        raw output and process status
  results/queries/:     serialized SMT-LIB from first repetitions
  figures/summary.csv:  per-cell median/min/max and sample count
  figures/smt-output.csv: preprocessing/downstream split and query bytes
  figures/*.{png,svg}:  overview and individual model figures

Use the new sequential data for comparisons. Earlier investigation Ring
measurements were single observations made while other work was running and
should not be mixed with this dataset.

Retained run provenance
  The original seven-model batch is results/. Its exact generator is archived
  as benchmark-main-run.py; the SHA-256 matches results/metadata.json. The
  current benchmark.py adds process-group cleanup and append/close event logs
  for robust timeout handling. It also records preprocessing completion before
  optional SMT work. Timed pipeline tactics and limits are unchanged.

  The original MultiSigAll and FloodSet model-wide 180-second budgets include
  all lower depths and repetitions; reaching that cap is not evidence that an
  individual larger-depth query cannot finish. Fresh one-repetition probes are
  retained in supplement-* directories. combine.py appends their samples with
  a batch column, preserving original censored rows. Figures show n=1 for
  supplemental-only points; their observations are not three-run medians.

  A guarded cleanup killed the original MultiSigAll Lean child immediately
  after its Lake parent timed out, before the next model's measured stages.
  After the main batch exited, a host process check confirmed no Lean or Lake
  processes remained. Supplemental runs use automatic process-group cleanup.
  The improved event log avoids buffered stdout loss at an abrupt timeout.

Example merging and plotting (use the supplement directories actually present):
  python3 combine.py --main results --supplement supplement-multisig \
    supplement-flood-current supplement-flood-early --out-dir combined
  python3 plot.py --results combined --out-dir figures \
    --solver-results final-solver/solver-results.csv

The final solver matrix shows one isolated solve per exact depth4/8 query,
with SAT, UNSAT, timeout-at-10s, and no-query statuses distinguished. It does
not estimate a solver speedup. Solver reproduction is in SOLVER_README.txt.
