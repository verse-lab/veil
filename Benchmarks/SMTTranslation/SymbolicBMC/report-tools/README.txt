Symbolic BMC report generation

Inputs
  ../manifest.json: authoritative, hashed inventory and exact per-model assertion.
  ../exclusions.json: support-only files excluded from the model inventory.
  ../results/runs.csv: one row per requested model/depth/variant/profile.
  ../results/stages.csv: per-phase begin/complete/failure records.
  ../EXECUTIVE_SUMMARY.txt (optional): final findings and ranked next fixes.
    Override with --executive-summary PATH. It is copied, hashed, and inserted near
    the beginning of HTML/text; plain paragraphs and numbered lines are preserved.
    HTML characters are escaped rather than interpreted as markup.

Reproduce (Python 3.12 or newer)
  python3 -m pip install matplotlib==3.11.2
  python3 report.py --manifest ../manifest.json --exclusions ../exclusions.json \
    --results ../results --out-dir ../report \
    --query-comparison ../query-comparison/paired.csv \
    --logical-comparison ../query-comparison/logical.csv

The standard library produces tables and HTML without matplotlib when --tables-only
is supplied. This intentionally omits figure generation; use a full run for a
standalone report with all referenced figures. Check the reporting boundary with:
  python3 check_reporting.py

Output
  index.html: complete, searchable model/query/outcome inventory, figures and notes.
    Per-model sections link each emitted raw SMT-LIB file. Keep report/ and results/
    as siblings when relocating the package to preserve the generated relative links.
  report.txt: plain-text report and query inventory.
  summary.json: exact counts and matched observed ratios for downstream summaries.
  sampled-depth-summary.csv: largest successful SAMPLED exact depth per variant for
    serialization, definite solver answers and preprocessing discharge separately;
    retains every successful sampled depth and makes no monotone-bound claim.
  outcomes.csv: all requested model/depth/variant cells, including missing results.
    solver_seconds retains raw elapsed wrapper time, including censored calls;
    completed_solver_seconds is populated only for definite SAT/UNSAT responses.
    Figures use only the completed field.
  appendices/: inventory, pipeline audit, backend findings and proposed next fixes.
  environment.json: exact hardware, Lean/dependency versions and suite-log hash.
  inventory.csv: every model, original source hash, selected assertion and scope.
  queries.csv: only actual emitted queries with recorded content hashes.
  failures.csv / failure-counts-by-phase.csv: diagnostics/phase totals, with blocked
    setup queries explicitly identified as unattempted rather than failed attempts.
  query-completion-differences.csv: cells where only one variant emitted a query.
  outcome-transitions.csv: original-to-early outcome counts.
  matched-timings.csv: only completed emitted-query timings in both variants.
  matched-preprocessing-timings.csv: completed Veil phases even if a later stage fails.
  selected-early-phase-costs.csv: exact phase seconds behind the all-file early panels.
  definite-disagreements.csv: paired definite answers which differ, counting preprocessing
    discharge as UNSAT while retaining its distinction from a solver response.
  figures/outcome-matrix-*.{png,svg}: all models, partitioned into readable pages.
  figures/outcome-counts.{png,svg}: all-model outcome counts at each exact depth.
  figures/matched-preprocessing-timings.{png,svg}: paired completed Veil phases.
  figures/early-phase-costs-*.{png,svg}: early phase shares at explicitly varying depths.
  figures/matched-query-timings.{png,svg}: matched completed SMT-query stage costs.
  figures/matched-completed-timings.{png,svg}: query stages plus definite solver call.
  figures/models/*.{png,svg}: a separate preprocessing/query/solver/size/phase/outcome figure
    for every file. Timeout/unknown solver calls have no completed timing point.

Interpretation
  Old/Original means the pre-change tactic order replayed on the current source
  base eb41b59673a179ad05773ceca18667ba25b7f079, not the historical issue commit.
  Each source file has one selected assertion (possibly a safety conjunction);
  overlapping variants are retained, so these are not 49 independent protocols.
  Primary query settings: maxHeartbeats=200000, maxRecDepth=512; default Veil
  nextSimp/guarded-hoisting maxSteps=100000. Existing dependency-local downstream
  overrides remain. Setup has separately recorded source options. The explicit
  trusted SMT backend and finite-model-find are standardized; source-specific
  query solver choices and original concrete model-checking commands are not run.
  Batched setup
  measurements are shared and must not be summed across query cells.
  Queries contain EXACTLY N actions, not all lengths at most N. The symbolic
  types/parameters are abstract or unbounded; concrete #model_check instantiations
  are not used. Manifest notes define the selected safety-property scope.
  Model setup is shared within a batch; each trace is a separate Lean command
  with its own command budget. Elab.async=false enforces sequential execution;
  variant order alternates by model/depth. Process caches are shared, so these
  paired single observations are not independent cold-start repetitions.
  No reconstructed proof is claimed by the benchmark scaffold.
  One observation per cell gives feasibility and approximate costs, not a stable
  speedup distribution. The old seven-model repeated benchmark has different
  assertions/settings and must remain separate. Its backend helper omitted the
  production compatibility wrapper: its Veil-preprocessing timings remain exploratory
  evidence, while its backend measurements do not establish production behavior.
  solver_ms measures Smt.solve: native manager/solver creation, parsing, checkSat,
  and native model-value/domain or unsat-core retrieval. It excludes Lean proof/model
  reconstruction and trace rendering. The 10-second tlimit-per limits checkSat; a
  separate 15-second watchdog covers the active wrapper call.
  Completed-query times exclude process startup, model setup, query/VC elaboration
  and solving. They include Veil preprocessing, SMT preprocessing, translation and
  serialization. Solver timeout still permits a completed query timing. Failed
  query attempts never appear as completed timings. Completed Veil preprocessing
  remains a valid separate metric when a subsequent SMT phase fails. A completed
  measurement recorded as 0 ms is omitted on logarithmic axes and explicitly labeled
  as below timer resolution; it is not mislabeled as an absent completion. Raw table
  values are unchanged. Each model
  shows these curves as dashed lines, with full emitted-query stages as solid lines.
  Preprocessing discharge is
  separate from solver UNSAT and emits no SMT query.
  Resource failure type and failing phase are independent: e.g. E:R is recursion
  failure in SMT embedding. G:— means the query was not attempted because model
  setup failed. Missing and pending cells remain visible.

The script rejects duplicate cells within a selected profile rather than silently
choosing one observation. report-config.json hashes the exact inputs used.
