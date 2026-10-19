Reproducing the primary sweep

Run from the package root. Use a Veil checkout at the recorded base commit and
toolchain/dependency revisions (environment.json). Apply implementation.patch
for the production change/tests, build Veil, and prebuild the imported
Examples.StellarConsensus.SCPTheory support module. The batch runner explicitly
encodes both old and early orders, so its comparison is controlled within one
checkout. The native cvc5 plugin must be present under .lake/packages/cvc5/.

Set REPO to that checkout and OUT to a NEW output directory. Do not overwrite
the archived results/ merely to reproduce measurements.

  python3 runner/run_batch.py --repo "$REPO" --manifest manifest.json --out "$OUT"
  python3 runner/solve_batch.py --repo "$REPO" --out "$OUT" --solver-timeout 10
  python3 runner/compare_queries.py --results "$OUT" --output paired-queries
  python3 runner/validate_results.py --results "$OUT" --manifest manifest.json --output validation-new.json
  python3 report-tools/report.py --manifest manifest.json --exclusions exclusions.json --results "$OUT" --out-dir report-new --query-comparison paired-queries.csv

Pass --models NAME ... and/or --depths N ... to restrict the sweep. The full-grid
validator intentionally expects all 588 primary cells. --profile recursion_only
sets maxRecDepth=10000 but keeps maxHeartbeats=200000. Default uses recursion512;
relaxed additionally removes the heartbeat limit and was not used in the primary
sweep. Always keep separate output roots for different profiles/controls.
The output is checkpointed; completed cells are retained on resume. Use a fresh
directory for independent repeated measurements. Runs are single observations,
sequential within the process and with alternating variant order/shared setup.

Report generation requires matplotlib; see report-tools/README.txt. Tables-only
mode does not create a complete visual report. For the existing portable package:

  python3 runner/validate_results.py --results results --manifest manifest.json --output portable-recheck.json --portable-only

Original recorded absolute paths are execution provenance. The comparator,
validator and report support relocated read-only data. solve_batch.py is intended
for new extraction output; to replay archived queries at another location, create
new replay inputs with checked query hashes rather than editing archived records.

run.py is the common helper and optional isolated-cell runner. Keep it beside
run_batch.py and solve_batch.py. The original primary runner snapshot is retained
under results/runner-snapshot; the scoped namespace repair snapshot is under
results/provenance/. Current convenience runners include that correction. The
precise correction, replaced cohorts and six formula-equivalence checks are in
DATASET_PROVENANCE.txt and provenance/.

finish_benchmark.py, diagnose_backends.py and package_report.py preserve the
investigation's original orchestration, including its original local paths.
They are provenance scripts, not portable one-command entry points. The commands
above are the portable reproduction interface; adapt diagnostic source paths and
launch directly with the recorded native plugin if running the functional probes.
No dependency patches or diagnostic simproc candidates are installed by the
production implementation.patch.
