Reproducing the paired sweep
===========================

Use the checkout at baseline commit 543817e6 and apply implementation.patch.
Build with the repository's pinned dependencies and native cvc5 plugin:
  lake build VeilTest

From this artifact's root (adjust paths as necessary):
  python3 runner/run_batch.py --repo /path/to/checkout \
    --manifest manifest.json --out fresh-results
  python3 runner/solve_batch.py --repo /path/to/checkout --out fresh-results
  python3 runner/validate_results.py --manifest manifest.json \
    --results fresh-results --output fresh-validation.json
  python3 runner/compare_local_queries.py --results fresh-results \
    --output fresh-logical-query-comparison

Both pipelines run on the same compiled checkout. The early pipeline explicitly
replays the committed tactic order; the local one calls the new internal helpers.
The default variants are early/local, and default depths are 1,2,4,8,16,32.
Do not merge this dataset with the prior old/early comparison. Use a fresh output
directory for changed code, options, manifests or instrumentation.

The runner loads the native cvc5 plugin even for extraction, since source setup
may need native operations. Helpers are enclosed in an unnamed section; event
marker commands use Lean.withOptions. The watchdog rejects a pipeline without
its query-begin marker, and rejects source errors outside query boundaries.
No output theorem is admitted. The extraction-complete diagnostic is expected.

Render the report with matplotlib installed:
  python3 report-tools/report.py --manifest manifest.json \
    --exclusions exclusions.json --results fresh-results --out-dir fresh-report \
    --logical-comparison fresh-logical-query-comparison.csv
  python3 report-tools/check_reporting.py

Review the executive summary and environment/suite evidence before reusing them
for a new run. Report configuration records its data-input hashes; the delivered
package additionally records every artifact's SHA-256. Raw paths describe the
original execution location; the tools support relocated query/source artifacts.

The optional step-profile runner is a separate normalization-only diagnostic.
It enables simp step tracing and stops before context destruction/SMT; it is not
part of the 588-cell outcome/timing dataset and does not yield solver answers.

Additional diagnostics (after the primary run, so timing is uncontended):
  python3 step-profile/runner/run_batch.py --repo /path/to/checkout \
    --manifest manifest.json --out step-profile/results \
    --models Ivy_Blockchain Tutorial_FloodSet Ivy_Ring
  python3 runner/summarize_step_profile.py --root .
  python3 runner/summarize_results.py --root .

solver-controls records three fresh native replays of paired definite-result
changes, newly emitted queries, and large observed solver-time changes (at least
5x, with the slower call at least 500 ms). These data remain separate from the
primary sweep. replay_controls.py documents the selection and alternating order.

Extended native checks use a separate 30-second cap on the three pairs that lost
a definite primary answer. The order/grouping probe generates four logically
audited scripts for Ivy TwoPhaseCommit depth 8. These experiments do not modify
primary queries. See SOLVER_BEHAVIOR.txt and runner/replay_extended.py,
runner/probe_solver_order.py and runner/summarize_diagnostics.py. Historical
run_full.py and run_diagnostics.py retain the original machine paths as execution
records; the commands above accept explicit checkout/output paths for fresh runs.
