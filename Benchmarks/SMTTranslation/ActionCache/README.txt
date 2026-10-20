Reproduce the exact-normalization cache experiment
================================================

The production option is veil.experimental.bmcCache (default false). Set it
before #gen_spec to generate exact normal forms, and leave it true for veil_bmc
to reuse them. Turning it off selects per-transition normalization.

Start from commit 543817e690debe6fbc9b518fb2694549d5986e90, apply the preceding
TransitionLocal implementation.patch, then this package's implementation.patch.
The full source snapshot and baseline/Core.lean let reviewers inspect both
states. Build with `lake build Veil VeilTest`.

Runner usage (substitute the worktree and output paths):
  python3 runner/run_batch.py --repo WORKTREE --out RESULTS --manifest manifest.json
  python3 runner/solve_batch.py --repo WORKTREE --out RESULTS
  python3 runner/compare_local_queries.py --results RESULTS --output AUDIT

run.py is the shared measurement library; use run_batch.py for this experiment
rather than its retained predecessor standalone entry point.

The scripts require the repository's built native cvc5 plugin. The archived
run_full.py also checks/fingerprints the test log and compiled artifacts, and
contains this investigation's original absolute worktree path. Copy/edit that
path when reproducing on another machine. Do not reuse a partially populated
RESULTS directory for a different implementation; its checkpoints deliberately
skip completed cells. report.py and package.py record the original layout.

Primary results have one observation per cell. Read METHODS.txt before treating
ratios or setup differences as stable estimates. Artifacts in controls, if
present, are a separate diagnostic experiment and are not pooled with primary
timings.
