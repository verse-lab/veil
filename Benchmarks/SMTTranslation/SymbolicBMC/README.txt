Veil issue #123: early introduction and symbolic BMC scaling

Start with report/index.html. It contains the executive findings, all 49 per-file
graphs, corpus outcome matrices, matched timing plots, exact selected queries,
sampled-depth summaries, raw-query links and technical appendices. report/report.txt
is the plain-text version. EXECUTIVE_SUMMARY.txt is the concise synthesis;
NEXT_FIXES.txt ranks further work and states its semantic acceptance criteria.

Scope: 49 model-bearing example files x exact depths 1,2,4,8,16,32 x old/early
orders = 588 primary observations. Files include related variants, not 49
independent protocols. Abstract symbolic queries do not instantiate the concrete
domains of the source #model_check commands. One selected assertion per file is
frozen in manifest.json. This is a single-observation feasibility/scaling sweep,
not a statistically repeated speedup study. Failed work and timed-out solves are
never plotted as completed timings. Query emission and solver acceptance/answers
are separate outcomes.

implementation.patch contains the production change and two regression files.
It introduces outer data/type binders before whole-target normalization, stops
before proof-domain binders, and retains the existing later pipeline. It does
not install any experimental dependency fixes. The source base and dependency
revisions are in environment.json. tests/ retains the complete successful
1226-job VeilTest build log and the new test sources.

results/ is the complete primary dataset, including sources, event logs, raw
SMT scripts, solver replay, checkpoints, hashes and original runner snapshots.
controls/ contains separate odd-depth and recursion-only checks. diagnostics/
contains standalone backend reproductions/candidate experiments, explicitly
separated from benchmark timings. synthetic/ preserves the earlier isolated
hoister experiment and equivalence sketches; its raised-limit measurements do
not belong in the primary tables. The earlier seven-model repeated experiment
is retained separately in the worktree and has been qualified as exploratory.

See DATASET_PROVENANCE.txt for the discarded preliminary run, namespace repair,
event-marker correction, affected cohorts and validation. Invalid observations
are excluded from this package. Original absolute execution paths are retained
as provenance; portable tools use checked relative artifacts. validation.json,
portable-validation.json and link-validation.json record the final audits.
SHA256SUMS covers every other packaged file. Unzip with report/ and results/
remaining siblings so the raw query/image links continue to resolve.

Reproduction commands are in runner/README.txt. Re-rendering graphs requires
matplotlib; report-tools/README.txt describes that interface. Use fresh output
directories for new measurements. Keep supplemental profiles separate.

The original issue's LamportMutexV1 branch/source is unavailable. This work
establishes behavior for the available corpus and regression models; it does
not claim a verified higher-depth result for that exact missing program.
Issue: https://github.com/verse-lab/veil/issues/123
