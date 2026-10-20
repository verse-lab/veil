# SMT translation depth investigation

The latest comparison is [per-transition normalization versus exact transition caching](ActionCache/report/index.html): 49 model-bearing files, six exact depths, all-model graphs, cold setup costs, emitted SMT queries, native solver replay, semantic audits and separate solver controls. [The incremental code diff](ActionCache/implementation.patch) applies on top of the preceding per-transition implementation. Enable `veil.experimental.bmcCache` before `#gen_spec` to opt in.

The preceding [early introduction versus per-transition normalization comparison](TransitionLocal/report/index.html) retains its own raw measurements and diagnostics. [Its code diff](TransitionLocal/implementation.patch) is against commit `543817e6`. The studies use separate fresh measurements; do not pool their timings.

The earlier [original-order versus early-introduction comparison](SymbolicBMC/report/index.html) retains its own raw data, graphs and diagnoses. Its timings are separate from the fresh early/local sweep.

[EarlyIntroduction/README.md](EarlyIntroduction/README.md) retains the earlier repeated seven-model experiment. It uses different assertions and raised limits; its backend helper omitted the production compatibility wrapper. Treat its preprocessing measurements as exploratory evidence and its backend figures as non-production diagnostics. Do not combine its tables with the comprehensive sweep.

Other files retain preliminary investigation artifacts:

- `ring_stages.py` and `RingResults.txt`: initial single-run Ring timings, superseded by the repeated seven-model measurements.
- `Pipeline.lean` and `PipelineResults.txt`: a prototype with additional early destruction; this is not the final conservative implementation.
- `QuantifierHoisting.lean` and `QuantifierHoistingResults.txt`: earlier synthetic global versus component-wise hoisting experiments; the production local implementation and its limits are documented in TransitionLocal.
- `HoistingEquivalences.lean`: logical equivalences examined for component-wise hoisting.
- `EarlyIntrosChecks.lean`: the earlier unrestricted introduction prototype. The final implementation stops at proof binders to preserve higher-order proof-header normalization.

Measurement scaffolds can intentionally end with `sorry`; they are not correctness tests. The new paired benchmark instead stops with an explicit extraction diagnostic and claims no proof. Production semantic and depth regressions are in `VeilTest/Regression/TraceEarlyIntroduction.lean`, `VeilTest/Regression/TraceLocalNormalization.lean`, `VeilTest/Regression/TraceCachedNormalization.lean` and `VeilTest/Performance/DeepBmcTranslation.lean`.
