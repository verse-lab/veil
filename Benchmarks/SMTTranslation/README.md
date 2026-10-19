# SMT translation depth investigation

The comprehensive 49-file, six-depth before/after comparison is in [SymbolicBMC/report/index.html](SymbolicBMC/report/index.html), with raw data, all-model graphs, solver replay and follow-up diagnoses. The implemented change and semantic tests are described there.

[EarlyIntroduction/README.md](EarlyIntroduction/README.md) retains the earlier repeated seven-model experiment. It uses different assertions and raised limits; its backend helper omitted the production compatibility wrapper. Treat its preprocessing measurements as exploratory evidence and its backend figures as non-production diagnostics. Do not combine its tables with the comprehensive sweep.

Other files retain preliminary investigation artifacts:

- `ring_stages.py` and `RingResults.txt`: initial single-run Ring timings, superseded by the repeated seven-model measurements.
- `Pipeline.lean` and `PipelineResults.txt`: a prototype with additional early destruction; this is not the final conservative implementation.
- `QuantifierHoisting.lean` and `QuantifierHoistingResults.txt`: synthetic global versus component-wise hoisting experiments, relevant to future work but not implemented by this change.
- `HoistingEquivalences.lean`: logical equivalences examined for component-wise hoisting.
- `EarlyIntrosChecks.lean`: the earlier unrestricted introduction prototype. The final implementation stops at proof binders to preserve higher-order proof-header normalization.

Measurement scaffolds can intentionally end with `sorry`; they are not correctness tests. Production semantic and depth regressions are in `VeilTest/Regression/TraceEarlyIntroduction.lean` and `VeilTest/Performance/DeepBmcTranslation.lean`.
