# SMT translation depth investigation

The [exact transition-cache report](ActionCache/README.md) compares per-transition normalization with cached, kernel-checked transition normal forms across all 49 existing model-bearing example files and six exact depths. It includes all-model graphs, setup costs, solver outcomes, semantic checks and reproduction scripts.

The [complete investigation snapshot](https://github.com/verse-lab/veil/tree/e98a4b64f68359d94f2f118bc61651e197bc9d6f/Benchmarks/SMTTranslation) retains the earlier original-order/early-introduction and early-introduction/per-transition comparisons, together with every raw query and log. The current PR keeps the review focused on source changes and the final results; the snapshot preserves the full evidence.

Production semantic and depth regressions are in `VeilTest/Regression/TraceEarlyIntroduction.lean`, `VeilTest/Regression/TraceLocalNormalization.lean`, `VeilTest/Regression/TraceCachedNormalization.lean` and `VeilTest/Performance/DeepBmcTranslation.lean`.
