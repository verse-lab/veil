module

public meta import Veil.Core.Tools.ModelChecker.Simulation.Basic
public meta import Veil.Core.Tools.ModelChecker.Concrete.Progress
public meta import VeilTest.TestUtil

public meta section

/-!
Simulation-specific runtime regressions: depth histograms stay bounded and
simulation progress records trace counts and the depths reached by those traces.
-/

open Veil Veil.ModelChecker.Simulation Veil.ModelChecker.Concrete

-- Large budgets must keep histogram storage bounded while covering every depth.
#eval do
  let h := depthHistogramFor 100000
  expect "bucket count must be capped" (h.counts.size == Histogram.maxBuckets)
  expect "buckets must span the whole budget"
    (h.counts.size * h.bucketWidth ≥ 100000 + 2)

-- Simulation progress must expose the trace budget, completed traces, and depth histogram.
#eval do
  let (id, _) ← allocProgressInstance (.simulation {})
  let h := [0, 1, 1, 1, 2, 4, 99].foldl Histogram.record (depthHistogramFor 3)
  expect "depths must be counted, with overflow in the last bucket"
    (h.counts == #[1, 3, 1, 0, 2] && h.total == 7)
  updateSimulationProgress id "Running random traces (7/50)" 7 50 h
  let before ← getProgress id
  expect "a simulation instance must report simulation metrics" <|
    match before.details with
    | .simulation m => m.tracesRun == 7 && m.numTraces == 50 && m.depthHistogram.counts == h.counts
    | .modelCheck .. => false
