import Veil

/-!
# Depth-histogram bucketing

`#simulate` reports how deep each completed trace got. A single depth number says
nothing about a population of random traces, so the result carries the distribution.

These pin the bucketing itself, which is independent of the RNG. The end-to-end
line is covered by `SimulateStepBound` and `SimulateStateConstraintPrune`, whose
walks are forced and therefore give a fixed histogram.
-/

open Veil Veil.ModelChecker.Simulation Veil.ModelChecker.Concrete

/-- Fail with a readable message; `assert!` panics with a backtrace instead. -/
private def expect (message : String) (cond : Bool) : IO Unit :=
  unless cond do throw (IO.userError message)

-- A small step budget gets one bucket per reachable depth, `0 … maxSteps + 1`.
#eval do
  let h := depthHistogramFor 3
  expect "a small budget must not be bucketed" (h.bucketWidth == 1)
  expect "buckets must cover depths 0 through maxSteps + 1" (h.counts.size == 5)

-- A large step budget is capped, so a reported result stays small.
#eval do
  let h := depthHistogramFor 100000
  expect "bucket count must be capped" (h.counts.size == Histogram.maxBuckets)
  expect "buckets must together span the whole budget"
    (h.counts.size * h.bucketWidth ≥ 100000 + 2)

-- Recorded depths land in the right buckets, and none is lost.
#eval do
  let h := [0, 1, 1, 1, 2, 4].foldl Histogram.record (depthHistogramFor 3)
  expect "counts must be per depth when unbucketed" (h.counts == #[1, 3, 1, 0, 1])
  expect "every recorded trace must be counted" (h.total == 6)

-- A depth past the last bucket is absorbed rather than dropped.
#eval do
  let h := Histogram.record (depthHistogramFor 3) 99
  expect "an out-of-range depth must land in the last bucket" (h.counts == #[0, 0, 0, 0, 1])
  expect "an out-of-range depth must still be counted" (h.total == 1)

-- The live progress panel carries the distribution too, not just the final result,
-- so it is visible while the run is still going.
#eval do
  let (id, _) ← allocProgressInstance (.simulation {})
  let h := [1, 1, 2].foldl Histogram.record (depthHistogramFor 3)
  updateSimulationProgress id "Running random traces (3/10)" 3 10 h
  let p ← getProgress id
  let carried :=
    match p.details with
    | .simulation m => m.depthHistogram.counts == #[0, 2, 1, 0, 0] && m.depthHistogram.total == 3
    | .modelCheck .. => false
  expect "live progress must carry the depth histogram" carried
