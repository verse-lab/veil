import Lean.Data.Json

namespace Veil
open Lean

/-- Counts of `Nat` samples, bucketed so that the array stays small even when the
samples range widely.

Bucket `i` covers `[i * bucketWidth, (i+1) * bucketWidth)`, and the last bucket
absorbs anything beyond, so no sample is ever dropped. -/
structure Histogram where
  /-- How many values each bucket spans. -/
  bucketWidth : Nat := 1
  /-- Sample counts, one per bucket. -/
  counts : Array Nat := #[]
deriving Inhabited, Repr, ToJson, FromJson

namespace Histogram

/-- Upper bound on the number of buckets, so a wide range cannot blow up the size
of a histogram that gets serialised. -/
def maxBuckets : Nat := 32

/-- An empty histogram covering samples `0 … span - 1`. -/
def forRange (span : Nat) : Histogram :=
  if span == 0 then {} else
    let buckets := min maxBuckets span
    let width := (span + buckets - 1) / buckets
    { bucketWidth := width, counts := Array.replicate buckets 0 }

/-- Record one sample. Samples past the last bucket land in it rather than being
dropped. -/
def record (h : Histogram) (sample : Nat) : Histogram :=
  if h.counts.isEmpty then h
  else
    let width := max 1 h.bucketWidth
    let idx := min (h.counts.size - 1) (sample / width)
    { h with counts := h.counts.modify idx (· + 1) }

/-- Total number of samples recorded. -/
def total (h : Histogram) : Nat := h.counts.foldl (· + ·) 0

/-- The non-empty buckets, as `(low, high, count)` triples. -/
def buckets (h : Histogram) : Array (Nat × Nat × Nat) :=
  let width := max 1 h.bucketWidth
  h.counts.zipIdx.filterMap fun (count, i) =>
    if count == 0 then none else some (i * width, i * width + width - 1, count)

end Histogram
end Veil
