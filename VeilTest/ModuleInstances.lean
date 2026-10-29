module

public import Examples.Modularity.Counters

#check TwoCounters.bounds.is_inv

-- Both families must be dispatched, and the occurrences have distinct fields.
example : TwoCounters.State.Label.inst_4_left__field__value ≠
    TwoCounters.State.Label.inst_5_right__field__value := by
  intro h
  cases h
