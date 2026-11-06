module

public import Veil

/-! Temporal proofs must work without a dummy `invariant true`, both with eager and deferred
verification preparation, and whether or not the proof keeps the invariant hypothesis. -/

veil module TemporalNoInvariants

individual x : Nat

#gen_state

after_init { x := 0 }

action inc { x := x + 1 }

temporal (only := verify) [positiveStable] □ (⌜ x > 0 ⌝ → ◯ ⌜ x > 0 ⌝)

#gen_spec

prove_temporal_by [positiveStable]
  tclear hInit hInv
  tmonotone
  unveil_temporal
  grind

temporal (only := verify) [positiveStableWithInvariants] □ (⌜ x > 0 ⌝ → ◯ ⌜ x > 0 ⌝)

prove_temporal_by [positiveStableWithInvariants]
  tclear hInit
  tmonotone
  unveil_temporal
  grind

end TemporalNoInvariants

set_option veil.deferVCGeneration true

veil module TemporalNoInvariantsDeferred

individual x : Nat

#gen_state

after_init { x := 0 }

action inc { x := x + 1 }

temporal (only := verify) [positiveStable] □ (⌜ x > 0 ⌝ → ◯ ⌜ x > 0 ⌝)

#gen_spec

prove_temporal_by [positiveStable]
  tclear hInit
  tmonotone
  unveil_temporal
  grind

end TemporalNoInvariantsDeferred
