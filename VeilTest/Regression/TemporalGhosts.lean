module

public import Veil

/-! Ghosts used in temporal atoms must share the concretized fields of the transition.
Cover relations and functions, including a ghost parameter, a module parameter and a theory field. -/

veil module TemporalGhosts

param step : Nat
immutable individual floor : Nat
individual x : Nat

after_init { x := floor }

action inc { x := x + step }

ghost relation positive := x > floor
ghost relation atLeast (k : Nat) := x ≥ floor + k
ghost function currentX : Nat := x

invariant [aboveFloor] x ≥ floor

temporal (only := verify) [positiveStable] □ (⌜ positive ⌝ → ◯ ⌜ positive ⌝)
temporal (only := verify) [atLeastStable]
  ∀ k : Nat, □ (⌜ atLeast k ⌝ → ◯ ⌜ atLeast k ⌝)
temporal (only := verify) [currentXMono]
  ∀ k : Nat, □ (⌜ k ≤ currentX ⌝ → ◯ ⌜ k ≤ currentX ⌝)

#gen_spec

prove_temporal_by [positiveStable]
  tclear hInit hInv
  tmonotone
  unveil_temporal
  grind

prove_temporal_by [atLeastStable]
  tclear hInit hInv
  tintro k
  tmonotone
  unveil_temporal
  grind

prove_temporal_by [currentXMono]
  -- Keep the invariant to exercise the existing narrowing path as well.
  tclear hInit
  tintro k
  tmonotone
  unveil_temporal
  grind

end TemporalGhosts
