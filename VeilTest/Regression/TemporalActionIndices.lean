module

public import Veil

/-! `unveil_temporal` must expand every action in `NextStep`, including indices above two.
Use distinct updates so the preservation proof needs each branch to be unfolded. -/

veil module TemporalActionIndices

individual x : Nat

after_init { x := 0 }

action a0 { pure () }
action a1 { pure () }
action a2 { pure () }
action a3 { x := x + 1 }
action a4 (n : Fin 3) { x := x + n.val }
action a5 { x := x + 2 }

temporal (only := verify) [xMono] ∀ k : Nat, □ (⌜ k ≤ x ⌝ → ◯ ⌜ k ≤ x ⌝)
temporal (only := verify) [xMonoWithoutFourth]
  ∀ k : Nat, □ ((⌜ k ≤ x ⌝ ∧ ¬ ⟨a3⟩) → ◯ ⌜ k ≤ x ⌝)

#gen_spec

prove_temporal_by [xMono]
  tclear hInit hInv
  tintro k
  tmonotone
  unveil_temporal
  grind

-- Excluding an action must preserve the original indices of the remaining branches.
prove_temporal_by [xMonoWithoutFourth]
  tclear hInit hInv
  tintro k
  tmonotone
  unveil_temporal
  grind

end TemporalActionIndices
