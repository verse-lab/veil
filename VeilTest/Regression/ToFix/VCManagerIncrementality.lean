module

public import Veil

/-
Single-module regression fixture for VC manager snapshot consistency.

Open this file, wait for elaboration, then delete the entire `step bounded`
proof below. Currently, `#gen_theorems` reports:
  (kernel) unknown constant 'VCManagerIncrementality.step_bounded'
The Lean environment rolls back, but the global manager retains the deleted
theorem as a successful interactive witness. A fresh open without that proof
does not report this error. This is a manager-state regression, rather than a
test of tactic snapshot reuse inside `prove_veil_invariant_goal`.

Batch compilation alone cannot reproduce the edit. Run the LSP regression:
  python3 scripts/tests/test-invariant-goal-incrementality.py --vc-manager
This mode is expected to fail until the manager's incremental state is fixed.
-/

veil module VCManagerIncrementality

individual x : Nat
after_init { x := 0 }
action step { require x < 10; x := x + 1 }
invariant [bounded] x ≤ 10

-- Keep the interactive proof as the only successful witness for this VC.
set_option veil.solver "custom"
#gen_spec

prove_veil_invariant_goal initializer bounded using wp by
  done

prove_veil_invariant_goal step bounded using wp by
  grind

#gen_theorems

end VCManagerIncrementality
