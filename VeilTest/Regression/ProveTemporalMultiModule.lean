module

public import Veil
public import Veil.Liveness

/-! Both modules deliberately reuse the property name, with different obligations.
The LSP test instruments the marked proofs to count tactic execution:
  python3 scripts/tests/test-temporal-proof-incrementality.py --multi-module
Add `--deferred` to also exercise deferred VC generation in both modules. -/

open Lentil

veil module ProveTemporalFirst

individual x : Nat
after_init { x := 0 }
action step { require x < 10; x := x + 1 }
invariant [bounded] x ≤ 10
temporal (only := verify) [stable] ⌜ x ≤ 10 ⌝ → ⌜ x ≤ 10 ⌝
#gen_spec

prove_temporal_by [stable]
  tstart hInit hNext hInv
  tdsimp only [stable]
  tintro h
  tassumption -- first proof

end ProveTemporalFirst

veil module ProveTemporalSecond

individual x : Nat
after_init { x := 0 }
action step { require x < 19; x := x + 2 }
invariant [bounded] x ≤ 20
temporal (only := verify) [stable] ⌜ x ≤ 20 ⌝ → ⌜ x ≤ 20 ⌝
#gen_spec

prove_temporal_by [stable]
  tstart hInit hNext hInv
  tdsimp only [stable]
  tintro h
  tassumption -- second proof

end ProveTemporalSecond

-- Both generated theorems remain available after switching modules.
example := @ProveTemporalFirst.stable._proof
example := @ProveTemporalSecond.stable._proof
