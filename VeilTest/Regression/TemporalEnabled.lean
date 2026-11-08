module

public import Veil

open Lentil

set_option veil.smt.trust false

veil module TemporalEnabled

param bound : Nat
param actionBound : Nat
immutable individual limit : Nat
individual counter : Nat
relation seen (n : Nat)

/--
warning: Field `seen` uses a hybrid representation. Updates over potentially unbounded domains (e.g. `f I := ...`) can switch it to the canonical case, where default `Hashable` or `BEq` instances can merge distinct states and miss reachable states during model checking. For meaningful hashing and equality in the canonical case, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation; see `docs/DSL-Reference.md#hybrid-field-representations`. If the field stays concrete, suppress this warning with `set_option veil.warnHybridFields false`. Alternatively, consider `TMap` if it better fits your model.
-/
#guard_msgs in
#gen_state

after_init {
  counter := bound
  seen N := false
}

action mark (n : Fin actionBound) {
  require n.val < limit
  seen n.val := true
}

action disabled {
  require false
}

transition native (n : Fin actionBound) {
  counter' = n.val
}

ghost relation atValue (n : Nat) := counter = n
theory ghost relation belowLimit (n : Nat) := n < limit

invariant [counterRefl] counter = counter

#gen_spec

-- Parameterized ghosts, theory fields and module parameters retain their binders.
temporal [ghostArgs] ⌞ belowLimit bound ⌟ → (⌜ atValue bound ⌝ → ⌜ atValue bound ⌝)
temporal (only := verify) [markEnabled] ∀ n : Fin actionBound, ⌞ n.val < limit ⌟ → Enabled (mark n)
temporal (only := verify) [neverEnabled] ¬ Enabled disabled

prove_temporal_by [ghostArgs]
  tintro hBound hAt
  tassumption

prove_temporal_by [markEnabled]
  tclear hInit hNext hInv
  veil_solve_temporal

prove_temporal_by [neverEnabled]
  tclear hInit hNext hInv
  veil_solve_temporal

-- The statement accessor agrees with the generated theorem, including all binders.
example : temporal_theorem_body_of% ghostArgs := ghostArgs._proof

run_meta do
  for name in [``markEnabled._proof, ``neverEnabled._proof,
      ``mark.ext.enabled_local_eq, ``native.ext.enabled_derived_eq] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected axiom in {name}: {axiomName}"

end TemporalEnabled

-- Exercise the shared proof-mode extension with both partitions nonempty.
example {σ : Type} (p q : pred σ) : (□ p ∧ q) |-tl- (□ p ∧ q) := by
  tstart hp hq
  tsplit_by_persistency <;> tassumption
