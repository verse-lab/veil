module

public import Veil
public import Veil.Liveness

open Lentil

/-! A `temporal` property is defined both for `prove_temporal_by` and for `#liveness_check`, whether it is
declared before or after `#gen_spec`. Without `(only := …)`, a definition that fails to elaborate is
dropped with a warning. -/

veil module TemporalTargets

individual flag : Bool

#gen_state

after_init {
  flag := false
}

action raise {
  flag := true
}

ghost relation raised := flag = true

invariant true

-- Both definitions, generated once the spec is finalized
temporal [selfImplied] ⌜ raised ⌝ → ⌜ raised ⌝
-- `T(…)` has no proof definition, and `𝒲ℱ` no model-checking one
temporal [raiseRecurs] □ ◇ T(raise)
temporal [fairRaise] 𝒲ℱ raise → ◇ ⌜ raised ⌝

/--
warning: `fairRaise` is only proved, since its model-checking definition fails to elaborate (write `temporal (only := verify)` to say so):
  a model-checked property is built from the atoms `⌜ … ⌝`, `⌞ … ⌟`, `E(…)` and `T(…)` and the fairness conditions `WF(…)` and `SF(…)` with `⊤`, `⊥`, `¬`, `∧`, `∨`, `→`, `↔`, `□`, `◇`, `◯`, `𝑈`, `↝` and `⇒`; this formula is none of them
---
warning: `raiseRecurs` is only model checked, since its proof definition fails to elaborate (write `temporal (only := check)` to say so):
  `T(…)` only exists for model checking
-/
#guard_msgs in
#gen_spec

-- One property, both model checked and proved
/-- info: ✅ No liveness violation (checked 1 properties, explored 1 product states) -/
#guard_msgs in
#liveness_check [selfImplied] interpreted {}

prove_temporal_by [selfImplied]
  tstart hInit hNext hInv
  tdsimp only [selfImplied]
  tintro h
  tassumption

/-- error: `fairRaise` is not a model-checked temporal property of this module. Model checked: selfImplied, raiseRecurs -/
#guard_msgs in
#liveness_check [fairRaise] interpreted {}

end TemporalTargets

/-! A property that is only model checked does not need `Init`, `NextStep`, …, so declaring it leaves
their generation deferred under `veil.deferVCGeneration`. -/

set_option veil.deferVCGeneration true

veil module TemporalCheckOnlyDeferred

individual flag : Bool

#gen_state

after_init {
  flag := false
}

action raise {
  flag := true
}

invariant true

#gen_spec

temporal (only := check) [eventuallyRaised] ◇ ⌜ flag ⌝

run_meta do
  if (← Lean.getEnv).contains `TemporalCheckOnlyDeferred.NextStep then
    throwError "declaring a property that is only model checked generated the deferred `NextStep`"

end TemporalCheckOnlyDeferred
