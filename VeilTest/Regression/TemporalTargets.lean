module

public import Veil

open Lentil

/-! A `temporal` property is defined both for `prove_temporal_by` and for `#temporal_check`, whether it is
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
temporal [raiseRecurs] □ ◇ ⟨raise⟩
temporal [fairRaise] 𝒲ℱ raise → ◇ ⌜ raised ⌝
-- A step relation that is not one of the module's actions has no model-checking definition
temporal [anyChange] □ ◇ ⟨ fun s s' => s ≠ s' ⟩

/--
warning: `anyChange` is only proved, since its model-checking definition fails to elaborate (write `temporal (only := verify)` to say so):
  expected an action of this module, applied to arguments or not; the module's actions are [raise]
-/
#guard_msgs in
#gen_spec

-- One property, both model checked and proved
/-- info: ✅ No liveness violation (checked 1 properties, explored 1 product states) -/
#guard_msgs in
#temporal_check [selfImplied] interpreted {}

prove_temporal_by [selfImplied]
  tintro h
  tassumption

/-- info: ✅ No liveness violation (checked 2 properties, explored 2 product states) -/
#guard_msgs in
#temporal_check [raiseRecurs] [fairRaise] interpreted {}

/-- error: `anyChange` is not a model-checked temporal property of this module. Model checked: selfImplied, raiseRecurs, fairRaise -/
#guard_msgs in
#temporal_check [anyChange] interpreted {}

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
