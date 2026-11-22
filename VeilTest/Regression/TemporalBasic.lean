module

public import Veil

open Lentil

veil module TemporalBasic

immutable individual limit : Nat
individual counter : Nat
relation seen (n : Nat)

/--
warning: Field `seen` uses a hybrid representation. Updates over potentially unbounded domains (e.g. `f I := ...`) can switch it to the canonical case, where default `Hashable` or `BEq` instances can merge distinct states and miss reachable states during model checking. For meaningful hashing and equality in the canonical case, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation; see `docs/DSL-Reference.md#hybrid-field-representations`. If the field stays concrete, suppress this warning with `set_option veil.warnHybridFields false`. Alternatively, consider `TMap` if it better fits your model.
-/
#guard_msgs in
#gen_state

after_init {
  counter := limit
}

action tick {
  counter := counter + 1
}

safety [counterRefl] counter = counter

ghost relation atLimit := counter = limit

temporal [usesTheoryArg] ⌞ limit = limit ⌟ ∧ ◇ ⌜ atLimit ⌝
temporal [usesMutableRelationField] ◇ ⌜ seen limit ⌝
temporal [usesMutableIndividualField] ◇ ⌜ counter = limit ⌝
temporal [top] (⊤)

-- The action atoms exist for both proving and model checking.
temporal [usesEnabledAtom] □ Enabled tick
temporal [usesTakenAtom] □ ◇ ⟨tick⟩

-- A step relation outside the module's actions can be used in a proof.
temporal [usesRelation] □ ◇ ⟨ fun s s' => s ≠ s' ⟩
temporal (only := check) [checksRelation] □ ◇ ⟨ fun s s' => s ≠ s' ⟩
temporal (only := check) [checkOnly] □ ◇ ⟨tick⟩
temporal (only := verify) [bracketedProof] ⌜ counter = limit ⌝ → ⌜ counter = limit ⌝

/--
warning: `usesRelation` is only proved, since its model-checking definition fails to elaborate (write `temporal (only := verify)` to say so):
  expected an action of this module, applied to arguments or not; the module's actions are [tick]
---
error: expected an action of this module, applied to arguments or not; the module's actions are [tick]
-/
#guard_msgs in
#gen_spec

/-- error: Temporal property 'checkOnly' is only model checked, so it has nothing to prove -/
#guard_msgs in
prove_temporal_by [checkOnly] sorry

-- The prelude also comes before a bracketed proof.
prove_temporal_by [bracketedProof] { tintro h; tassumption }

end TemporalBasic

veil module TemporalWarningAsError

individual counter : Nat

after_init { counter := 0 }
action tick { counter := counter + 1 }

temporal [relationAsError] □ ◇ ⟨ fun s s' => s ≠ s' ⟩

-- `warningAsError` turns the warning into an error. The property is still kept for proving.
set_option warningAsError true
/--
error: `relationAsError` is only proved, since its model-checking definition fails to elaborate (write `temporal (only := verify)` to say so):
  expected an action of this module, applied to arguments or not; the module's actions are [tick]
-/
#guard_msgs in
#gen_spec
set_option warningAsError false

/-- warning: declaration uses `sorry` -/
#guard_msgs in
prove_temporal_by [relationAsError] sorry

end TemporalWarningAsError
