module

public import Veil
public import Veil.Liveness

open Lentil

veil module TemporalBasic

immutable individual limit : Nat
individual counter : Nat
relation seen (n : Nat)

#gen_state

after_init {
  counter := limit
}

action tick {
  counter := counter + 1
}

safety [counterRefl] counter = counter

ghost relation atLimit := counter = limit

#gen_spec

temporal [usesTheoryArg] ⌞ limit = limit ⌟ ∧ ◇ ⌜ atLimit ⌝
temporal [usesMutableRelationField] ◇ ⌜ seen limit ⌝
temporal [usesMutableIndividualField] ◇ ⌜ counter = limit ⌝
temporal [top] (⊤)

-- The action atoms exist for both proving and model checking
#guard_msgs in
temporal [usesEnabledAtom] □ Enabled tick
#guard_msgs in
temporal [usesTakenAtom] □ ◇ ⟨tick⟩

-- A step relation that is not one of the module's actions only exists for proving: without `only`, such a
-- property is only proved
/--
warning: `usesRelation` is only proved, since its model-checking definition fails to elaborate (write `temporal (only := verify)` to say so):
  expected an action of this module, applied to arguments or not; the module's actions are [tick]
-/
#guard_msgs in
temporal [usesRelation] □ ◇ ⟨ fun s s' => s ≠ s' ⟩
/-- error: expected an action of this module, applied to arguments or not; the module's actions are [tick] -/
#guard_msgs in
temporal (only := check) [checksRelation] □ ◇ ⟨ fun s s' => s ≠ s' ⟩

temporal (only := check) [checkOnly] □ ◇ ⟨tick⟩
/-- error: Temporal property 'checkOnly' is only model checked, so it has nothing to prove -/
#guard_msgs in
prove_temporal_by [checkOnly] sorry

-- `warningAsError` turns the warning into an error; the property is still kept for proving.
-- (Not `set_option … in`: the section it opens would drop the property from the module when it ends.)
set_option warningAsError true
/--
error: `relationAsError` is only proved, since its model-checking definition fails to elaborate (write `temporal (only := verify)` to say so):
  expected an action of this module, applied to arguments or not; the module's actions are [tick]
-/
#guard_msgs in
temporal [relationAsError] □ ◇ ⟨ fun s s' => s ≠ s' ⟩
set_option warningAsError false

/-- warning: declaration uses `sorry` -/
#guard_msgs in
prove_temporal_by [relationAsError] sorry

-- The prelude also comes before a bracketed proof
temporal (only := verify) [bracketedProof] ⌜ counter = limit ⌝ → ⌜ counter = limit ⌝
prove_temporal_by [bracketedProof] { tintro h; tassumption }

end TemporalBasic
