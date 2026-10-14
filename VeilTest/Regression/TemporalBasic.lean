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

-- The action atoms only exist for model checking: without `only`, such a property is only model checked
/--
warning: `usesEnabledAtom` is only model checked, since its proof definition fails to elaborate (write `temporal (only := check)` to say so):
  `E(…)` only exists for model checking
-/
#guard_msgs in
temporal [usesEnabledAtom] □ E(tick)
/-- error: `T(…)` only exists for model checking -/
#guard_msgs in
temporal (only := verify) [usesTakenAtom] □ ◇ T(tick)

/-- error: Temporal property 'usesEnabledAtom' is only model checked, so it has nothing to prove -/
#guard_msgs in
prove_temporal_by [usesEnabledAtom] sorry

-- `warningAsError` turns the warning into an error; the property is still kept for model checking.
-- (Not `set_option … in`: the section it opens would drop the property from the module when it ends.)
set_option warningAsError true
/--
error: `takenAsError` is only model checked, since its proof definition fails to elaborate (write `temporal (only := check)` to say so):
  `T(…)` only exists for model checking
-/
#guard_msgs in
temporal [takenAsError] □ ◇ T(tick)
set_option warningAsError false

/-- error: Temporal property 'takenAsError' is only model checked, so it has nothing to prove -/
#guard_msgs in
prove_temporal_by [takenAsError] sorry

end TemporalBasic
