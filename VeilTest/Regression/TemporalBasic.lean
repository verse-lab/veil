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

-- The action atoms of model-checked properties are rejected
/--
error: `E(…)` is an atom of `liveness` properties, which are model checked; a `temporal` property cannot use it
-/
#guard_msgs in
temporal [usesEnabledAtom] □ E(tick)
/--
error: `T(…)` is an atom of `liveness` properties, which are model checked; a `temporal` property cannot use it
-/
#guard_msgs in
temporal [usesTakenAtom] □ ◇ T(tick)

end TemporalBasic
