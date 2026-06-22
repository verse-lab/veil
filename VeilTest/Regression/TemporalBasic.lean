import Veil
import Veil.Liveness

open TLA

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
temporal [top] (⊤)

end TemporalBasic
