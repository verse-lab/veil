import Veil

set_option linter.unusedVariables false

veil module FirstModule

type node

relation leader : node -> Bool
relation pending : node -> node -> Bool

#gen_state

after_init {
  leader N := false
  pending M N := false
}

action send (n next : node) {
  pending n next := true
}

safety [single_leader] leader N ∧ leader M → N = M

#gen_spec

end FirstModule


veil module SecondModule

type node

relation leader : node -> Bool
relation pending : node -> node -> Bool

#gen_state

after_init {
  leader N := false
  pending M N := false
}

action send (n next : node) {
  pending n next := true
}

safety [single_leader] leader N ∧ leader M → N = M

#gen_spec

end SecondModule
