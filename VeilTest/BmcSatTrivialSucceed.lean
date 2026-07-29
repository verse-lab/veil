import Veil

set_option linter.unusedVariables false

veil module Test
type block

-- Don't change this from `Bool`. We used to have a bug where individuals of type
-- `Bool` would have issues deriving `ToJson` in `#gen_state`
individual x : Bool

#gen_state

after_init {
  x := true
}

action empty {
  pure ()
}

invariant true

#gen_spec

#guard_msgs(drop warning, drop info) in
sat trace [ini] { }
