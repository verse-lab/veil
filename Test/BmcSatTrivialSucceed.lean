import Veil.DSL
import Test.TestUtil


set_option linter.unusedVariables false

veil module Test
type block
type queue

individual x : Prop

#gen_state

after_init {
  x := True
}

action empty = {
  pure ()
}

invariant True

#gen_spec

#guard_msgs(drop info, drop warning) in
sat trace [ini] { } by { bmc_sat }
