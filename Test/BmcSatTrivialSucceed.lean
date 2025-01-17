import Veil.DSL
import Veil.TestUtil

open Classical
set_option linter.unusedVariables false

section Test
type block
type queue

individual x : Prop

#gen_state Test

after_init {
  x := True
}

invariant True

#gen_spec Test

#guard_msgs(drop warning) in
sat trace [init] { } by { bmc_sat }
