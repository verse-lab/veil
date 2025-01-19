import Veil.DSL
import Veil.TestUtil

open Classical
set_option linter.unusedVariables false

namespace Test
type block
type queue

individual x : Prop

#gen_state

after_init {
  x := True
}

invariant True

#gen_spec

#guard_msgs(drop warning) in
sat trace [ini] { } by { bmc_sat }
