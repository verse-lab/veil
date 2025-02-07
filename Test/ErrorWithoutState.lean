import Veil.DSL
import Test.TestUtil

open Classical

namespace Test

individual x : Prop

/-- error: State has not been declared so far: run `#gen_state [name]` -/
#guard_msgs in
after_init { pure () }

/-- error: State has not been declared so far: run `#gen_state [name]` -/
#guard_msgs in
action foo = { pure () }

/-- error: State has not been declared so far: run `#gen_state [name]` -/
#guard_msgs in
invariant [inv] True

/-- error: State has not been declared so far: run `#gen_state [name]` -/
#guard_msgs in
#gen_spec

/-- error: State has not been declared so far: run `#gen_state [name]` -/
#guard_msgs in
#check_invariants

/-- error: State has not been declared so far: run `#gen_state [name]` -/
#guard_msgs in
#check_invariants?

/-- error: State has not been declared so far: run `#gen_state [name]` -/
#guard_msgs in
#check_invariant inv

/-- error: State has not been declared so far: run `#gen_state [name]` -/
#guard_msgs in
#check_action foo

/-- error: State has not been declared so far: run `#gen_state [name]` -/
#guard_msgs in
sat trace { } by { bmc_sat }

/-- error: State has not been declared so far: run `#gen_state [name]` -/
#guard_msgs in
unsat trace { } by { bmc }

end Test
