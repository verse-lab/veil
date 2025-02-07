import Veil.DSL
import Test.TestUtil

open Classical
set_option linter.unusedVariables false

namespace Test
type block
type queue

individual x : Prop
relation r : block -> block -> Prop

#gen_state

#guard_msgs in
action fresh_with_type = {
  let b ← fresh block
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``fresh_with_type

#guard_msgs in
action fresh_with_lhs_type = {
  let b : block ← fresh
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``fresh_with_lhs_type

#guard_msgs in
action fresh_with_lhs_type_ok = {
  let b : block ← (fresh)
  let q : queue ← fresh
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``fresh_with_lhs_type_ok

#guard_msgs in
action fresh_with_lhs_type_2 = {
  let b : block ← fresh
  let q : queue ← fresh
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``fresh_with_lhs_type_2
