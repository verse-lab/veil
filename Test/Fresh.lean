import Veil.DSL
import Test.TestUtil


set_option linter.unusedVariables false

veil module Test
type block
type queue

individual x : Prop
relation r : block -> block -> Prop

#gen_state

#guard_msgs in
action pick_with_type = {
  let b ← pick block
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``pick_with_type

#guard_msgs in
action pick_with_lhs_type = {
  let b : block ← pick
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``pick_with_lhs_type

#guard_msgs in
action pick_with_lhs_type_ok = {
  let b : block ← (pick)
  let q : queue ← pick
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``pick_with_lhs_type_ok

#guard_msgs in
action pick_with_lhs_type_2 = {
  let b : block ← pick
  let q : queue ← pick
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``pick_with_lhs_type_2
