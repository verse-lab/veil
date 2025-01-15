import Veil.DSL
import Veil.TestUtil
open Classical

section Test

type node

relation r (n : node) (m : node)
individual x : Prop

#gen_state Test

after_init {
  r N M := False
  x := False
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``Test.initialState?

#guard_msgs in
action empty = {

}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``empty

#guard_msgs in
action call_empty = {
  empty
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``call_empty

#guard_msgs(drop warning) in
action f (n : Nat) (x : node) = {
  return x
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``f

#guard_msgs(drop warning) in
action call_f (x : node) = {
  f 5 x
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``call_f

#guard_msgs(drop warning) in
action nested_call (n : node ) = {
  call_f n
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``nested_call

end Test
