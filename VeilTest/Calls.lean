import Veil
import VeilTest.TestUtil


veil module Test

type node

relation r (n : node) (m : node)
individual x : Bool

#gen_state

after_init {
  r N M := false
  x := false
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``Test.initializer

#guard_msgs in
action empty {
  pure ()
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``empty

#guard_msgs in
action call_empty {
  empty
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``call_empty

#guard_msgs(drop warning) in
action f (n : Nat) (x : node) {
  return x
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``f

#guard_msgs(drop warning) in
action call_f (z : node) {
  f 5 z
}

#guard_msgs(drop warning) in
action foo (z : node) {
  let _qq ← f 5 z;
  pure 42
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``call_f

#guard_msgs(drop warning) in
action nested_call (n : node ) {
  call_f n
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``nested_call

end Test
