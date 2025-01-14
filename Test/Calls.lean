import Veil.DSL
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

#guard_msgs in
action empty = {

}

#guard_msgs in
action call_empty = {
  empty
}

#guard_msgs(drop warning) in
action f (n : Nat) (x : node) = {
  return x
}

#guard_msgs(drop warning) in
action call_f (x : node) = {
  f 5 x
}

#guard_msgs(drop warning) in
action nested_call (n : node ) = {
  call_f n
}

end Test
