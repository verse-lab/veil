import Veil.DSL

open Classical

section Test

type node

relation r (n : node) (m : node)
individual x : Prop

#gen_state Test

#guard_msgs in
after_init {
  r N N := False
  x := False
}

#guard_msgs in
action empty = { }

#guard_msgs in
action call_empty = {
  empty
}

#guard_msgs in
action retval = {
  return 42
}

#guard_msgs in
action call_retval = {
  retval
}

#guard_msgs in
action with_if = {
  if (x) then
    r N M := False
}

#guard_msgs in
action call_with_if = {
  with_if
  x := False
}

#guard_msgs in
action with_if_fresh = {
  if (x) then
    let m ← fresh node
    r N m := False
}

#guard_msgs in
action call_with_if_fresh = {
  with_if_fresh
  x := False
}

#guard_msgs in
action with_if_fresh_more = {
  if (x) then
    let m ← fresh node
    r N m := False
    require x
}

#guard_msgs in
action call_with_if_fresh_more = {
  if x then
    with_if_fresh_more
  x := False
}

#guard_msgs in
action nested_call = {
  call_with_if_fresh_more
  x := False
}

#guard_msgs in
action callee_with_if_some = {
  if m : (r m m) then
    if n : (r n n ∧ n ≠ m) then
      r n m := True
      require x
      x := False
}

#guard_msgs in
action with_if_some_nested = {
  if m : (r m m) then
    if n : (r n n ∧ n ≠ m) then
      r n m := True
      callee_with_if_some
      require x
      x := False
      callee_with_if_some
}

end Test
