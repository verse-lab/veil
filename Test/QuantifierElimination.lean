import Veil.DSL



veil module Test

type node

relation r (n : node) (m : node)
individual x : Prop

#gen_state

#guard_msgs in
after_init {
  r N N := False
  x := False
}

#guard_msgs in
action empty = { pure () }

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
    pure ()
    -- r N M := False
}

#guard_msgs in
action call_with_if = {
  with_if
  -- x := False
}

#guard_msgs in
action with_if_pick = {
  if (x) then
    let m ← pick node
    r N m := False
}

#guard_msgs in
action ff = {
  with_if_pick
  -- x := False
}

#guard_msgs in
action with_if_pick_more = {
  if (x) then
    let m ← pick node
    r N m := False
    require x
}

#guard_msgs in
action call_with_if_pick_more = {
  if x then
    with_if_pick_more
  -- x := False
}

#guard_msgs in
action nested_call = {
  call_with_if_pick_more
  -- x := False
}

#guard_msgs in
action callee_with_if_some = {
  if m : (r m m) then
    if n : (r n n ∧ n ≠ m) then
      -- r n m := True
      require x
      -- x := False
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

#guard_msgs in
action nondet_assgn (m : node) = {
  if x then
    r N m := *
    x := *
}

#guard_msgs in
action call_nondet_assgn = {
  let m ← pick node;
  if x then
      nondet_assgn m;
  else
    r N M := *;
}

#guard_msgs in
action call_nondet_assgn' = {
  let m ← pick node;
  if x then
    nondet_assgn m;
    call_nondet_assgn
  else
    let n ← pick node;
    nondet_assgn n
    r N M := *;
}

end Test
