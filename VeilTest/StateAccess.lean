import Veil

set_option linter.unusedVariables false

veil module Test
type block
type node
type queue

individual x : Bool
immutable individual b : block
relation r : block → block → Bool
relation n_have_privilege : node → Bool

#gen_state

/--
error: Error in action initializer: individual b in module Test was declared immutable, but trying to assign to it!
-/
#guard_msgs in
after_init {
  let b' ← pick block
  b := b'
}

/--
warning: parameter `b` shadows immutable theory component `b`; references to this name resolve to the parameter
-/
#guard_msgs(warning) in
action with_block (b : block) {
  let b' ← pick block
  return (b, b')
}

#guard_msgs in
action test {
  let mut (z, y) := (5, 7)
}

/--
error: Error in action try_assign_immutable: individual b in module Test was declared immutable, but trying to assign to it!
-/
#guard_msgs in
action try_assign_immutable {
  let b' ← pick block
  b := b'
}

/--
error: individual b in module Test was declared immutable, but the transition might modify it (since it mentions its primed version b')!
-/
#guard_msgs in
transition try_assign_immutable' (x : block) {
    b' = x
}

action double_bind (rr : Int) {
    let (bb, b') ← with_block b
 }

#guard_msgs in
action state_acess_if {
  if x then
    return true
  else
    return false
}

#guard_msgs in
action state_access_if_prop (n : node) {
  if ¬ (n_have_privilege n) then
    return true
  else
    return false
}
