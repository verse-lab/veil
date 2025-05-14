import Veil.DSL
import Test.TestUtil


set_option linter.unusedVariables false

veil module Test
type block
type node
type queue

individual x : Prop
immutable individual b : block
relation r : block -> block -> Prop
relation n_have_privilege : node → Prop

#gen_state

/--
error: Error in action Test.initializer: individual b in module Test was declared immutable, but trying to assign to it!
-/
#guard_msgs in
after_init {
  let b' ← fresh block
  b := b'
}

#guard_msgs in
action with_block (b : block) = {
  let b' ← fresh block
  return (b, b')
}

#guard_msgs in
action test = {
  let mut (z, y) := (5, 7)
}

/--
error: Error in action Test.try_assign_immutable: individual b in module Test was declared immutable, but trying to assign to it!
-/
#guard_msgs in
action try_assign_immutable = {
  let b' ← fresh block
  b := b'
}

#guard_msgs in
action double_bind (r : Int) = {
    let (bb, b') ← with_block b
 }

#guard_msgs in
action state_acess_if = {
  if x then
    return True
  else
    return False
}

#guard_msgs in
action state_access_if_prop (n : node) = {
  if ¬ (n_have_privilege n) then
    return True
  else
    return False
}
