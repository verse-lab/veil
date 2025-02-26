import Veil.DSL
import Test.TestUtil


set_option linter.unusedVariables false

veil module Test
type block
type node
type queue

individual x : Prop
individual b : block
relation r : block -> block -> Prop
relation n_have_privilege : node → Prop

#gen_state

action with_block (b : block) = {
  let b' ← fresh block
  return (b, b')
}

action test = {
  let mut (z, y) := (5, 7)
}

-- FIXME Vova: this is a BROKEN test
-- #guard_msgs(drop error) in
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
