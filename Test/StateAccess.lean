import Veil.DSL
import Veil.TestUtil

open Classical
set_option linter.unusedVariables false

section Test
type block
type queue

individual x : Prop
individual b : block
relation r : block -> block -> Prop

#gen_state Test

action with_block (b : block) = {
  let b' ← fresh block
  return (b, b')
}

action test = {
  let mut (x, y) := (5, 7)
}

-- #guard_msgs in
-- action double_bind (r : Int) = {
--     let (b, b') ← with_block b
--  }
