import Veil.DSL
import Test.TestUtil

open Classical
set_option linter.unusedVariables.analyzeTactics true
set_option veil.smt.translator "lean-smt"

namespace Test
type node

relation r : node -> Nat -> Prop
individual n : node
function f : Nat -> Nat

#gen_state

-- FIXME BROKEN test: we want this to throw an error, but don't really care
-- what it is
#guard_msgs(drop all) in
action foo = {
  foo
}
