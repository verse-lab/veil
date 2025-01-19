import Veil.DSL
import Veil.TestUtil

open Classical
set_option linter.unusedVariables.analyzeTactics true
set_option sauto.smt.translator "lean-smt"

namespace Test
type node

relation r : node -> Nat -> Prop
individual n : node
function f : Nat -> Nat

#gen_state

#guard_msgs(drop warning) in
action foo (k : Nat) =
  requires ∀ x, r x k
  ensures True
{
  let x <- fresh node
  require r x k
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``foo

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``foo.spec_correct

#guard_msgs(drop warning) in
action bar =
  requires True
  ensures True
{
  require n = n
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``bar

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``bar.spec_correct


end Test
