import Veil.DSL
import Test.TestUtil


set_option linter.unusedVariables.analyzeTactics true
set_option veil.smt.translator "lean-smt"

veil module Test
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
  let x <- pick node
  require r x k
}

#guard_msgs(drop warning) in
procedure foobar (k : Nat) =
  requires ∀ x, r x k
  ensures True
{
  let x <- pick node
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
