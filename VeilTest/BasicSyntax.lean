import Veil
import VeilTest.TestUtil


veil module Test
type node

abbrev Nat3 := Fin 3

relation r : node -> Nat3 -> Bool
individual n : node
function f : Nat3 -> Nat3

#gen_state

action foo (k : Nat3)
{
  let x <- pick node
  -- return x
  require r x k
  n := x
}

#guard_msgs(drop warning) in
action foo2 (k : Nat3) {
  -- y := k
  if k > 0 then
    return True
  else return False
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``foo2

#guard_msgs(drop warning) in
action foo3 (k : Nat3) {
  let x <- pick node
  n := x
  let mut y := f 0 = 7
  let mut z := r x k
  y := f 4 > 3
  if r x k then
    r x k := true
    y <- foo2 (f k)
  else
    y := f 1 < 5
  return y
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``foo3

#guard_msgs(drop warning) in
action foo4 (k : Nat3) (m : node) {
  let mut y := m
  if x : r x k then
    y := x
  else y := y
  return y
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``foo4

end Test
