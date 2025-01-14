import Veil.DSL

section Test

open Classical

type node

relation r : node -> Nat -> Prop
individual n : node
function f : Nat -> Nat

#gen_state Test

set_option linter.unusedVariables.analyzeTactics true


action foo (k : Nat) = {
  let x <- fresh node
  require r x k
}

action foo2 (k : Nat) = {
  let mut y := 0
  y := k
  if y > 0 then
    return True
  else return False
}


action foo3 (k : Nat) = {
  let x <- fresh node
  n := x
  let mut y := f 0 = 7
  let mut z := r x k
  y := f 4 > 3
  if r x k then
    r x k := True
    y <- foo2 (f k)
  else
    y := f 1 < 5
  return y
}

action foo4 (k : Nat) (m : node) = {
  let mut y := m
  if x : r x k then
    y := x
  else y := y
  return y
}

end Test
