import Veil.DSL

section Test

open Classical

type node

relation r : node -> Nat -> Prop
individual n : node

#gen_state Test


action foo (k : Nat) = {
  let x <- fresh node
  require r x k
}

action foo2 (k : Nat) = {
  let mut y := 0
  y := k
  if y > 0 then
    return true
  else return false
  -- r N k := True
}

action foo3 (k : Nat) = {
  let x <- fresh node
  n := x
  let mut y := 0
  if r x k then
    r x k := True
    y := 0
  else
    y := 1
  return y
}


end Test
