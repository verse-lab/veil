import Veil.DSL

section Test

open Classical

type node

relation r : node -> Nat -> Prop
individual n : node
function f : Nat -> Nat

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
set_option linter.unusedVariables.analyzeTactics true

action foo3 (k : Nat) = {
  let x <- fresh node
  n := x
  let mut y := f 0
  let mut z := r x k
  y := f 4
  if r x k then
    r x k := True
    y := 0
  else
    y := f 1
  ensure ∀ N, f N = 0
  return y
}

-- #print foo3.fn

end Test
