import Veil.DSL
import Test.TestUtil

set_option veil.smt.translator "lean-smt"

veil module Test
type node

relation r : node -> Nat -> Prop
individual n : node
function f : Nat -> Nat

set_option trace.veil.debug true

#gen_state

#check VeilM.require

-- set_option pp.all true

-- #guard_msgs(drop warning) in
action foo (k : Nat) =
  -- requires ∀ x, r x k
  -- ensures True
{
  let x <- pick node
  -- return x
  require r x k
}

#print foo.wpSucc_eq

#print foo.ext.wp_eq

#check foo.wp_eq

open PartialCorrectness DemonicChoice

example (P : _ -> Prop) (hd : ExId -> Prop) [IsHandler hd]
  [σ_substate : IsSubStateOf (State node) σ] [ρ_reader : IsSubStateOf (Reader node σ) ρ] :
  P ( Test.foo.ext.wpSucc (σ_substate := σ_substate) (ρ_reader := ρ_reader)) := by
  unfold Test.foo.ext.wpSucc
  simp [actSimp]



#print foo.ext.gen_wp


#guard_msgs(drop warning) in
action foo2 (k : Nat) = {
  let mut y := 0
  y := k
  if y > 0 then
    return True
  else return False
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``foo2

#guard_msgs(drop warning) in
action foo3 (k : Nat) = {
  let x <- pick node
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

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``foo3

#guard_msgs(drop warning) in
action foo4 (k : Nat) (m : node) = {
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
