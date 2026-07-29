import Veil

veil module TestIfElseIf

relation r : Nat → Nat → Bool

#gen_state

action act (b : Nat) (c : Nat) {
  if b > c then
    r b b := true
  else
     if b < c then
      r c c := true
}

action actWithElseIf (b : Nat) (c : Nat) {
  if b > c then
    r b b := true
  else if b < c then
    r c c := true
}

#check (rfl : @act = @actWithElseIf)

action actChain (a : Nat) (b : Nat) (c : Nat) {
  if a > b then
    r a a := true
  else if a < b then
    r b b := true
  else if b < c then
    r c c := true
}

end TestIfElseIf
