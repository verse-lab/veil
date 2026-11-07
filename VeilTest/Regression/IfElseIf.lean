module

public import Veil

veil module TestIfElseIf

relation r : Nat → Nat → Bool

/--
warning: Field `r` uses a hybrid representation with default canonical `Hashable` or `BEq` instances, which can cause model checking to merge distinct states and miss reachable states. For meaningful hashing and equality, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation.
-/
#guard_msgs in
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
