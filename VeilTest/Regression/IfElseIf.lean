module

public import Veil

veil module TestIfElseIf

relation r : Nat → Nat → Bool

/--
warning: Field `r` uses a hybrid representation. Updates over potentially unbounded domains (e.g. `f I := ...`) can switch it to the canonical case, where default `Hashable` or `BEq` instances can merge distinct states and miss reachable states during model checking. For meaningful hashing and equality in the canonical case, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation; see `docs/DSL-Reference.md#hybrid-field-representations`. If the field stays concrete, suppress this warning with `set_option veil.warnHybridFields false`. Alternatively, consider `TMap` if it better fits your model.
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
