import Veil

/-!
# Regression: state binders are refreshed after calls in `pick` and `veil_var` types

Although `pick` itself does not modify state, its type can contain a lifted
computation. In each action below, `set_x_return_nat` runs while computing the
type `Fin 1`, so the following `y := x` must observe its write to `x`.

This covers untyped and explicitly typed `pick` binders, plus `veil_var`, which
generates a `pick` binder internally.
-/

set_option linter.unusedVariables false
set_option veil.smt.trust false
set_option veil.printCounterexamples false

veil module StateRefreshAfterPickTypeCall

individual x : Bool
individual y : Bool

#gen_state

after_init {
  x := false
  y := false
}

procedure set_x_return_nat {
  x := true
  return 1
}

action pick_type {
  let b ← pick (Fin (← set_x_return_nat))
  y := x
}

action typed_pick {
  let b : Fin (← set_x_return_nat) ← pick
  y := x
}

action veil_var_type {
  veil_var b : Fin (← set_x_return_nat)
  y := x
}

invariant [xy] x = y

#guard_msgs(drop warning) in
#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  xy ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  typed_pick
    doesNotThrow ... ✅
    xy ... ✅
  pick_type
    doesNotThrow ... ✅
    xy ... ✅
  veil_var_type
    doesNotThrow ... ✅
    xy ... ✅
-/
#guard_msgs(info, drop warning) in
#check_invariants

end StateRefreshAfterPickTypeCall
