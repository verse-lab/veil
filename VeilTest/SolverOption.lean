import Veil

-- This test intentionally uses SMT proofs for trivial `True` goals below.
-- Suppress the trusted-SMT proof warning so the expected messages stay focused
-- on the solver-option behavior.
set_option warn.sorry false

-- `veil.solver` configures `veil_solve`. With `custom`, `veil_solve` should
-- fail until the user provides a `veil_solve` macro.
/--
error: Custom solver is not specified
⊢ False
-/
#guard_msgs in
example : False := by
  set_option veil.solver "custom" in
  veil_solve

-- `veil_smt` always calls the SMT backend directly. It should ignore
-- `veil.solver`, even when the option is set to `custom`.
example : True := by
  set_option veil.solver "custom" in
  veil_smt

macro_rules
  | `(tactic| veil_solve) => `(tactic| grind)

-- The custom macro above only affects `veil_solve`; `veil_smt` remains direct
-- SMT.
example : True := by
  set_option veil.solver "custom" in
  veil_smt

-- Once the custom `veil_solve` macro exists, the configurable solver entry
-- point should use it.
example : True := by
  set_option veil.solver "custom" in
  veil_solve
