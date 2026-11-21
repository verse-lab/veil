module

public import Veil

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

example : True := by
  set_option veil.smt.trust true in
  veil_smt

-- Registration order applies to every generated VC, including alternatives,
-- even when the primary uses a custom solver.
veil module GrindFallback

individual x : Nat
after_init { x := 0 }
action step { x := 0 }
transition keep { x' = x }
invariant [zero] x = 0

set_option veil.solver "custom"
#gen_spec

open Lean in
run_cmd do
  let mgr ← Veil.Verifier.readVCManager
  for name in [`step_zero, `step_zero_tr, `step_doesNotThrow, `keep_zero_tr, `keep_zero] do
    unless mgr.nodes.valuesArray.any (·.name == name) do throwError "missing VC {name}"
  for vc in mgr.nodes.valuesArray do
    unless vc.dischargers.size == 2 && vc.dischargers[1]?.any (·.id.name.toString.endsWith "_GRIND") do
      throwError "missing grind fallback for {vc.name}"

end GrindFallback

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
