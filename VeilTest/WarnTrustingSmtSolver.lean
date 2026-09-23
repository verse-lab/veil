module

public import Veil

set_option warn.sorry false
set_option veil.smt.trust true

veil module WarnTrustingSmtSolver

type node

relation r : node -> Bool

#gen_state

after_init {
  r N := false
}

action keep {
  pure ()
}

invariant [r_excluded] r N ∨ ¬ r N

#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  r_excluded ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  keep
    doesNotThrow ... ✅
    r_excluded ... ✅
---
warning: Trusting SMT solver for 2 goals. `set_option veil.smt.trust false` to enable proof reconstruction.
-/
#guard_msgs in
#check_invariants
#gen_theorems

-- Publication and the WP/TR bridge must preserve the solver's trust provenance.
run_cmd do
  for name in #[`WarnTrustingSmtSolver.keep_r_excluded, `WarnTrustingSmtSolver.keep_r_excluded_tr,
      `WarnTrustingSmtSolver.Invariants.is_inv, `WarnTrustingSmtSolver.r_excluded.is_inv] do
    unless (← Lean.collectAxioms name).contains ``sorryAx do
      throwError "expected trusted SMT proof to retain sorryAx: {name}"

/--
info: The following set of actions must preserve the invariant and successfully terminate:
  keep
    doesNotThrow ... ✅
    r_excluded ... ✅
---
warning: Trusting SMT solver for 1 goal. `set_option veil.smt.trust false` to enable proof reconstruction.
-/
#guard_msgs in
#check_action keep

end WarnTrustingSmtSolver
