import Veil

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
