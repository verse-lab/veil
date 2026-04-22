import Veil

/--
error: Custom solver is not specified
⊢ False
-/
#guard_msgs in
example : False := by
  set_option veil.solver "custom" in
  veil_solver

/--
error: Custom solver is not specified
⊢ False
-/
#guard_msgs in
example : False := by
  set_option veil.solver "custom" in
  veil_smt

macro_rules
  | `(tactic| veil_solver) => `(tactic| grind)

example : True := by
  set_option veil.solver "custom" in
  veil_solver

example : True := by
  set_option veil.solver "custom" in
  veil_smt
