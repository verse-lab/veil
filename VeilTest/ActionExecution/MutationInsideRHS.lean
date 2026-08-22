import VeilTest.ActionExecution

/-! Regression coverage for Veil's extensible-`do` protocol integration. -/

open Lean Parser Term
open VeilTest.ActionExecution

veil module MutationInsideRHS

relation r : Bool → Bool

veil_set_field_representation relation Veil.CanonicalField

#gen_state

/- The wrapper's control-info handler must propagate the reassignment of `x`
from the arrow RHS through the surrounding `if` join point. -/
action arrow_rhs_control_info {
  let mut x := false
  if true then
    r true ← do
      x := true
      pure true
  else
    pure ()
  return x
}

def initial : State FieldConcreteType := {
  r := fun _ => false
}

#guard exactlyOneSuccess (__veil_exec_action% {} {} initial arrow_rhs_control_info)
  fun value _ => value

end MutationInsideRHS
