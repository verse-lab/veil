/-
Correct behavior:
the structural restrictions checked by `validateVeilDo` should also hold for
syntax produced by do-element macros.  In particular, a macro should not be
able to introduce a stored term-level `do` block or an effectful state-update
index.  The custom havoc syntax must be checked under the same rule as ordinary
`:=` and `←` assignments.

Before the protocol fix, validation ran only before do-element macro expansion,
and `assignmentTarget?` did not recognize havoc.  The guards below record that
both direct and macro-generated forms are now rejected.
-/

import Veil

open Lean Parser Term

macro "hidden_term_do" : doElem =>
  `(doElem| let _deferred : Id Unit := do pure ())

macro "hidden_effectful_target" : doElem =>
  `(doElem| r (← pure true) := true)

veil module ExtensibleDoValidationBypass

relation r : Bool → Bool

#gen_state

section DirectForms

/--
error: Error in action direct_term_do_is_rejected: term-level `do` blocks cannot be stored, passed, or otherwise deferred inside Veil actions
-/
#guard_msgs (substring := true) in
action direct_term_do_is_rejected {
  let _deferred : Id Unit := do pure ()
}

/--
error: Error in action direct_effectful_target_is_rejected: effects are not supported in state-update target indices
-/
#guard_msgs (substring := true) in
action direct_effectful_target_is_rejected {
  r (← pure true) := true
}

end DirectForms

section HavocTarget

/--
error: Error in action effectful_havoc_target_is_rejected: effects are not supported in state-update target indices
-/
#guard_msgs in
action effectful_havoc_target_is_rejected {
  r (← pick Bool) := *
}

end HavocTarget

section MacroGeneratedForms

/--
error: Error in action rejects_hidden_term_do: term-level `do` blocks cannot be stored, passed, or otherwise deferred inside Veil actions; execute the block directly as a statement or bind its result
-/
#guard_msgs in
action rejects_hidden_term_do {
  hidden_term_do
}

/--
error: Error in action rejects_hidden_effect_in_target: effects are not supported in state-update target indices
-/
#guard_msgs in
action rejects_hidden_effect_in_target {
  hidden_effectful_target
}

end MacroGeneratedForms

end ExtensibleDoValidationBypass
