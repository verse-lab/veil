module

public import Veil

-- The proof command also forces deferred VC generation.
set_option veil.deferVCGeneration true
veil module ProveInvariantGoalDeferred
individual flag : Bool
after_init { flag := false }
action keep { pure () }
invariant [excluded] flag = flag
#gen_spec

run_cmd do
  unless (← Veil.getCurrentModule)._vcGenerationDeferred do
    throwError "expected deferred VC generation"

prove_veil_invariant_goal keep excluded using wp by
  done

run_cmd do
  if (← Veil.getCurrentModule)._vcGenerationDeferred then
    throwError "the proof command did not generate the deferred VCs"

/-- error: unknown action or initializer `missing` -/
#guard_msgs in
prove_veil_invariant_goal missing excluded using wp by
  done

/-- error: unknown invariant `missing` -/
#guard_msgs in
prove_veil_invariant_goal keep missing using wp by
  done

-- Invalid styles are rejected by the parser, before elaboration.
open Lean in
run_cmd do
  match Parser.runParserCategory (← getEnv) `command
      "prove_veil_invariant_goal keep excluded using other by done" with
  | .error _ => pure ()
  | .ok _ => throwError "the parser accepted an invalid VC style"

-- The mode tokens remain usable as ordinary identifiers.
example (wp tr : Nat) : wp + tr = wp + tr := rfl

/-- error: `doesNotThrow` only supports `using wp` -/
#guard_msgs in
prove_veil_invariant_goal keep doesNotThrow using tr by
  done

end ProveInvariantGoalDeferred
