module

public import Veil
import all Veil.Frontend.DSL.Module.Util.ExecutionWorkflow

-- In a module file this ordinary declaration is private. Checking only the
-- exported name `main` misses it and attempts to generate a conflicting entry.
def main : IO Unit := pure ()

veil module ExecutionWorkflowMain
individual flag : Bool
after_init { flag := false }
action toggle { flag := !flag }
invariant true
#gen_spec

/-- error: Cannot compile #model_check: the file already declares `main`, which the generated binary needs as its entry point. Move the `main` declaration into another file, or use `#model_check interpreted`. -/
#guard_msgs in
#model_check compiled {} {} (sequential := true)

/-- error: Cannot compile #simulate: the file already declares `main`, which the generated binary needs as its entry point. Move the `main` declaration into another file, or use `#simulate interpreted`. -/
#guard_msgs in
#simulate compiled {} {} (seed := 1) (numTraces := 1) (maxSteps := 1)

-- The conflict affects only native entry points; interpreted checks still run.
/-- info: ✅ No violation (explored 2 states) -/
#guard_msgs in
#model_check interpreted {} {} (sequential := true)

end ExecutionWorkflowMain

-- Exercise both exporting modes explicitly: a Veil namespace normally exports
-- its generated declarations, but that must not hide the user's private main.
open Lean Elab Command Veil in
#guard_msgs in
run_cmd do
  for exporting in [false, true] do
    withExporting (isExporting := exporting) do
      let failed ← try
        discard <| ExecutionWorkflow.generateCCode { name := "simulate" } (← `(pure))
        -- Never reaches here
        pure false
      catch e =>
        let message ← e.toMessageData.toString
        pure <| (message.splitOn "the file already declares `main`").length > 1
      unless failed do
        throwError "a private main must be diagnosed even when exporting = {exporting}"
