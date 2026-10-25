module

public import Veil

/-!
`veil.modelChecker.buildOnly` (used by `scripts/bench-model-check.py`): `#model_check` builds its
checker binary but does not run it. As for `#model_check X …` for a module `X`, the binary is copied
out of its build folder to `.lake/model_checkers`, and a `VEIL_BUILD_ONLY` line holding a JSON object
reports the copy, the build folder and the phases of the build. The paths and the times in that
line vary, so the test elaborates the command itself and inspects the message it logged.
-/

veil module BuildOnly

type node
relation active : node → Bool

#gen_state

after_init { active N := false }

action activate (n : node) { active n := true }
action deactivate (n : node) { active n := false }

invariant true

#gen_spec

open Lean Elab Command in
/-- info: build-only report checked -/
#guard_msgs in
run_cmd do
  let cmd ← `(command| #model_check compiled { node := Fin 2 } {} (sequential := true))
  let messagesBefore := (← get).messages
  modify fun s => { s with messages := {} }
  withScope (fun scope => { scope with opts := veil.modelChecker.buildOnly.set scope.opts true }) do
    elabCommand cmd
  let logged := (← get).messages
  modify fun s => { s with messages := messagesBefore }
  if logged.hasErrors then
    throwError "the build-only check logged an error:\n{← logged.toList.mapM (·.toString)}"
  let texts ← logged.toList.mapM (·.data.toString)
  let some report := texts.findSome? fun text =>
      text.splitOn "\n" |>.findSome? fun line =>
        match line.splitOn "VEIL_BUILD_ONLY " with
        | ["", json] => some json
        | _ => none
    | throwError "no VEIL_BUILD_ONLY line was logged; messages: {texts}"
  let json ← IO.ofExcept (Json.parse report)
  let binary := System.FilePath.mk (← IO.ofExcept (json.getObjValAs? String "binary"))
  let buildFolder := System.FilePath.mk (← IO.ofExcept (json.getObjValAs? String "build_folder"))
  unless ← binary.pathExists do
    throwError "the reported binary does not exist: {binary}"
  -- The copy, named after the build folder, not the binary in it
  unless binary.parent != some buildFolder && binary.fileStem == buildFolder.fileName do
    throwError "the reported binary {binary} is not a copy of the one in {buildFolder}"
  for key in ["extract_ms", "emit_c_ms", "cc_link_ms", "c_bytes"] do
    discard <| IO.ofExcept (json.getObjValAs? Nat key)
  -- The search did not run: no verdict was logged.
  if texts.any (·.startsWith "✅") then
    throwError "the check ran although buildOnly was set: {texts}"
  logInfo "build-only report checked"

end BuildOnly
