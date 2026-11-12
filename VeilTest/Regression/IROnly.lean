module

public import Veil

/-! Testing `veil.modelChecker.irOnly`. -/

veil module IROnly

type node
relation active : node → Bool

#gen_state

after_init { active N := false }

action activate (n : node) { active n := true }
action deactivate (n : node) {
  require ∀ m, active m
  active n := false
}

invariant true

#gen_spec

open Lean Elab Command in
/-- info: IR-only report checked -/
#guard_msgs in
run_cmd do
  let cmd ← `(command| #model_check compiled { node := Fin 2 } {} (sequential := true))
  let messagesBefore := (← get).messages
  modify fun s => { s with messages := {} }
  withScope (fun scope => { scope with opts := veil.modelChecker.irOnly.set scope.opts true }) do
    elabCommand cmd
  let logged := (← get).messages
  modify fun s => { s with messages := messagesBefore }
  if logged.hasErrors then
    throwError "the IR-only check logged an error:\n{← logged.toList.mapM (·.toString)}"
  let texts ← logged.toList.mapM (·.data.toString)
  let some report := texts.findSome? fun text =>
      text.splitOn "\n" |>.findSome? fun line =>
        match line.splitOn "VEIL_IR_ONLY " with
        | ["", json] => some json
        | _ => none
    | throwError "no VEIL_IR_ONLY line was logged; messages: {texts}"
  let json ← IO.ofExcept (Json.parse report)
  let file := System.FilePath.mk (← IO.ofExcept (json.getObjValAs? String "ir_file"))
  let decls ← IO.ofExcept (json.getObjValAs? Nat "decls")
  discard <| IO.ofExcept (json.getObjValAs? Nat "compile_ms")
  unless file.components.take 2 == [".lake", "model_checker_ir"] do
    throwError "the IR file {file} is not under .lake/model_checker_ir"
  let ir ← IO.FS.readFile file
  -- One declaration per line starting a `def` or an `extern`, the entry point among them
  let starts := (ir.splitOn "\n").filter fun line => line.startsWith "def " || line.startsWith "extern "
  unless starts.length == decls && decls > 0 do
    throwError "{file} has {starts.length} declarations, the report says {decls}"
  unless starts.any (·.startsWith "def main ") do
    throwError "no IR of `main` in {file}"
  -- The actions, as compiled into the checker
  for name in ["activate", "deactivate"] do
    unless (ir.splitOn s!"IROnly.{name}.ext.extracted").length > 1 do
      throwError "no IR of the action {name} in {file}"
  -- The check did not run, and the entry point is not left in the environment
  if texts.any fun text => text.startsWith "✅" || text.startsWith "❌" then
    throwError "the check ran although irOnly was set: {texts}"
  if (← getEnv).contains `main then
    throwError "the temporary entry point `main` was left in the environment"
  logInfo "IR-only report checked"

end IROnly
