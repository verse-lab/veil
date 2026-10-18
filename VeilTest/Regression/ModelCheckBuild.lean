module

public import Veil
public import VeilTest.Regression.ModelCheckBuildHelper
meta import Lean

/-! `#model_check_build` builds a model checker for a module of another file. -/

-- The holes are filled from the `instantiate` constraints that `#gen_executable` recorded. As
-- inside the module, the scoped instances of its enums are needed.
open CheckedElsewhere in
def inferred : CheckedElsewhere.Instantiation :=
  __veil_instantiation_of% CheckedElsewhere { node := Fin 2, NodeSet := OrdList _, Buffer := Array _ }

example : inferred.NodeSet = OrdList (Fin 2) := rfl
example : inferred.Buffer = Array (Fin 2) := rfl
-- The enum sort keeps its default
example : inferred.Phase = CheckedElsewhere.Phase_IndT := rfl

-- Remove the binaries of earlier runs, so that the one run below is the one built here
run_cmd do
  let dir := (← IO.currentDir) / ".lake" / "model_checkers"
  if ← dir.pathExists then
    for entry in ← dir.readDir do
      if entry.fileName.startsWith "ModelCheckBuild_model_check_build_" then
        IO.FS.removeFile entry.path

/-- info: Model checker built: -/
#guard_msgs (substring := true) in
#model_check_build CheckedElsewhere { node := Fin 2, NodeSet := OrdList _, Buffer := Array _ }
  { limit := 2 }

-- The binary is copied out of its build folder, and runs from there
open Lean Elab Command in
/-- info: "no_violation_found", 4 states -/
#guard_msgs in
run_cmd do
  let dir := (← IO.currentDir) / ".lake" / "model_checkers"
  let some binary := (← dir.readDir).find? (·.fileName.startsWith "ModelCheckBuild_model_check_build_")
    | throwError "no binary was built"
  -- The binary exits once its stdin is closed, so keep it open
  let child ← IO.Process.spawn
    { cmd := binary.path.toString, stdin := .piped, stdout := .piped, stderr := .null }
  let stdout ← child.stdout.readToEnd
  unless (← child.wait) == 0 do throwError "the binary failed"
  let result ← IO.ofExcept (Json.parse stdout)
  logInfo m!"{result.getObjValD "result"}, {result.getObjValD "explored_states"} states"

-- A hole that no default instance fills is reported at the instantiation
/-- error: failed to synthesize instance of type class -/
#guard_msgs (substring := true) in
open CheckedElsewhere in
example : CheckedElsewhere.Instantiation :=
  __veil_instantiation_of% CheckedElsewhere { node := Fin 2, NodeSet := OrdList _, Buffer := List _ }

-- The parallel configuration is an argument of the binary
/--
error: `sequential` is not part of the model checker: pass the parallel configuration to the binary as arguments.
-/
#guard_msgs in
#model_check_build CheckedElsewhere { node := Fin 2, NodeSet := OrdList _, Buffer := Array _ }
  { limit := 2 } (sequential := true)

/--
error: Module NotExecutable has no executable definitions here: add `#gen_executable` to the `veil module NotExecutable` block that declares it.
-/
#guard_msgs in
#model_check_build NotExecutable {} {}
