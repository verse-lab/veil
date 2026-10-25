module

public import Veil
public import VeilTest.Regression.ModelCheckBuildHelper
meta import Lean

/-!
Multiple external `#model_check` commands in one file can target different Veil modules,
instantiations, theories, and checker options. Each command builds without running the search.
-/

-- Keep every binary until the assertions below have run, even if this test is built again.
set_option veil.modelChecker.maxStoredCheckers 0

veil module ModelCheckBuildMultipleToggle

individual flag : Bool

after_init { flag := false }

action toggle { flag := !flag }

invariant true

#gen_spec
#gen_executable

end ModelCheckBuildMultipleToggle

-- The imported module with a configuration that violates its bound.
/-- info: Model checker built: -/
#guard_msgs (substring := true) in
#model_check CheckedElsewhere { node := Fin 2, NodeSet := OrdList _, Buffer := Array _ }
  { limit := 1 } (maxDepth := 10)

-- The same module, instantiation, and theory, with a different checker option.
/-- info: Model checker built: -/
#guard_msgs (substring := true) in
#model_check CheckedElsewhere { node := Fin 2, NodeSet := OrdList _, Buffer := Array _ }
  { limit := 1 } (maxDepth := 1)

-- The same module with a larger instantiation and a theory that permits all eight states.
/-- info: Model checker built: -/
#guard_msgs (substring := true) in
#model_check CheckedElsewhere { node := Fin 3, NodeSet := OrdList _, Buffer := Array _ }
  { limit := 3 } (maxDepth := 10)

-- A different module, declared in this file rather than imported.
/-- info: Model checker built: -/
#guard_msgs (substring := true) in
#model_check ModelCheckBuildMultipleToggle {} {} (maxDepth := 10)

-- Use this process's completed builds, so binaries left by an earlier run cannot satisfy the test.
-- All four copied binaries must coexist and run with their own module and configuration.
open Lean Elab Command Veil.ModelChecker.Compilation in
/-- info: Four external model checkers built and ran independently. -/
#guard_msgs in
run_cmd do
  let sourceFile ← getFileName
  let registry ← compilationRegistry.atomically fun ref => ref.get
  let builds := registry.toArray.filter (fun (key, _) => key.sourceFile == sourceFile)
  unless builds.size == 4 do
    throwError "expected four independent command registrations, got {builds.size}"
  let dir := (← IO.currentDir) / ".lake" / "model_checkers"
  let mut binaries : Array System.FilePath := #[]
  let mut results : Array String := #[]
  for (_, status) in builds do
    let .finished folder := status | throwError "a model checker did not finish building"
    let binary := buildFolderBinary dir (folder.fileName.getD "")
    if binaries.contains binary then
      throwError "different model checker configurations shared a binary: {binary}"
    binaries := binaries.push binary
    unless ← binary.pathExists do
      throwError "a model checker binary was overwritten or removed: {binary}"
    -- Keep stdin open: closing it requests cancellation of the checker.
    let child ← IO.Process.spawn
      { cmd := binary.toString, stdin := .piped, stdout := .piped, stderr := .piped }
    let stderr ← IO.asTask child.stderr.readToEnd
    let stdout ← child.stdout.readToEnd
    unless (← child.wait) == 0 do throwError "the binary failed: {binary}"
    discard <| IO.ofExcept (← IO.wait stderr)
    let result ← IO.ofExcept (Json.parse stdout)
    let verdict ← IO.ofExcept (result.getObjValAs? String "result")
    let summary := if verdict == "no_violation_found" then
      s!"{verdict}: {result.getObjValD "explored_states"}"
    else verdict
    results := results.push summary
  let expected := #["found_violation", "found_violation",
    "no_violation_found: 2", "no_violation_found: 8"]
  unless results.qsort (· < ·) == expected do
    throwError "unexpected model checker results: {results}"
  logInfo "Four external model checkers built and ran independently."
