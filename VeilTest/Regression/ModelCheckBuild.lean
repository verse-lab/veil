module

public import Veil
public import VeilTest.Regression.ModelCheckBuildHelper
meta import Lean

/-! `#mc_config` builds a model checker for a module of another file. -/

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
#mc_config CheckedElsewhere { node := Fin 2, NodeSet := OrdList _, Buffer := Array _ }
  { limit := 1 }

-- The binary is copied out of its build folder, and runs from there. Its counterexample shows the
-- states and the theory, whose `Display` instances are scoped in the module.
open Lean Elab Command in
/--
info: "found_violation" of ["bounded"], theory {"$veil":"record","fields":[{"name":"limit","value":1}],"type":"Theory"}, last state {"$veil":"record","fields":[{"name":"phase","value":"idle"},{"name":"finished","value":{"$veil":"set","elements":[0,1]}}],"type":"State"}
---
info: actions ["finish"]
-/
#guard_msgs in
run_cmd do
  let dir := (← IO.currentDir) / ".lake" / "model_checkers"
  let some binary := (← dir.readDir).find? (·.fileName.startsWith "ModelCheckBuild_model_check_build_")
    | throwError "no binary was built"
  -- The binary exits once its stdin is closed, so keep it open
  let child ← IO.Process.spawn
    { cmd := binary.path.toString, stdin := .piped, stdout := .piped, stderr := .piped }
  let stderr ← IO.asTask child.stderr.readToEnd
  let stdout ← child.stdout.readToEnd
  unless (← child.wait) == 0 do throwError "the binary failed"
  let result ← IO.ofExcept (Json.parse stdout)
  let cex := result.getObjValD "trace"
  let states ← IO.ofExcept (cex.getObjValAs? (Array Json) "states")
  logInfo m!"{result.getObjValD "result"} of {(result.getObjValD "violation").getObjValD "violates"}, \
    theory {(cex.getObjValD "theory").compress}, last state {(states.back!.getObjValD "fields").compress}"
  -- It first reports the actions of the module, so that those never enabled can be told
  let lines := (← IO.ofExcept (← IO.wait stderr)).splitOn "\n"
  let start ← IO.ofExcept (Json.parse lines.head!)
  logInfo m!"actions {((start.getObjValD "start").getObjValD "actionLabels").compress}"

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
#mc_config CheckedElsewhere { node := Fin 2, NodeSet := OrdList _, Buffer := Array _ }
  { limit := 2 } (sequential := true)

-- Options can also follow a left-out theory, instead of being parsed as one
/--
error: `sequential` is not part of the model checker: pass the parallel configuration to the binary as arguments.
-/
#guard_msgs in
#mc_config CheckedElsewhere { node := Fin 2, NodeSet := OrdList _, Buffer := Array _ }
  (sequential := true)

/--
error: `config` sets the parallel configuration, which is not part of the model checker: pass it to the binary as arguments.
-/
#guard_msgs in
#mc_config CheckedElsewhere { node := Fin 2, NodeSet := OrdList _, Buffer := Array _ }
  { limit := 2 } (config := { sequential := true })

-- A full configuration without them is fine
/-- info: Model checker built: -/
#guard_msgs (substring := true) in
#mc_config CheckedElsewhere { node := Fin 2, NodeSet := OrdList _, Buffer := Array _ }
  { limit := 2 } (config := { maxDepth := 3 })

-- As the instantiation and the theory do, the values of the options resolve the names of the
-- module's namespace, so that a `#model_check` of the module can be copied as it is
namespace CheckedElsewhere
def depthBound : Nat := 3
end CheckedElsewhere

/-- info: Model checker built: -/
#guard_msgs (substring := true) in
#mc_config CheckedElsewhere { node := Fin 2, NodeSet := OrdList _, Buffer := Array _ }
  { limit := 2 } (maxDepth := depthBound)

/--
error: Module NotExecutable has no executable definitions here: add `#gen_executable` to the `veil module NotExecutable` block that declares it.
-/
#guard_msgs in
#mc_config NotExecutable {} {}

-- The template of a config file for `CheckedElsewhere`, which the VS Code extension asks for. The enum
-- sort keeps its default, and the other fields are holes. A file in no library has no import.
open Lean Meta in
/--
info: {"import":"VeilTest.Regression.ModelCheckBuildHelper","instantiation":[{"name":"node","value":"_"},{"name":"NodeSet","value":"_"},{"name":"Buffer","value":"_"}],"module":"CheckedElsewhere","theory":[{"name":"limit","value":"_"}]}
null
-/
#guard_msgs in
#eval show MetaM Unit from do
  let some em ← Veil.getExecutableModule? `CheckedElsewhere | throwError "no executable definitions"
  IO.println (toJson (← Veil.configTemplate em `VeilTest.Regression.ModelCheckBuildHelper)).compress
  IO.println ((toJson (← Veil.configTemplate em `_unknown)).getObjValD "import").compress

/-- error: don't know how to synthesize placeholder -/
#guard_msgs (substring := true) in
#mc_config CheckedElsewhere { node := Fin 2, NodeSet := _, Buffer := _ } { limit := _ }

/-- Fields missing: `limit` -/
#guard_msgs (substring := true) in
#mc_config CheckedElsewhere { node := Fin 2, NodeSet := _, Buffer := _ }

/-- Fields missing: `limit` -/
#guard_msgs (substring := true) in
#mc_config CheckedElsewhere { node := Fin 2, NodeSet := _, Buffer := _ } {}

/-- error: don't know how to synthesize placeholder -/
#guard_msgs (substring := true) in
#mc_config CheckedElsewhere { node := Fin 2, NodeSet := _, Buffer := _ } _

/-- error: don't know how to synthesize placeholder -/
#guard_msgs (substring := true) in
#mc_config CheckedElsewhere _ { limit := 2 }

/-- error: don't know how to synthesize placeholder -/
#guard_msgs (substring := true) in
#mc_config CheckedElsewhere { node := _, NodeSet := _, Buffer := _ } { limit := 2 }

/-- error: failed to synthesize instance of type class -/
#guard_msgs (substring := true) in
#mc_config CheckedElsewhere { node := Fin 2, NodeSet := _, Buffer := List _ } { limit := 2 }

/--
error: Type mismatch
  true
has type
  Bool
but is expected to have type
  Nat
-/
#guard_msgs in
#mc_config CheckedElsewhere { node := Fin 2, NodeSet := _, Buffer := _ } { limit := true }

/-- error: `unknown` is not a field of structure `CheckedElsewhere.Theory` -/
#guard_msgs in
#mc_config CheckedElsewhere { node := Fin 2, NodeSet := _, Buffer := _ } { unknown := 2 }

/-- info: Model checker built: -/
#guard_msgs (substring := true) in
#mc_config CheckedElsewhere { node := _, NodeSet := OrdList (Fin 2), Buffer := _ } { limit := 2 }

-- Where the actions and the properties of `CheckedElsewhere` are, which the VS Code extension links
-- the results to
open Lean Meta in
/--
info: #[after_init at ModelCheckBuildHelper.lean:36:0, finish at ModelCheckBuildHelper.lean:41:0]
#[bounded at ModelCheckBuildHelper.lean:47:0]
-/
#guard_msgs in
#eval show MetaM Unit from do
  let some em ← Veil.getExecutableModule? `CheckedElsewhere | throwError "no executable definitions"
  let describe (source : Veil.DeclSource) :=
    s!"{source.name} at {(System.FilePath.mk source.file).fileName.getD ""}:{source.line}:{source.character}"
  IO.println (em.actionSources.map describe)
  IO.println (em.propertySources.map describe)

-- The sources that results give the infoview within a module, which link its trace to them: with the
-- URIs of their files, where a relative file is in the workspace
open Lean in
/--
info: {"actions":[{"character":0,"line":36,"name":"after_init","uri":"file:///repo/M.lean"}],"properties":[{"character":2,"line":47,"name":"bounded","uri":"file:///repo/Examples/M.lean"}]}
-/
#guard_msgs in
#eval IO.println (Veil.ExecutionWorkflow.infoviewSources
  #[{ name := "after_init", file := "/repo/M.lean", line := 36, character := 0 }]
  #[{ name := "bounded", file := "Examples/M.lean", line := 47, character := 2 }] "/repo").compress
