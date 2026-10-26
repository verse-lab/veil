module

public meta import Lean.Server.CodeActions
meta import Lean.Util.LakePath
public meta import Veil.Frontend.DSL.Module.Syntax
public meta import Veil.Frontend.DSL.Module.Util.Instantiation

/-! What the VS Code extension of Veil asks Lean for with code actions: the template of a config file,
which builds the model checker of a module with `#mc_config` in another file, and where the
declarations of the module of such a command are. -/

public meta section

open Lean Meta Server Lsp

namespace Veil

/-- A field of a config template, with the value that the template suggests for it -/
structure ConfigTemplateField where
  name : String
  value : String
  deriving ToJson

/-- What a config file for a module needs: the import of the module, and the fields without a
default of the instantiation and of the theory that `#mc_config` takes -/
structure ConfigTemplate where
  «module» : String
  /-- The name that imports the file of the module, unless no file can import it -/
  «import» : Option String
  instantiation : Array ConfigTemplateField
  «theory» : Array ConfigTemplateField
  deriving ToJson

/-- The fields of structure `struct` without a default value, each a hole, `_` -/
def templateFields (struct : Name) : MetaM (Array ConfigTemplateField) := do
  let env ← getEnv
  return (getStructureFieldsFlattened env struct (includeSubobjectFields := false)).filterMap fun field =>
    if (getDefaultFnForField? env struct field).isSome then none else some { name := field.toString, value := "_" }

/-- The config template of `em`, whose file is `mainModule`. Its values are holes, which guess
nothing: the instantiation fills in some of them, such as the containers that its constraints give,
and Lean reports the others for the user to fill in. -/
def configTemplate (em : ExecutableModule) (mainModule : Name) : MetaM ConfigTemplate := do
  return {
    «module» := em.name.toString
    -- `lake setup-file` gives `_unknown` for a file that is in no library, which no file imports
    «import» := if mainModule == `_unknown || mainModule.isAnonymous then none else some mainModule.toString
    instantiation := ← templateFields (em.name ++ instantiationTypeName)
    «theory» := ← templateFields (em.name ++ theoryName) }

/-- The kind of the code action that gives the config template of a module, with
`veil.modelCheck.createConfig` as its command. It is only given to a request for this kind, which the
VS Code extension of Veil makes, so that the menus of the editor do not show it.

Lean's server advertises `refactor` and `source.organizeImports`, but not all of `source`.
The `refactor` prefix therefore keeps VS Code from filtering out the Lean provider before sending
the request, as it would for `source.veil.modelCheckConfig`. -/
def configTemplateKind : String := "refactor.veil.modelCheckConfig"

@[command_code_action Veil.genExecutable]
def configTemplateCodeAction : CodeAction.CommandCodeAction := fun params snap ctx _ => do
  unless params.context.only?.any (·.contains configTemplateKind) do return #[]
  -- The module and what `#gen_executable` recorded about it
  let env := snap.env
  let some mod := (localEnv.getState env).currentModule | return #[]
  let some em := (executableModuleExt.getState env)[mod.name]? | return #[]
  -- `env.mainModule` may be path-derived even when the file is outside Lake's libraries.
  -- Ask Lake for its import name instead, without building dependencies or downloading caches.
  -- `configTemplate` maps `_unknown` or anonymous names to no import, so the extension can warn
  -- instead of creating a config that imports an unregistered module.
  let mainModule ← do
    let some filePath := System.Uri.fileUriToPath? params.textDocument.uri | pure Name.anonymous
    let setup ← IO.Process.output {
      cmd := (← determineLakePath).toString
      args := #["setup-file", filePath.toString, "--no-build", "--no-cache"] }
    if setup.exitCode == 2 then pure Name.anonymous
    else
      unless setup.exitCode == 0 do
        throw <| RequestError.internalError s!"Cannot determine the module's Lake library: {setup.stderr}"
      let json ← IO.ofExcept (Json.parse setup.stdout)
      IO.ofExcept (json.getObjValAs? Name "name")
  let template ← { ctx with env }.runMetaM {} (configTemplate em mainModule)
  return #[{ eager := {
    title := s!"Create a model checking config for {mod.name}"
    kind? := configTemplateKind
    command? := some {
      title := "Create a model checking config"
      command := "veil.modelCheck.createConfig"
      arguments? := #[toJson template, toJson params.textDocument.uri] } } }]

/-- Where the declarations of a module are, by the names that model checking results give them -/
structure ModuleSources where
  actions : Array DeclSource
  properties : Array DeclSource
  deriving ToJson

/-- The kind of the code action that gives where the declarations of the module of a
`#mc_config` command are. As with `configTemplateKind`, only a request for it gets it, and it
is a `refactor` kind for VS Code to ask Lean. -/
def moduleSourcesKind : String := "refactor.veil.modelCheckSources"

@[command_code_action Veil.modelCheckBuild]
def moduleSourcesCodeAction : CodeAction.CommandCodeAction := fun params snap _ node => do
  unless params.context.only?.any (·.contains moduleSourcesKind) do return #[]
  let .node (.ofCommandInfo info) _ := node | return #[]
  let some em := (executableModuleExt.getState snap.env)[info.stx[1].getId]? | return #[]
  -- The file of a module that `lake build` built is relative to the workspace, where the server is
  let workspace ← IO.currentDir
  let absolute (source : DeclSource) : DeclSource :=
    let file : System.FilePath := source.file
    { source with file := (if file.isAbsolute then file else workspace / file).toString }
  let sources : ModuleSources :=
    { actions := em.actionSources.map absolute, properties := em.propertySources.map absolute }
  return #[{ eager := {
    title := s!"Where the declarations of {em.name} are"
    kind? := moduleSourcesKind
    -- The extension reads the arguments of the command, and does not run it
    command? := some { title := "", command := "veil.modelCheck.sources", arguments? := #[toJson sources] } } }]

end Veil
