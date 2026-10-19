module

public meta import Lean.Server.CodeActions
public meta import Veil.Frontend.DSL.Module.Syntax
public meta import Veil.Frontend.DSL.Module.Util.Instantiation

/-! The template of a config file, which builds the model checker of a module with
`#model_check_build` in another file. The VS Code extension of Veil asks for it with a code action. -/

public meta section

open Lean Meta Server Lsp

namespace Veil

/-- A field of a config template, with the value that the template suggests for it -/
structure ConfigTemplateField where
  name : String
  value : String
  deriving ToJson

/-- What a config file for a module needs: the import of the module, and the fields without a
default of the instantiation and of the theory that `#model_check_build` takes -/
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
VS Code extension of Veil makes, so that the menus of the editor do not show it. -/
def configTemplateKind : String := "source.veil.modelCheckConfig"

@[command_code_action Veil.genExecutable]
def configTemplateCodeAction : CodeAction.CommandCodeAction := fun params snap ctx _ => do
  unless params.context.only?.any (·.contains configTemplateKind) do return #[]
  -- The module and what `#gen_executable` recorded about it
  let env := snap.env
  let some mod := (localEnv.getState env).currentModule | return #[]
  let some em := (executableModuleExt.getState env)[mod.name]? | return #[]
  let template ← { ctx with env }.runMetaM {} (configTemplate em env.mainModule)
  return #[{ eager := {
    title := s!"Create a model checking config for {mod.name}"
    kind? := configTemplateKind
    command? := some {
      title := "Create a model checking config"
      command := "veil.modelCheck.createConfig"
      arguments? := #[toJson template, toJson params.textDocument.uri] } } }]

end Veil
