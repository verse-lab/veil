import Lean
import Veil.Util.Meta
import Veil.Util.Deriving

open Lean Elab Command

namespace Veil

syntax (name := _root_.veil_decl) "veil_decl" : attr

private def veilDeclAttrName : Name := `veil_decl

private def defaultDerivingClasses : List Name := [
  ``Inhabited, ``Nonempty, ``DecidableEq, ``Lean.ToJson,
  ``Hashable, ``Ord, ``Repr,
  ``Std.TransOrd, ``Std.LawfulEqOrd,
]

initialize veilDeclExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    name := `veil_decl_ext
    addEntryFn := fun s n => s.push n
    addImportedFn := fun arrays => arrays.foldl (fun acc a => acc ++ a) #[]
  }

initialize registerBuiltinAttribute {
  name := veilDeclAttrName
  descr := "Marks a structure or inductive as a Veil declaration and automatically derives common instances for it."
  applicationTime := .afterTypeChecking
  add := fun declName _stx _kind => do
    let info ← getConstInfo declName
    unless info.isInductive do
      throwError "`@[veil_decl]` can only be applied to structure or inductive declarations"
    modifyEnv fun env => veilDeclExt.addEntry env declName
    let nameIdent := mkIdent declName
    -- `liftCommandElabM` creates a fresh scope with an anonymous namespace,
    -- but `scoped instance` (used by some deriving handlers) requires a
    -- non-anonymous namespace. Restore the declaration's namespace so that
    -- scoped attributes work correctly.
    let ns := (← read).currNamespace
    for className in defaultDerivingClasses do
      let classIdent := mkIdent className
      try
        liftCommandElabM (throwOnError := true) do
          withScope (fun scope => { scope with currNamespace := ns }) do
            elabVeilCommand <| ← `(command| deriving instance $classIdent:ident for $nameIdent:ident)
      catch ex =>
        liftCommandElabM (throwOnError := false) do
          logWarning m!"Could not automatically derive {className} for {declName}. You may need to provide a manual instance.\nError: {← ex.toMessageData.toString}"
}

end Veil
