import Lean
import Veil.Backend.SMT.Base
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

/-- Return whether a declaration is supported as Veil data. `Prod` is built in;
all other structures and inductives must be marked with `@[veil_decl]`. -/
def hasVeilDeclAttr (env : Environment) (declName : Name) : Bool :=
  declName == ``Prod || (veilDeclExt.getState env).contains declName

initialize registerBuiltinAttribute {
  name := veilDeclAttrName
  descr := "Marks a structure or inductive as a Veil declaration and automatically derives common instances for it."
  applicationTime := .afterCompilation
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
    -- Veil eliminates structures into their fields before calling SMT. Registering
    -- the generated constructor-injectivity theorem makes structure equalities
    -- reduce to field equalities in the existing `smtSimp` pass. Keep inductive
    -- declarations on their existing deriving-only path.
    let isStructureDecl := (getStructureInfo? (← getEnv) declName).isSome
    if isStructureDecl then
      if let some (.inductInfo indInfo) := (← getEnv).find? declName then
        if let some ctorName := indInfo.ctors.head? then
          let injEqName := ctorName ++ `injEq
          if (← getEnv).contains injEqName then
            liftCommandElabM (throwOnError := true) do
              elabVeilCommand <| ← `(command|
                attribute [$(mkIdent `smtSimp):ident] $(mkIdent injEqName):ident)
    -- Compute this before deriving `Inhabited`: `mkInstName` chooses a fresh
    -- name, so calling it afterwards would identify the next unused name.
    let inhabitedDefaultName? ← if isStructureDecl then
      liftCommandElabM do
        liftTermElabM do
          let instName ← Lean.Elab.Deriving.mkInstName ``Inhabited declName
          let instName := if instName.isAtomic then declName.getPrefix ++ instName else instName
          return some (instName ++ `default)
    else
      pure none
    for className in defaultDerivingClasses do
      let classIdent := mkIdent className
      try
        liftCommandElabM (throwOnError := true) do
          withScope (fun scope => { scope with currNamespace := ns }) do
            elabVeilCommand <| ← `(command| deriving instance $classIdent:ident for $nameIdent:ident)
      catch ex =>
        liftCommandElabM (throwOnError := false) do
          logWarning m!"Could not automatically derive {className} for {declName}. You may need to provide a manual instance.\nError: {← ex.toMessageData.toString}"
    -- Lean's built-in `Inhabited` derivation puts the chosen constructor in a
    -- separate opaque `<instance>.default` declaration. Unfold it before SMT,
    -- otherwise an unconstrained structure field can escape flattening.
    if let some defaultName := inhabitedDefaultName? then
      if (← getEnv).contains defaultName then
        liftCommandElabM (throwOnError := true) do
          elabVeilCommand <| ← `(command|
            attribute [$(mkIdent `smtSimp):ident] $(mkIdent defaultName):ident)
}

end Veil
