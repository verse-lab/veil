import Lean
import Std
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.State.Concrete

/-!
# Concrete Representation Registry

This file defines a registry for concrete runtime representations of fields in Veil.
Users can configure which concrete type to use for `relation` (finset-like) and
`function` (finmap-like) fields.

Each concrete representation stores:
- The typeclass instance requirements for constructing the type
- The typeclass instance requirements for `FieldRepresentation`
- The typeclass instance requirements for `LawfulFieldRepresentation`
- The instance names for resolving FieldRepresentation

For functions, we distinguish between instances required on domain types vs codomain types.
-/

open Lean

namespace Veil

/-! ## Data Structures -/

/-- The kind of concrete representation (for relations or functions). -/
inductive ConcreteRepKind where
  /-- For `relation` fields (finset-like: set of domain elements) -/
  | finsetLike
  /-- For `function` fields (finmap-like: map from domain to codomain) -/
  | finmapLike
deriving Inhabited, BEq, Hashable, Repr

/-- Configuration for a concrete representation type. -/
structure ConcreteRepConfig where
  /-- The kind of representation (finset-like or finmap-like) -/
  kind : ConcreteRepKind
  /-- The name of the concrete type (e.g., `Std.ExtTreeMap`) -/
  typeName : Name
  /-- Instance requirements on DOMAIN types for constructing the type itself -/
  domainTypeInstances : Array Name
  /-- Instance requirements on CODOMAIN type for constructing the type itself (only for finmapLike) -/
  codomainTypeInstances : Array Name := #[]
  /-- Instance requirements on DOMAIN types for `FieldRepresentation` instance -/
  domainFieldRepInstances : Array Name
  /-- Instance requirements on CODOMAIN type for `FieldRepresentation` instance -/
  codomainFieldRepInstances : Array Name := #[]
  /-- Instance requirements on DOMAIN types for `LawfulFieldRepresentation` instance -/
  domainLawfulFieldRepInstances : Array Name
  /-- Instance requirements on CODOMAIN type for `LawfulFieldRepresentation` instance -/
  codomainLawfulFieldRepInstances : Array Name := #[]
  /-- Name of the `FieldRepresentation` instance (e.g., `instFinmapLikeAsFieldRep`) -/
  fieldRepInstance : Name
  /-- Name of the `LawfulFieldRepresentation` instance -/
  lawfulFieldRepInstance : Name
deriving Inhabited, Repr

/-- The global registry of available concrete representations. -/
structure ConcreteRepRegistry where
  /-- Map from type name to its configuration -/
  configs : Std.HashMap Name ConcreteRepConfig := {}
deriving Inhabited

/-! ## Built-in Concrete Representations -/

namespace ConcreteRepRegistry

/-- Configuration for `Std.ExtTreeSet` (default for relations). -/
def extTreeSetConfig : ConcreteRepConfig := {
  kind := .finsetLike
  typeName := ``Std.ExtTreeSet
  domainTypeInstances := #[``Ord]
  domainFieldRepInstances := #[``Ord, ``Std.TransOrd]
  domainLawfulFieldRepInstances := #[``DecidableEq, ``Ord, ``Std.TransOrd, ``Std.LawfulEqOrd]
  fieldRepInstance := ``instFinsetLikeAsFieldRep
  lawfulFieldRepInstance := ``instFinsetLikeLawfulFieldRep
}

/-- Configuration for `Std.ExtTreeMap` (default for functions). -/
def extTreeMapConfig : ConcreteRepConfig := {
  kind := .finmapLike
  typeName := ``Std.ExtTreeMap
  domainTypeInstances := #[``Ord]
  codomainTypeInstances := #[]
  domainFieldRepInstances := #[``Ord, ``Std.TransOrd]
  codomainFieldRepInstances := #[``Inhabited]
  domainLawfulFieldRepInstances := #[``DecidableEq, ``Ord, ``Std.TransOrd, ``Std.LawfulEqOrd]
  codomainLawfulFieldRepInstances := #[``Inhabited]
  fieldRepInstance := ``instFinmapLikeAsFieldRep
  lawfulFieldRepInstance := ``instFinmapLikeLawfulFieldRep
}

/-- All built-in concrete representation configs. -/
def builtinConcreteRepConfigs : List ConcreteRepConfig :=
  [extTreeSetConfig, extTreeMapConfig]

end ConcreteRepRegistry

/-- The persistent environment extension for the concrete representation registry. -/
initialize concreteRepRegistry : SimplePersistentEnvExtension ConcreteRepConfig ConcreteRepRegistry ←
  registerSimplePersistentEnvExtension {
    name := `veil.concreteRepRegistry
    addEntryFn := fun reg cfg => { reg with configs := reg.configs.insert cfg.typeName cfg }
    addImportedFn := fun entries =>
      -- Start with built-in configs
      let builtinReg : ConcreteRepRegistry := { configs :=
        Std.HashMap.ofList <| ConcreteRepRegistry.builtinConcreteRepConfigs.map fun cfg => (cfg.typeName, cfg) }
      -- Add imported configs
      let allConfigs := entries.flatten
      { configs := allConfigs.foldl (init := builtinReg.configs) fun acc cfg => acc.insert cfg.typeName cfg }
  }

/-- Get the current concrete representation registry. -/
def getConcreteRepRegistry [Monad m] [MonadEnv m] : m ConcreteRepRegistry := do
  return concreteRepRegistry.getState (← getEnv)

/-- Register a new concrete representation configuration. -/
def ConcreteRepRegistry.registerConcreteRep [Monad m] [MonadEnv m] (cfg : ConcreteRepConfig) : m Unit := do
  modifyEnv (concreteRepRegistry.addEntry · cfg)

/-- Look up a concrete representation by name. -/
def ConcreteRepRegistry.lookupConcreteRep [Monad m] [MonadEnv m] (name : Name) : m (Option ConcreteRepConfig) := do
  let reg ← getConcreteRepRegistry
  return reg.configs[name]?

/-! ## Resolved Configuration -/

/-- Resolved concrete representation configs for a module.
    Contains the configs to use for relation and function fields. -/
structure ResolvedConcreteRepConfigs where
  relationConfig : ConcreteRepConfig
  functionConfig : ConcreteRepConfig
deriving Inhabited

/-- Get the resolved concrete representation configs for a module.
    Uses module-level configuration if set, otherwise defaults. -/
def resolveConcreteRepConfigs [Monad m] [MonadEnv m] [MonadError m]
    (moduleConfig : Std.HashMap StateComponentKind Name) : m ResolvedConcreteRepConfigs := do
  let relationCfg ← match moduleConfig[StateComponentKind.relation]? with
    | some name =>
      let some cfg ← ConcreteRepRegistry.lookupConcreteRep name | throwError s!"Unknown concrete representation: {name}"
      pure cfg
    | none => pure ConcreteRepRegistry.extTreeSetConfig
  let functionCfg ← match moduleConfig[StateComponentKind.function]? with
    | some name =>
      let some cfg ← ConcreteRepRegistry.lookupConcreteRep name | throwError s!"Unknown concrete representation: {name}"
      pure cfg
    | none => pure ConcreteRepRegistry.extTreeMapConfig
  return { relationConfig := relationCfg, functionConfig := functionCfg }

end Veil
