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
  /-- Instance requirements for constructing the type itself (applied to all sorts) -/
  typeInstances : Array Name
  /-- Instance requirements for `FieldRepresentation` instance (applied to all sorts) -/
  fieldRepInstances : Array Name
  /-- Instance requirements for `LawfulFieldRepresentation` instance (applied to all sorts) -/
  lawfulFieldRepInstances : Array Name
  /-- Name of the `FieldRepresentation` instance (e.g., `instFinmapLikeAsFieldRep`) -/
  fieldRepInstance : Name
  /-- Name of the `LawfulFieldRepresentation` instance -/
  lawfulFieldRepInstance : Name
  /-- Name of the hybrid (not-necessarily-finite) FieldRepresentation instance -/
  hybridFieldRepInstance : Name
  /-- Name of the hybrid LawfulFieldRepresentation instance -/
  hybridLawfulFieldRepInstance : Name
deriving Inhabited, Repr

/-- The global registry of available concrete representations. -/
structure ConcreteRepRegistry where
  /-- Map from type name to its configuration -/
  configs : Std.HashMap Name ConcreteRepConfig := {}
deriving Inhabited

/-! ## Global Registry -/

/-! ## Built-in Concrete Representations -/

/-- Configuration for `Std.ExtTreeSet` (default for relations). -/
def extTreeSetConfig : ConcreteRepConfig := {
  kind := .finsetLike
  typeName := ``Std.ExtTreeSet
  -- Type needs: Ord on domain (implicit via compare)
  typeInstances := #[``Ord]
  -- FieldRepresentation needs: Inhabited, Enumeration, DecidableEq, Ord, TransCmp
  fieldRepInstances := #[``Inhabited, ``Enumeration, ``DecidableEq, ``Ord, ``Std.TransCmp]
  -- LawfulFieldRepresentation additionally needs: LawfulEqCmp
  lawfulFieldRepInstances := #[``Inhabited, ``Enumeration, ``DecidableEq, ``Ord, ``Std.TransCmp, ``Std.LawfulEqCmp]
  fieldRepInstance := ``instFinsetLikeAsFieldRep
  lawfulFieldRepInstance := ``instFinsetLikeLawfulFieldRep
  hybridFieldRepInstance := ``NotNecessarilyFinsetLikeUpdates.instHybridFinsetLikeAsFieldRep
  hybridLawfulFieldRepInstance := ``NotNecessarilyFinsetLikeUpdates.instHybridFinsetLikeLawfulFieldRep
}

/-- Configuration for `Std.ExtTreeMap` (default for functions). -/
def extTreeMapConfig : ConcreteRepConfig := {
  kind := .finmapLike
  typeName := ``Std.ExtTreeMap
  -- Type needs: Ord on domain
  typeInstances := #[``Ord]
  -- FieldRepresentation needs: Inhabited, Enumeration, DecidableEq, Ord, TransCmp
  fieldRepInstances := #[``Inhabited, ``Enumeration, ``DecidableEq, ``Ord, ``Std.TransCmp]
  -- LawfulFieldRepresentation additionally needs: LawfulEqCmp
  lawfulFieldRepInstances := #[``Inhabited, ``Enumeration, ``DecidableEq, ``Ord, ``Std.TransCmp, ``Std.LawfulEqCmp]
  fieldRepInstance := ``instFinmapLikeAsFieldRep
  lawfulFieldRepInstance := ``instFinmapLikeLawfulFieldRep
  hybridFieldRepInstance := ``NotNecessarilyFinmapLikeUpdates.instHybridFinmapLikeAsFieldRep
  hybridLawfulFieldRepInstance := ``NotNecessarilyFinmapLikeUpdates.instHybridFinmapLikeLawfulFieldRep
}

/-- Configuration for `Std.HashSet` (alternative for relations). -/
def hashSetConfig : ConcreteRepConfig := {
  kind := .finsetLike
  typeName := ``Std.HashSet
  -- Type needs: BEq, Hashable on domain
  typeInstances := #[``BEq, ``Hashable]
  -- FieldRepresentation needs: Inhabited, Enumeration, DecidableEq, BEq, Hashable
  fieldRepInstances := #[``Inhabited, ``Enumeration, ``DecidableEq, ``BEq, ``Hashable]
  -- LawfulFieldRepresentation additionally needs nothing special
  lawfulFieldRepInstances := #[``Inhabited, ``Enumeration, ``DecidableEq, ``BEq, ``Hashable]
  fieldRepInstance := ``instFinsetLikeAsFieldRep
  lawfulFieldRepInstance := ``instFinsetLikeLawfulFieldRep
  hybridFieldRepInstance := ``NotNecessarilyFinsetLikeUpdates.instHybridFinsetLikeAsFieldRep
  hybridLawfulFieldRepInstance := ``NotNecessarilyFinsetLikeUpdates.instHybridFinsetLikeLawfulFieldRep
}

/-- Configuration for `Std.HashMap` (alternative for functions). -/
def hashMapConfig : ConcreteRepConfig := {
  kind := .finmapLike
  typeName := ``Std.HashMap
  -- Type needs: BEq, Hashable on domain
  typeInstances := #[``BEq, ``Hashable]
  -- FieldRepresentation needs: Inhabited, Enumeration, DecidableEq, BEq, Hashable, LawfulHashable
  fieldRepInstances := #[``Inhabited, ``Enumeration, ``DecidableEq, ``BEq, ``Hashable, ``LawfulHashable]
  -- LawfulFieldRepresentation same
  lawfulFieldRepInstances := #[``Inhabited, ``Enumeration, ``DecidableEq, ``BEq, ``Hashable, ``LawfulHashable]
  fieldRepInstance := ``instFinmapLikeAsFieldRep
  lawfulFieldRepInstance := ``instFinmapLikeLawfulFieldRep
  hybridFieldRepInstance := ``NotNecessarilyFinmapLikeUpdates.instHybridFinmapLikeAsFieldRep
  hybridLawfulFieldRepInstance := ``NotNecessarilyFinmapLikeUpdates.instHybridFinmapLikeLawfulFieldRep
}

/-- All built-in concrete representation configs. -/
def builtinConcreteRepConfigs : Array ConcreteRepConfig :=
  #[extTreeSetConfig, extTreeMapConfig, hashSetConfig, hashMapConfig]

/-- The persistent environment extension for the concrete representation registry. -/
initialize concreteRepRegistry : SimplePersistentEnvExtension ConcreteRepConfig ConcreteRepRegistry ←
  registerSimplePersistentEnvExtension {
    name := `veil.concreteRepRegistry
    addEntryFn := fun reg cfg => { reg with configs := reg.configs.insert cfg.typeName cfg }
    addImportedFn := fun entries =>
      -- Start with built-in configs
      let builtinReg : ConcreteRepRegistry := { configs := builtinConcreteRepConfigs.foldl (init := {}) fun acc cfg => acc.insert cfg.typeName cfg }
      -- Add imported configs
      let allConfigs := entries.flatten
      { configs := allConfigs.foldl (init := builtinReg.configs) fun acc cfg => acc.insert cfg.typeName cfg }
  }

/-- Get the current concrete representation registry. -/
def getConcreteRepRegistry [Monad m] [MonadEnv m] : m ConcreteRepRegistry := do
  return concreteRepRegistry.getState (← getEnv)

/-- Register a new concrete representation configuration. -/
def registerConcreteRep [Monad m] [MonadEnv m] (cfg : ConcreteRepConfig) : m Unit := do
  modifyEnv (concreteRepRegistry.addEntry · cfg)

/-- Look up a concrete representation by name. -/
def lookupConcreteRep [Monad m] [MonadEnv m] (name : Name) : m (Option ConcreteRepConfig) := do
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
      let some cfg ← lookupConcreteRep name | throwError s!"Unknown concrete representation: {name}"
      pure cfg
    | none => pure extTreeSetConfig
  let functionCfg ← match moduleConfig[StateComponentKind.function]? with
    | some name =>
      let some cfg ← lookupConcreteRep name | throwError s!"Unknown concrete representation: {name}"
      pure cfg
    | none => pure extTreeMapConfig
  return { relationConfig := relationCfg, functionConfig := functionCfg }

/-- Get all unique type instance requirements from both configs. -/
def ResolvedConcreteRepConfigs.allTypeInstances (cfg : ResolvedConcreteRepConfigs) : Array Name :=
  let all := cfg.relationConfig.typeInstances ++ cfg.functionConfig.typeInstances
  all.foldl (init := #[]) fun acc n => if acc.contains n then acc else acc.push n

/-- Get all unique field rep instance requirements from both configs. -/
def ResolvedConcreteRepConfigs.allFieldRepInstances (cfg : ResolvedConcreteRepConfigs) : Array Name :=
  let all := cfg.relationConfig.fieldRepInstances ++ cfg.functionConfig.fieldRepInstances
  all.foldl (init := #[]) fun acc n => if acc.contains n then acc else acc.push n

/-- Get all unique lawful field rep instance requirements from both configs. -/
def ResolvedConcreteRepConfigs.allLawfulFieldRepInstances (cfg : ResolvedConcreteRepConfigs) : Array Name :=
  let all := cfg.relationConfig.lawfulFieldRepInstances ++ cfg.functionConfig.lawfulFieldRepInstances
  all.foldl (init := #[]) fun acc n => if acc.contains n then acc else acc.push n

end Veil
