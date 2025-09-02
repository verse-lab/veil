import Lean
open Lean Parser

namespace Veil

/-! # Module representation

  This file contains the in-memory representation of Veil DSL modules.

-/

/-! ## Background theory and State -/

inductive Mutability where
  /-- This should go in the `mutable` state. -/
  | mutable
  /-- This should go in the `immutable` background theory. -/
  | immutable
  /-- Mutability is inherited from the child module. This is only
  allowed for `module` state components. -/
  | inherit
deriving Inhabited, BEq

inductive StateComponentKind where
  /-- A first-order constant -/
  | individual
  /-- A first-order relation -/
  | relation
  /-- A first-order function -/
  | function
  /-- A structure that represents the state of a child module. This
  will lift the immutable (background theory of the child) into the
  parent, and the mutable state of the child into the parent. If
  multiple children of the same `Module` type exist, only one instance
  of the background theory will be lifted. -/
  | module
deriving Inhabited, BEq

/-- How is the type (i.e. Lean type) of the state component given? -/
inductive StateComponentType where
  /-- e.g. `stateComponentName : Int -> vertex -> Prop` -/
  | simple (t : TSyntax ``Command.structSimpleBinder)
  /-- e.g. `(r : Int) (v : vertex)` and `Prop` -/
  | complex (binders : TSyntaxArray ``Term.bracketedBinder) (dom : Term)
deriving Inhabited, BEq

structure StateComponent where
  /-- Is this state component mutable or immutable? -/
  mutability : Mutability
  /-- Is this an `individual`, a `relation`, or ` function`?-/
  kind       : StateComponentKind
  /-- The name of the state component -/
  name       : Name
  /-- The Lean syntax that declares the type of this state component -/
  type       : StateComponentType
  /-- The user-written syntax that resulted in the declaration of this
  state component. -/
  userSyntax : Syntax
deriving Inhabited, BEq

inductive ModuleTypeClassKind where
  /-- This typeclass assumption relates to the background theory of the
  environment that this module operates in. We put every assumption
  about the sorts into this kind, even though those sorts might not in
  fact be used in the immutable theory. -/
  | backgroundTheory
  /-- This typeclass assumption relates to the state of the environment
  that this module operates in. -/
  | environmentState
  /-- This typeclass assumption was made explicitly by the user. -/
  | userDefined
deriving Inhabited, BEq

inductive ParameterKind where
  /-- A (FOL) sort, i.e. a Lean type. The `sort` parameters are those that
  are used to declare the `State` type of the module. -/
  | uninterpretedSort
  /-- The type of the state of the _environment_ that this module
  operates in. The module's own state will be a sub-state of this. -/
  | environmentState -- i.e. `σ`
  /-- The background theory of the environment that this module
  operates in. The module's own background theory will be a sub-reader
  of this. -/
  | backgroundTheory -- i.e. `ρ`
  /-- A typeclass assumption this module makes -/
  | moduleTypeclass (kind : ModuleTypeClassKind)
  /-- A typeclass assumption that _a particular definition_ makes.
  These are typically `Decidable` instances. -/
  | definitionTypeclass (defName : Name)
deriving Inhabited, BEq

structure Parameter where
  kind : ParameterKind
  name : Name
  type : Term
  /-- The user-written syntax that resulted in the declaration of this
  parameter. Note that multiple parameters might be due to the same
  user-provided syntax. -/
  userSyntax : Syntax
deriving Inhabited, BEq

/-! ## Assertions about state (or background theory) -/

inductive StateAssertionKind
  /-- A property of the immutable background theory. -/
  | assumption
  /-- A property of the mutable state. -/
  | invariant
  /-- Mean the same thing as `invariant`, but `safety` is as a convention
  used to denote the main, top-level properties of the system, whereas
  `invariant` clauses support the safety properties.-/
  | safety
  /-- An `trusted invariant` is different from an `assumption` in that
  it can refer to `mutable` state. It differs from an `invariant` in
  that is only assumed, not checked. -/
  | trustedInvariant
deriving BEq, Hashable

instance : Inhabited StateAssertionKind where
  default := StateAssertionKind.invariant

structure StateAssertion where
  kind : StateAssertionKind
  name : Name
  /-- "Extra parameters" that are needed to make this assertion
  decidable/checkable. -/
  extraParams : Array Parameter
  /-- Lean term for this predicate -/
  term : Term
  /-- The sets of assertions that this assertion is in. -/
  inSets : Std.HashSet Name
  /-- The user-written syntax that resulted in the declaration of this
  assertion. -/
  userSyntax : Syntax
deriving Inhabited

/-! ## Procedure and actions -/

/--
  A `procedure` is a chunk of imperative code that takes arguments and
  potentially returns a value.

  If you think in terms of transition systems, an `action` is a
  procedure that behaves as a visible `transition` of the system,
  whereas a regular `procedure` is an internal, invisible transition.

  | Veil        | Ivy equivalent  |
  |-------------|-----------------|
  | `procedure` | `action`        |
  | `action`    | `export action` |
 -/

abbrev ProcedureIdentifier := Lean.Name

inductive ProcedureInfo
  /-- A procedure that is called by the environment to initialize the module. -/
  | initializer
  /-- Callable by the environment -/
  | action (name : Name)
  /-- Not callable by the environment -/
  | procedure (name : Name)
deriving Inhabited, BEq

abbrev ActionSyntax := TSyntax ``Term.doSeq

structure ProcedureSpecification where
  /-- Is this an `action` or a `procedure`? And what is its declaration? -/
  info : ProcedureInfo
  /-- Parameters of the current action. -/
  params : Option (TSyntax ``Lean.explicitBinders) := none
  /-- "Extra parameters" that are needed to make this action
  executable. -/
  extraParams : Array Parameter
  /-- DSL expression for the specification of this action -/
  spec : Option ActionSyntax
  /-- DSL expression for this action -/
  code : ActionSyntax
  /-- The user-written syntax that resulted in the declaration of this
  procedure. -/
  userSyntax : Syntax
deriving Inhabited, BEq

/-- Modules can depend on other modules, which must be
fully-instantiated with arguments provided for all the module
parameters. -/
structure ModuleDependency where
  /-- The name of the module that this module depends on. This is used
  to lookup the module in the global environment. -/
  name : Name
  /-- Modules can be referred to in the dependee by an alias. This
  allows multiple instantiations of child/depended on modules in a
  parent. -/
  alias : Option Name
  /-- Instantiations of the module's parameters, i.e. the arguments
  passed to the module when it is instantiated. -/
  arguments : Array Term
  /-- The user-written syntax that resulted in the declaration of this
  module dependency. -/
  userSyntax : Syntax
deriving Inhabited, BEq

inductive DerivedDefinitionKind where
  /-- This derived definition is like an `assumption`, in terms of the
  parameters it needs. -/
  | assumptionLike
  /-- This derived definition is like an `invariant`, in terms of the
  parameters it needs. -/
  | invariantLike
deriving Inhabited, BEq, Hashable

/-- A derived definition is not directly part of the module, but
programmatically generated/derived from some of the module's
definitions. Examples of this are `Invariants` and `Assumptions`. -/
structure DerivedDefinition where
  /-- The name of this definition in the Lean environment. -/
  name : Name
  /-- The kind of this derived definition. -/
  kind : DerivedDefinitionKind
  /-- Extra parameters this definition needs. -/
  extraParams : Array Parameter
  /-- The definitions that this derived definition depends on. -/
  derivedFrom : Std.HashSet Name
  /-- The syntax of the definition that was derived. -/
  stx : Command
deriving Inhabited

structure Module where
  /-- The name of the module -/
  name : Name
  /-- The parameters of the module -/
  parameters : Array Parameter
  /-- Modules that this module depends on (i.e. instantiates) -/
  dependencies : Array ModuleDependency
  /-- All constants, relations, and functions that compose the state.
  This basically defines a FOL signature. -/
  signature : Array StateComponent
  /-- Procedures of the system, some of which are marked as `action`s,
  i.e. procedures that can be called by the environment. One of these
  must be the `initializer` procedure. (A module can have only one
  initializer.) -/
  procedures : Array ProcedureSpecification
  /-- The assertions that this module makes -/
  assertions : Array StateAssertion

  /-- Implementation detail. Used to check that names are unique. -/
  protected _declarations : Std.HashSet Name

  /-- Derived definitions that this module has. -/
  protected _derivedDefinitions : Std.HashMap Name DerivedDefinition

  /-- Implementation detail. Whether the state (and background theory)
  of this module has been defined as a Lean `structure` definition.
  This is done explicitly by `#gen_state`, or implicitly when a
  `procedure`/`action` or assertion is defined. -/
  protected _stateDefined : Bool := false

  /-- Implementation detail. Whether the set of `procedures` and
  `assertions` has been fixed. This is done explicitly when `#gen_spec`
  is executed. Derived definitions can still be added after this. -/
  protected _specFinalized : Bool := false

  /-- Assertions can be grouped into "sets", which are checked
  independently of each other. Sets are per-module. By default, all
  assertions are added to the same set. -/
  protected _assertionSets : Std.HashMap Name (Std.HashSet Name) := Std.HashMap.emptyWithCapacity
deriving Inhabited

def Module.defaultAssertionSet (mod : Module) : Name := mod.name

end Veil
