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
  /-- Set of isolates that were open when this invariant was defined -/
  isolates : List Name := []
  /-- Lean term for this predicate -/
  term : Option Term
  /-- Lean `Expr` for this predicate; this is usually a constant in the
  environment, *without* having applied the section variables. -/
  expr : Expr
deriving Inhabited, BEq

/-! ## Procedure and actions

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

/-- This is an implementation detail of the DSL, used to construct the
`Label` type for specifications, which has as constructors every
possible transition of the system described by this Veil module. -/
structure ProcedureDeclaration where
  name: ProcedureIdentifier
  ctor : Option (TSyntax ``Lean.Parser.Command.ctor)
deriving Inhabited, BEq

abbrev ActionDeclaration := ProcedureDeclaration

inductive ProcedureInfo
  /-- A procedure that is called by the environment to initialize the module. -/
  | initializer
  /-- Callable by the environment -/
  | action (decl : ActionDeclaration)
  /-- Not callable by the environment -/
  | procedure (decl : ProcedureDeclaration)
deriving Inhabited, BEq

abbrev ActionSyntax := TSyntax ``Term.doSeq

structure ProcedureSpecification where
  /-- Is this an `action` or a `procedure`? And what is its declaration? -/
  info : ProcedureInfo
  /-- DSL expression for this action -/
  lang : ActionSyntax
  /-- DSL expression for the specificarion of this action -/
  spec : Option ActionSyntax
  /-- Arguments of the current action -/
  br   : Option (TSyntax ``Lean.explicitBinders) := none
deriving Inhabited, BEq

inductive TypeclassAssumptionKind where
  /-- A typeclass assumption that is needed for the module to be
  well-defined. An example is the `Nonempty` assumption we make about
  sorts, which is needed for the translation to SMT to be sound. -/
  | alwaysRequired
  /-- A typeclass assumption that is needed to execute the module's
  actions. Examples: uninterpreted sorts must have `DecidableEq`, and
  relations must be `DecidableRel`. Also, sorts which are quantified
  over in the module's procedures must be `FinEnum`. -/
  | requiredForExecution
deriving Inhabited, BEq

inductive ParameterKind where
  /-- A (FOL) sort, i.e. a Lean type. The `sort` parameters are those that
  are used to declare the `State` type of the module. -/
  | uninterpretedSort
  /-- The type of the state of the _environment_ that this module
  operates in. The module's own state with be a sub-state of this. -/
  | environmentState -- i.e. `σ`
  /-- The background theory of the environment that this module
  operates in. The module's own background theory will be a sub-state
  of this.-/
  | backgroundTheory -- i.e. `ρ`
  /-- A typeclass assumption this module makes -/
  | moduleTypeclass (k : TypeclassAssumptionKind)
  /-- A typeclass assumption that _this definition_ makes. These are
  typically `Decidable` instances. -/
  | definitionTypeclass (defName : Name) (k : TypeclassAssumptionKind)
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
deriving Inhabited, BEq

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
deriving Inhabited

end Veil
