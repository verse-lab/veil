
import Lean
import Lean.Parser

open Lean Lean.Parser


namespace Veil

section VeilKeywords

/- FIXME: Veil keywords introduce a reserved symbol, which means users of Veil
can't use them in their code.

See
[Naming conflict when defining a new syntax](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/.E2.9C.94.20Naming.20conflict.20when.20defining.20a.20new.20syntax)
thread on Zulip for more details, particularly
[this comment](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/.E2.9C.94.20Naming.20conflict.20when.20defining.20a.20new.20syntax/near/502658016).
Unfortunately, this means all our keywords (`veil`, `module,` `type`, etc.) are
reserved symbols, so users of Veil can't use them in their code. -/


declare_syntax_cat veilKeyword
syntax (name := kw_veil) "veil" : veilKeyword
syntax (name := kw_module) "module" : veilKeyword

scoped syntax (name := kw_type) "type" : veilKeyword
scoped syntax (name := kw_enum) "enum" : veilKeyword
scoped syntax (name := kw_param) "param" : veilKeyword
scoped syntax (name := kw_instantiate) "instantiate" : veilKeyword

scoped syntax (name := kw_immutable) "immutable" : veilKeyword
scoped syntax (name := kw_mutable) "mutable" : veilKeyword

scoped syntax (name := kw_individual) "individual" : veilKeyword
scoped syntax (name := kw_relation) "relation" : veilKeyword
scoped syntax (name := kw_function) "function" : veilKeyword

scoped syntax (name := kw_theory) "theory" : veilKeyword
scoped syntax (name := kw_ghost) "ghost" : veilKeyword

scoped syntax (name := kw_includes) "includes" : veilKeyword

scoped syntax (name := kw_as) "as" : veilKeyword

scoped syntax (name := kw_gen_state) "#gen_state" : veilKeyword

scoped syntax (name := kw_after_init) "after_init" : veilKeyword

scoped syntax (name := kw_transition) "transition" : veilKeyword
scoped syntax (name := kw_action) "action" : veilKeyword
scoped syntax (name := kw_procedure) "procedure" : veilKeyword

scoped syntax (name := kw_open_isolate) "open_isolate" : veilKeyword
scoped syntax (name := kw_close_isolate) "close_isolate" : veilKeyword

scoped syntax (name := kw_trusted) "trusted" : veilKeyword

scoped syntax (name := kw_assumption) "assumption" : veilKeyword
scoped syntax (name := kw_invariant) "invariant" : veilKeyword
scoped syntax (name := kw_safety) "safety" : veilKeyword
scoped syntax (name := kw_termination) "termination" : veilKeyword
scoped syntax (name := kw_state_constraint) "state_constraint" : veilKeyword

scoped syntax (name := kw_gen_spec) "#gen_spec" : veilKeyword

end VeilKeywords

/-!
  # Specification Language Syntax

  This file defines the syntax for the specification language, which is used to
  declare Veil modules.

-/
/-- Declare a Veil module.

Example:
```lean
veil module MyModule
  [module goes here]
end MyModule
```
-/
syntax (name := moduleDeclaration) atomic(kw_veil kw_module) ident : command


/-- Declare an uninterpreted type.

Example:
```lean
type node
```
-/
scoped syntax (name := typeDeclaration) kw_type ident : command

/--Declare an enum type.

Example:
```lean
enum switch_state = {on, off}
```
-/
scoped syntax (name := enumDeclaration) kw_enum ident "=" "{" ident,+ "}" : command

/-- Instantiate a typeclass instance.

Example:
```lean
instantiate tot : TotalOrder node
```
-/
scoped syntax (name := instanceDeclaration) kw_instantiate ident " : " term : command

/-- Declare an uninterpreted parameter of arbitrary type.
`type` is a special case of `param` (equivalent to `param name : Type`
plus auto-generated `DecidableEq` and `Inhabited` instances).
Dependencies between `param`s are allowed.

`param` is superficially similar to `immutable individual`, since both
introduce named *values*. However, there are important structural differences:

- **Structural role**: `param` values are universal parameters of `State`,
  `Theory`, and `Label` (like `type`). In contrast, `immutable` values are
  fields of the `Theory` structure.
- **Type dependency**: State components (mutable and immutable) can depend on
  `param`s in their types (e.g., `function f : node → Fin n` when
  `param n : Nat`). State component types cannot depend on `immutable` values.
- **Instantiation vs Theory**: `param` values are provided in the
  `Instantiation` structure (first argument of `#model_check`). `immutable`
  values are provided in the `Theory` term (second argument).
- **No auto-instances**: Unlike `type`, `param` does **NOT** auto-generate
  `DecidableEq` or `Inhabited` instances. In other words, `type` is `param name : Type`
  plus some instance declarations.

Example:
```lean
param n : Nat
param m : Fin n   -- dependent parameters allowed
```
-/
scoped syntax (name := parameterDeclaration) kw_param ident " : " term : command

/- ## State -/
declare_syntax_cat stateMutability

/-- This state component cannot be modified. If you have `immutable` state, you
typically want to make `assumption`s about it. -/
scoped syntax (name := immutableState) kw_immutable : stateMutability
/-- This state component can be modified. This is the default. -/
scoped syntax (name := mutableState) kw_mutable : stateMutability

declare_syntax_cat stateComponentKind

/-- A state component that is an individual value, e.g.
`individual currentRound : round`
-/
scoped syntax (name := individualStateComponent) kw_individual : stateComponentKind
/-- A state component that is a relation, e.g.
`relation initial_msg : address → address → round → value → Prop`

Relations can also be defined with names for the arguments, e.g.
`relation sent (n : address) (r : round)`
-/
scoped syntax (name := relationStateComponent) kw_relation : stateComponentKind

/-- A state component that is a function, e.g.
`function currentRound : address → round`

Functions can also be defined with names for the arguments, e.g.
`function currentRound (n : address) : round`
-/
scoped syntax (name := functionStateComponent) kw_function : stateComponentKind

/-- This state component is the state of another module. -/
scoped syntax (name := moduleStateComponent) kw_module : stateComponentKind

/-- Assemble the state type for this Veil module, based on the previously
declared state components. -/
scoped syntax (name := genState) "#gen_state" : command

/-- Declares a state component using the `[mut] [kind] name (args) : type` syntax. -/
scoped syntax (name := stateComponentDeclaration) (stateMutability)? stateComponentKind ident bracketedBinder* (":" term)? : command

/-- A module abbreviation, e.g. `as rb`. -/
syntax moduleAbbrev := (kw_as ident)

/-- Declare a dependency on another module. -/
scoped syntax (name := declareDependency) kw_includes ident term:max* moduleAbbrev : command

/- ## Ghost definitions -/

/-- Define a ghost relation. By default, `ghost relation`s depend on both the
background theory and the state. If you want to define a ghost relation that
only depends on the background theory, define a `theory ghost relation`. Example:

  ```lean
  ghost relation R (r : round) (v : value) := [definition]
  theory ghost relation V (v : value) := [definition]
  ```
-/
scoped syntax (name := ghostRelationDefinition) kw_theory ? kw_ghost kw_relation ident explicitBinders ? ":=" term : command

/-- Define a ghost function. Ghost functions are like ghost relations but can
return any type (not just `Prop`). An optional return type annotation is
supported. By default, ghost functions depend on both the background theory
and the state. Use `theory ghost function` for functions that depend only on
the background theory. Example:

  ```lean
  ghost function myFn (n : node) : SomeType := body
  ghost function myFn (n : node) := body
  theory ghost function myFn (n : node) : SomeType := body
  ```
-/
scoped syntax (name := ghostFunctionDefinition) kw_theory ? kw_ghost kw_function ident explicitBinders ? (":" term)? ":=" term : command

/- ## Initial state -/

/-- Define the initial state as an imperative program that executes on top of a
non-deterministic initial state. The initial state is given by the post-state
after executing `after_init` starting from the unspecified initial state. -/
scoped syntax (name := initializerDefinition) kw_after_init "{" doSeq "}" : command

/- ## Actions -/

/-- Transition defined via a Veil two-state relation, which implicitly has
access to the state variables. The post-state can be referred to with primed
variable names, e.g. `initial_msg'`.

Every variable that is not mentioned with its primed name is assumed to
be unchanged.

Example:

```lean
transition byz = {
  (∀ (src dst : node) (r : round) (v : value),
    (¬ is_byz src ∧ (initial_msg src dst r v ↔ initial_msg' src dst r v)) ∨
    (is_byz src ∧ (initial_msg src dst r v → initial_msg' src dst r v))) ∧
```
 -/
scoped syntax (name := transitionDefinition) (priority := high) kw_transition ident explicitBinders ? "{" term "}" : command

declare_syntax_cat procedureKind

scoped syntax (name := actionKind) kw_action : procedureKind
scoped syntax (name := procedureKind) kw_procedure : procedureKind

/-- An imperative `procedure` or `action` in Veil. -/
scoped syntax (name := procedureDefinition) procedureKind ident (explicitBinders)? "{" doSeq "}" : command

scoped syntax (name := procedureDefinitionWithSpec) procedureKind ident (explicitBinders)? doSeq "{" doSeq "}" : command

/- ## Assertions -/

declare_syntax_cat propertyName
scoped syntax (name := propertyName) "[" ident "]" : propertyName

scoped syntax (name := openIsolate) kw_open_isolate ident ("with" ident+)? : command
scoped syntax (name := closeIsolate) kw_close_isolate : command

declare_syntax_cat propertyTrustKind

/-- This property is assumed to hold. `assumption`s can only talk about
`immutable` state components, so if you want an 'assumption' about a `mutable`
state component, you must use `trusted invariant`. -/
scoped syntax (name := trustedProperty) kw_trusted : propertyTrustKind

declare_syntax_cat propertyKind

/-- An `assumption` is a background axiom. Assumptions can only refer to
`immutable` state components.

If you want to assume facts about `mutable` state components, use
`trusted invariant`. -/
scoped syntax (name := assumptionKind) kw_assumption : propertyKind

scoped syntax (name := trustedInvariantKind) kw_trusted kw_invariant : propertyKind

/-- An `invariant` is a property that we are asserting holds for all reachable
states of the system. Invariants can refer to both `immutable` and `mutable`
state components. -/
scoped syntax (name := invariantKind) kw_invariant : propertyKind

/-- `safety` is a synonym for `invariant`. As a co-/
scoped syntax (name := safetyKind) kw_safety : propertyKind

/--`termination` is also a synonym for `invariant`, but only used for model checker,
which would not be emitted to VC generator while verification. -/
scoped syntax (name := terminationKind) kw_termination : propertyKind

/-- A `state_constraint` filters out states during model checking.
States that do not satisfy the constraint are not explored. -/
scoped syntax (name := stateConstraintKind) kw_state_constraint : propertyKind

/-- An assertion. -/
scoped syntax (name := assertionDeclaration) propertyKind (propertyName)? term : command

/-- Assemble the specification. -/
scoped syntax (name := genSpec) kw_gen_spec : command

scoped syntax (name := checkInvariants) "#check_invariants" : command

scoped syntax (name := checkAction) "#check_action" ident : command

/-- Run the explicit state model checker on the current module with the given
type instantiation and theory. The optional `maxDepth` parameter limits how
deep the breadth-first search will go before terminating.

## Execution Modes

**Default behavior** (`#model_check`):
- Runs interpreted mode immediately and shows real-time progress
- Starts compilation in background
- When compilation finishes (if no violation found yet), automatically restarts
  with the compiled binary for faster execution

**Interpreted-only mode** (`#model_check interpreted`):
- Runs only interpreted mode without background compilation
- Use this when you don't need the compiled binary

Example:
```lean
#model_check { node := Fin 5 } {baaaa := fun _ _ => 0}
#model_check { node := Fin 5 } {baaaa := fun _ _ => 0} (maxDepth := 10)
#model_check { node := Fin 5 }  -- theory term can be omitted if there are no theory fields
#model_check interpreted { node := Fin 5 } {}  -- interpreted only, no compilation
```

This will check all invariants and terminate early if a violation is found or
the maximum depth is reached.

## Important: the model checker is not complete!

In its current implementation, the model checker DOES NOT enumerate all
possible theories and all possible instantiations of the type classes used. It
only uses the theory you explicitly provide and the default instances for the
type classes.

This means that it should only be used for testing. In the future, we will add
support for complete enumeration of background theories.
-/
declare_syntax_cat modelCheckMode
scoped syntax (name := interpreted) "interpreted" : modelCheckMode
scoped syntax (name := compiled) "compiled" : modelCheckMode

/-- Optional clause to check that the provided theory satisfies the module's
assumptions before model checking. `Assumptions` is automatically unfolded via
`dsimp` first; if no tactic is given, `first | decide | native_decide` is used. -/
syntax assumptionsHoldBy := "assumptions_hold_by " tacticSeq

scoped syntax (name := modelCheck) "#model_check " (modelCheckMode)? term:max (term:max)? Parser.Tactic.optConfig (assumptionsHoldBy)? : command

/-- Configure the concrete runtime representation for `relation` or `function` fields.
This command must be used before `#gen_state`.

Example:
```lean
veil_set_field_representation relation Std.ExtTreeSet
veil_set_field_representation function Std.ExtTreeMap
```
-/
declare_syntax_cat concreteRepField
scoped syntax (name := crRelation) kw_relation : concreteRepField
scoped syntax (name := crFunction) kw_function : concreteRepField

scoped syntax (name := concreteRepresentationDecl) "veil_set_field_representation " concreteRepField ident : command

end Veil
