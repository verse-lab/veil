
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

syntax (name := kw_type) "type" : veilKeyword
syntax (name := kw_enum) "enum" : veilKeyword
syntax (name := kw_instantiate) "instantiate" : veilKeyword

syntax (name := kw_immutable) "immutable" : veilKeyword
syntax (name := kw_mutable) "mutable" : veilKeyword

syntax (name := kw_individual) "individual" : veilKeyword
syntax (name := kw_relation) "relation" : veilKeyword
syntax (name := kw_function) "function" : veilKeyword

syntax (name := kw_theory) "theory" : veilKeyword
syntax (name := kw_ghost) "ghost" : veilKeyword

syntax (name := kw_includes) "includes" : veilKeyword

syntax (name := kw_as) "as" : veilKeyword

syntax (name := kw_gen_state) "#gen_state" : veilKeyword

syntax (name := kw_after_init) "after_init" : veilKeyword

syntax (name := kw_transition) "transition" : veilKeyword
syntax (name := kw_action) "action" : veilKeyword
syntax (name := kw_procedure) "procedure" : veilKeyword

syntax (name := kw_open_isolate) "open_isolate" : veilKeyword
syntax (name := kw_close_isolate) "close_isolate" : veilKeyword

syntax (name := kw_trusted) "trusted" : veilKeyword

syntax (name := kw_assumption) "assumption" : veilKeyword
syntax (name := kw_invariant) "invariant" : veilKeyword
syntax (name := kw_safety) "safety" : veilKeyword

syntax (name := kw_gen_spec) "#gen_spec" : veilKeyword

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
syntax (name := typeDeclaration) kw_type ident : command

/--Declare an enum type.

Example:
```lean
enum switch_state = {on, off}
```
-/
syntax (name := enumDeclaration) kw_enum ident "=" "{" ident,+ "}" : command

/-- Instantiate a typeclass instance.

Example:
```lean
instantiate tot : TotalOrder node
```
-/
syntax (name := instanceDeclaration) kw_instantiate ident " : " term : command

/- ## State -/
declare_syntax_cat stateMutability

/-- This state component cannot be modified. If you have `immutable` state, you
typically want to make `assumption`s about it. -/
syntax (name := immutableState) kw_immutable : stateMutability
/-- This state component can be modified. This is the default. -/
syntax (name := mutableState) kw_mutable : stateMutability

declare_syntax_cat stateComponentKind

/-- A state component that is an individual value, e.g.
`individual currentRound : round`
-/
syntax (name := individualStateComponent) kw_individual : stateComponentKind
/-- A state component that is a relation, e.g.
`relation initial_msg : address → address → round → value → Prop`

Relations can also be defined with names for the arguments, e.g.
`relation sent (n : address) (r : round)`
-/
syntax (name := relationStateComponent) kw_relation : stateComponentKind

/-- A state component that is a function, e.g.
`function currentRound : address → round`

Functions can also be defined with names for the arguments, e.g.
`function currentRound (n : address) : round`
-/
syntax (name := functionStateComponent) kw_function : stateComponentKind

/-- This state component is the state of another module. -/
syntax (name := moduleStateComponent) kw_module : stateComponentKind

/-- Inline Lean's built-in `structure` and `inductive` definitions in module. -/
syntax (name := inlineBuiltinDeclaration) "@[veil_decl]" command : command

/-- Assemble the state type for this Veil module, based on the previously
declared state components. -/
syntax (name := genState) "#gen_state" : command

/-- Declares a state component using the `[mut] [kind] name (args) : type` syntax. -/
syntax (name := stateComponentDeclaration) (stateMutability)? stateComponentKind ident bracketedBinder* (":" term)? : command

/-- A module abbreviation, e.g. `as rb`. -/
syntax moduleAbbrev := (kw_as ident)

/-- Declare a dependency on another module. -/
syntax (name := declareDependency) kw_includes ident term:max* moduleAbbrev : command

/- ## Ghost relations -/

/-- Define a ghost relation. By default, `ghost relation`s depend on both the
background theory and the state. If you want to define a ghost relation that
only depends on the background theory, define a `theory ghost relation`. Example:

  ```lean
  ghost relation R (r : round) (v : value) := [definition]
  theory ghost relation V (v : value) := [definition]
  ```
-/
syntax (name := ghostRelationDefinition) kw_theory ? kw_ghost kw_relation ident explicitBinders ? ":=" term : command

/- ## Initial state -/

/-- Define the initial state as an imperative program that executes on top of a
non-deterministic initial state. The initial state is given by the post-state
after executing `after_init` starting from the unspecified initial state. -/
syntax (name := initializerDefinition) kw_after_init "{" doSeq "}" : command

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
syntax (name := transitionDefinition) (priority := high) kw_transition ident explicitBinders ? "{" term "}" : command

declare_syntax_cat procedureKind

syntax (name := actionKind) kw_action : procedureKind
syntax (name := procedureKind) kw_procedure : procedureKind

/-- An imperative `procedure` or `action` in Veil. -/
syntax (name := procedureDefinition) procedureKind ident (explicitBinders)? "{" doSeq "}" : command

syntax (name := procedureDefinitionWithSpec) procedureKind ident (explicitBinders)? doSeq "{" doSeq "}" : command

/- ## Assertions -/

declare_syntax_cat propertyName
syntax (name := propertyName) "[" ident "]" : propertyName

syntax (name := openIsolate) kw_open_isolate ident ("with" ident+)? : command
syntax (name := closeIsolate) kw_close_isolate : command

declare_syntax_cat propertyTrustKind

/-- This property is assumed to hold. `assumption`s can only talk about
`immutable` state components, so if you want an 'assumption' about a `mutable`
state component, you must use `trusted invariant`. -/
syntax (name := trustedProperty) kw_trusted : propertyTrustKind

declare_syntax_cat propertyKind

/-- An `assumption` is a background axiom. Assumptions can only refer to
`immutable` state components.

If you want to assume facts about `mutable` state components, use
`trusted invariant`. -/
syntax (name := assumptionKind) kw_assumption : propertyKind

syntax (name := trustedInvariantKind) kw_trusted kw_invariant : propertyKind

/-- An `invariant` is a property that we are asserting holds for all reachable
states of the system. Invariants can refer to both `immutable` and `mutable`
state components. -/
syntax (name := invariantKind) kw_invariant : propertyKind

/-- `safety` is a synonym for `invariant`. As a co-/
syntax (name := safetyKind) kw_safety : propertyKind

/--`termination` is also a synonym for `invariant`, but only used for model checker,
which would not be emitted to VC generator while verification. -/
syntax (name := terminationKind) "termination" : propertyKind

/-- An assertion. -/
syntax (name := assertionDeclaration) propertyKind (propertyName)? term : command

/-- Assemble the specification. -/
syntax (name := genSpec) kw_gen_spec : command

declare_syntax_cat checkInvariantsCmd

syntax (name := checkInvariantsNormal) "#check_invariants" : checkInvariantsCmd
syntax (name := checkInvariantsWithSuggestions) "#check_invariants?" : checkInvariantsCmd
syntax (name := checkInvariantsUndischarged) "#check_invariants!" : checkInvariantsCmd

syntax (name := checkInvariants) checkInvariantsCmd : command

/-- Run the explicit state model checker on the current module with the given
type instantiation and theory. The optional `maxDepth` parameter limits how
deep the breadth-first search will go before terminating.

Example:
```lean
#model_check { node := Fin 5 } {baaaa := fun _ _ => 0}
#model_check { node := Fin 5 } {baaaa := fun _ _ => 0} (maxDepth := 10)
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
syntax (name := modelCheck) "#model_check " term:max term:max Parser.Tactic.optConfig : command

end Veil
