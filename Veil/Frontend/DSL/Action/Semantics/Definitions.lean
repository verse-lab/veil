import Loom.MonadAlgebras.NonDetT'.Extract
import Loom.MonadAlgebras.NonDetT'.ExtractList
import Veil.Frontend.DSL.State.SubState

/-!
  # Action Language

  This file defines the semantics for the imperative language we use to
  define initializers and actions.
-/

namespace Veil

/-! ## Types  -/
section Types
/-- Actions in Veil can be elaborated in two ways:

- `internal`: when we call an action, callee should ensure all
`require`s are satisfied. That is, under this interpretation, `require
P` is equivalent to `assert P`.

- `external`: when we call an action, it's the environment's
responsibility to ensure `require`s are satisfied. We treat `require`s
as `assume`s under this interpretation. Only top-level actions should
be interpreted as `external`.

See the definition of `Wp.require`.
-/
inductive Mode where
  | internal : Mode
  | external : Mode
deriving BEq

-- abbrev ExId := Int
-- workaround for [lean-smt#185](https://github.com/ufmg-smite/lean-smt/issues/185)
macro "ExId" : term => `($(Lean.mkIdent ``Int))

/-- A predicate on the theory and the mutable state. -/
abbrev SProp (ρ σ : Type) := ρ -> σ -> Prop
/-- A predicate on the theory, the post-state, and the result of an action.-/
abbrev RProp (α ρ σ : Type) := α -> SProp ρ σ

/-! Our language is parametric over the mutable state, immutable state, and return type. -/
set_option linter.unusedVariables false in
/-- Executable semantics of _deterministic_ Veil actions. -/
abbrev VeilExecM (m : Mode) (ρ σ α : Type) := ReaderT ρ (StateT σ (ExceptT ExId DivM)) α
/-- Denotation of _non-deterministic_ Veil actions. -/
abbrev VeilM (m : Mode) (ρ σ α : Type) := NonDetT (VeilExecM m ρ σ) α
/-- Executable semantics of _non-deterministic_ Veil actions, which works by
returning a _list_ of all possible results (either exceptions or post-states &
return values). -/
abbrev VeilMultiExecM κ ε ρ σ α :=
  ReaderT ρ (StateT σ (TsilT (ExceptT ε (PeDivM (List κ))))) α

abbrev VeilSpecM (ρ σ α : Type) := Cont (SProp ρ σ) α
abbrev Transition (ρ σ : Type) := ρ -> σ -> σ -> Prop

end Types

/-! ## Theory  -/
section Theory

/-!
  There are four different ways we interpret `VeilM` `action`s:
-/

/--
  `DemonSucc` is what we use to verify that invariants are preserved.
  Veil `action`s are atomic, with the semantics that if an exception is
  thrown, then all intermediate changes to the state are discarded.
  This also means that non-terminating actions have no visible effect.
  Therefore, assuming the invariant holds in the pre-state, it is
  preserved by the action IF either (a) the action does not terminate,
  or (b) the action throws an exception, or (c) the action terminates
  without throwing an exception and the invariant holds in the
  post-state. That's what `PartialCorrectness DemonicChoice
  ExceptionAsSuccess` encodes.
-/
macro "[DemonSucc|" t:term "]" : term =>  `(open PartialCorrectness DemonicChoice ExceptionAsSuccess in $t)

/--
  Of course, the actual thing we want to verify is that:
  (a) the action NEVER throws an exception, and
  (b) it preserves the invariant

  This is what the `DemonFail` semantics encodes. However, in practice,
  we don't check this directly, but rather obtain it by a combination
  of `DemonSucc` and `IgnoreEx`, i.e. we check (a) and (b) separately.
-/
macro "[DemonFail|" t:term "]" : term =>  `(open PartialCorrectness DemonicChoice ExceptionAsFailure in $t)

/--
  `AngelFail` corresponds to the "transition" semantics of `action`s,
  i.e. an action "can happen" if there EXISTS a way of making the
  non-deterministic choices such that the action terminates without
  exceptions being thrown.
-/
macro "[AngelFail|" t:term "]" : term =>  `(open TotalCorrectness AngelicChoice ExceptionAsFailure in $t)

/--
  Our most general semantics is `IgnoreEx`, which is parametrised by a
  set of exceptions `ExId → Prop` which the program can throw WITHOUT
  that implying a failure (i.e. ignore).

  Exception as success: `λ _ => ⊤`
  Exception as failure: `λ _ => ⊥`

  Moreover, for a particular exception ID `ex`, `λ e => e ≠ ex` gives a
  semantics such that the program fails IF the particular exception
  `ex` can be violated in any execution. We use this to discover which
  exceptions might be violated in an action and highlight them in the
  IDE.

  Finally, `IgnoreEx` can be used to derive the other three semantics
  we have by setting the set of exceptions appropriately (for
  `DemonFail` and `DemonSucc`) or by double-negating `DemonSucc` (to
  obtain `AngelFail`).
-/
macro "[IgnoreEx" ex:term "|" t:term "]" : term =>  `(open PartialCorrectness DemonicChoice in let _ : IsHandler (ε := ExId) $ex := ⟨⟩; $t)

variable {m : Mode} {ρ σ α : Type}

section WeakestPreconditionsSemantics

/-- The weakest precondition for an action that, given a precondition,
always succeeds (doesn't throw an exception) and meets the
post-condition. -/
@[reducible]
def VeilM.succeedsAndMeetsSpecification (act : VeilM m ρ σ α) (pre : SProp ρ σ) (post : RProp α ρ σ) : Prop :=
  [DemonFail| triple pre act post]

/-- There is no code path that throws an exception. -/
@[reducible]
def VeilM.doesNotThrow (act : VeilM m ρ σ α) (pre : SProp ρ σ) : Prop :=
  VeilM.succeedsAndMeetsSpecification act pre ⊤

@[reducible]
def VeilM.doesNotThrowAssuming (act : VeilM m ρ σ α) (assu : ρ → Prop) (pre : SProp ρ σ) : Prop :=
  VeilM.succeedsAndMeetsSpecification act (fun th st => assu th ∧ pre th st) ⊤

@[reducible]
def VeilM.succeedsAndPreservesInvariants (act : VeilM m ρ σ α) (inv : SProp ρ σ) : Prop :=
  VeilM.succeedsAndMeetsSpecification act inv (fun _ => inv)

@[reducible]
def VeilM.succeedsAndPreservesInvariantsAssuming (act : VeilM m ρ σ α) (assu : ρ → Prop) (inv : SProp ρ σ) : Prop :=
  VeilM.succeedsAndMeetsSpecification act (fun th st => assu th ∧ inv th st) (fun _ => inv)

/-- The weakest precondition for an action that, given a precondition,
_IF_ it succeeds (doesn't throw an exception), then it meets the
post-condition. -/
abbrev VeilM.meetsSpecificationIfSuccessful (act : VeilM m ρ σ α) (pre : SProp ρ σ) (post : RProp α ρ σ) : Prop :=
  [DemonSucc| triple pre act post]

@[reducible]
def VeilM.preservesInvariantsIfSuccesful (act : VeilM m ρ σ α) (inv : SProp ρ σ) : Prop :=
  VeilM.meetsSpecificationIfSuccessful act inv (fun _ => inv)

@[reducible]
def VeilM.meetsSpecificationIfSuccessfulAssuming (act : VeilM m ρ σ α) (assu : ρ → Prop) (pre post : SProp ρ σ) : Prop :=
  VeilM.meetsSpecificationIfSuccessful act (fun th st => assu th ∧ pre th st) (fun _ => post)

@[reducible]
def VeilM.preservesInvariantsIfSuccessfulAssuming (act : VeilM m ρ σ α) (assu : ρ → Prop) (inv : SProp ρ σ) : Prop :=
  VeilM.meetsSpecificationIfSuccessful act (fun th st => assu th ∧ inv th st) (fun _ => inv)

abbrev VeilM.choices (act : VeilM m ρ σ α) := ExtractNonDet WeakFindable act

noncomputable def VeilM.run (act : VeilM m ρ σ α) (chs : act.choices) : VeilExecM m ρ σ α := act.runWeak chs

end WeakestPreconditionsSemantics

section TransitionSemantics

def VeilSpecM.toTransition (spec : VeilSpecM ρ σ α) : Transition ρ σ :=
  fun r₀ s₀ s₁ => spec (fun _ r s => r = r₀ ∧ s = s₁) r₀ s₀

def VeilM.toTransition (act : VeilM m ρ σ α) : Transition ρ σ :=
  fun r₀ s₀ s₁ =>
    [AngelFail| triple (fun r s => r = r₀ ∧ s = s₀) act (fun _ r s => r = r₀ ∧ s = s₁)]

def Transition.triple (act : Transition ρ σ) (pre : SProp ρ σ) (post : SProp ρ σ) : Prop :=
  ∀ r₀ s₀ s₁,
    pre r₀ s₀ ->
    act r₀ s₀ s₁ ->
    post r₀ s₁

abbrev Transition.meetsSpecificationIfSuccessful (act : Transition ρ σ) (pre : SProp ρ σ) (post : SProp ρ σ) : Prop :=
  Transition.triple act pre post

def Transition.preservesInvariantsIfSuccesful (act : Transition ρ σ) (inv : SProp ρ σ) : Prop :=
  Transition.meetsSpecificationIfSuccessful act inv inv

end TransitionSemantics

section ExecutableSemantics

def VeilExecM.operational (act : VeilExecM m ρ σ α) (r₀ : ρ) (s₀ : σ) (s₁ : σ) (res : Except ExId α) : Prop :=
  match act r₀ s₀ with
  | .div => False
  | .res (.error i)   => res = .error i ∧ /- can be anything -/ s₁ = s₀
  | .res (.ok (a, s)) => res = .ok a ∧ s = s₁

def VeilExecM.axiomatic (act : VeilExecM m ρ σ α) (r₀ : ρ) (s₀ : σ) (post : RProp α ρ σ) : Prop :=
  match act r₀ s₀ with
  | .div => False
  | .res (.error _) => False
  | .res (.ok (a, s)) => post a r₀ s

def VeilExecM.operationalTriple (act : VeilExecM m ρ σ α) (pre : SProp ρ σ) (post : RProp α ρ σ) : Prop :=
  ∀ r₀ s₀ s₁ res,
    pre r₀ s₀ ->
    act.operational r₀ s₀ s₁ res ->
    match res with
    | .ok a => post a r₀ s₁
    | .error _ => False

end ExecutableSemantics

section DerivingSemantics


/-- Does `act` terminate successfully if the set `ex` of exceptions is
ignored / allowed to be thrown? -/
def VeilM.succeedsWhenIgnoring (ex : Set ExId) (act : VeilM m ρ σ α) (pre : SProp ρ σ) : Prop :=
  [IgnoreEx ex| triple pre act (fun _ => ⊤)]

def VeilSpecM.toTransitionDerived (spec : VeilSpecM ρ σ α) : Transition ρ σ :=
  fun r₀ s₀ s₁ => spec.inv (fun _ r s => r = r₀ ∧ s = s₁) r₀ s₀

def VeilM.toTransitionDerived (act : VeilM m ρ σ α) : Transition ρ σ :=
  [IgnoreEx (fun _ => True)| VeilSpecM.toTransitionDerived <| wp act]

/--
We don't use the simpler definition:
```lean4
let st' ← pick σ
assume (tr (← read) (← get) st')
set st'
```
because that would entail enumerating all environments via `(← get)`, which is
not possible in general. Instead, we structure the definition to only enumerate
all possible states of the system.

This is still VERY slow when doing explicit state model checking, though.
Eventually, we will need to come up with a better execution strategy, similar
to what TLC does: it "recovers" imperative assignments from two-state
transitions.
-/
def Transition.toVeilM [x :IsSubStateOf σ σ'] (tr : Transition ρ σ') : VeilM m ρ σ' Unit := do
  let st : σ' ← MonadStateOf.get
  let newSt ← pick σ
  let st' := setIn newSt st
  assume (tr (← read) st st')
  set st'

end DerivingSemantics

end Theory

end Veil
