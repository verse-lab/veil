import Veil.DSL.Base
import Loom.MonadAlgebras.NonDetT'.Extract

/-!
  # Action Language

  This file defines the semantics for the imperative language we use to
  define initializers and actions.
-/
section Veil
open Classical
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

instance : ToString Mode where
  toString := fun m => match m with
  | .internal => "internal"
  | .external => "external"

abbrev ExId := Int

abbrev SProp (ρ σ : Type) := ρ -> σ -> Prop
abbrev RProp (α ρ σ : Type) := α -> SProp ρ σ

/-! Our language is parametric over the mutable state, immutable state, and return type. -/
set_option linter.unusedVariables false in
abbrev VeilExecM (m : Mode) (σ ρ α : Type) := ReaderT ρ (StateT σ (ExceptT ExId DivM)) α
abbrev VeilM (m : Mode) (σ ρ α : Type) := NonDetT (VeilExecM m σ ρ) α

abbrev VeilSpecM (σ ρ α : Type) := Cont (SProp ρ σ) α

abbrev BigStep (ρ σ α : Type) := ρ -> σ -> α -> σ -> Prop
abbrev TwoState (ρ σ : Type) := ρ -> σ -> σ -> Prop

end Types

/-! ## Theory  -/
section Theory


macro "[DemonSucc|" t:term "]" : term =>  `(open PartialCorrectness DemonicChoice ExceptionAsSuccess in $t)
macro "[DemonFail|" t:term "]" : term =>  `(open PartialCorrectness DemonicChoice ExceptionAsFailure in $t)
macro "[AngelFail|" t:term "]" : term =>  `(open TotalCorrectness AngelicChoice ExceptionAsFailure in $t)
macro "[CanRaise" ex:term "|" t:term "]" : term =>  `(open PartialCorrectness DemonicChoice in let _ : IsHandler (ε := ExId) $ex := ⟨⟩; $t)

variable {m : Mode} {σ ρ α : Type}

section WeakestPreconditionsSemantics

def VeilM.succesfullyTerminates (act : VeilM m σ ρ α) (pre : SProp ρ σ) : Prop :=
  [DemonFail| triple pre act ⊤]

def VeilM.preservesInvariantsOnSuccesful (act : VeilM m σ ρ α) (inv : SProp ρ σ) : Prop :=
  [DemonSucc| triple inv act (fun _ => inv)]

def VeilM.succeedsAndPreservesInvariants (act : VeilM m σ ρ α) (inv : SProp ρ σ) : Prop :=
  [DemonFail| triple inv act (fun _ => inv)]

def VeilM.assumptions (act : VeilM m σ ρ α) (ex : ExtractNonDet WeakFindable act) : SProp ρ σ :=
  [DemonFail| ex.prop]

abbrev VeilM.choices (act : VeilM m σ ρ α) := ExtractNonDet WeakFindable act

noncomputable
def VeilM.run (act : VeilM m σ ρ α) (chs : act.choices) : VeilExecM m σ ρ α :=
  act.runWeak chs

end WeakestPreconditionsSemantics

section TwoStateSemantics

def VeilSpecM.toTwoState (spec : VeilSpecM σ ρ α) : TwoState ρ σ :=
  fun r₀ s₀ s₁ => spec (fun _ r s => r = r₀ ∧ s = s₁) r₀ s₀

def VeilM.toTwoState (act : VeilM m σ ρ α) : TwoState ρ σ :=
  fun r₀ s₀ s₁ =>
    [AngelFail| triple (fun r s => r = r₀ ∧ s = s₀) act (fun _ r s => r = r₀ ∧ s = s₁)]

def TwoState.triple (act : TwoState ρ σ) (pre : SProp ρ σ) (post : SProp ρ σ) : Prop :=
  ∀ r₀ s₀ s₁,
    pre r₀ s₀ ->
    act r₀ s₀ s₁ ->
    post r₀ s₁

def TwoState.preservesInvariantsOnSuccesful (act : TwoState ρ σ) (inv : SProp ρ σ) : Prop :=
  act.triple inv inv

end TwoStateSemantics

section OperationalSemantics

def VeilExecM.operational (act : VeilExecM m σ ρ α) (r₀ : ρ) (s₀ : σ) (res : Except ExId σ) : Prop :=
  match act r₀ s₀ with
  | .div => False
  | .res (.error i)   => res = .error i
  | .res (.ok (_, s)) => res = .ok s

def VeilExecM.axiomatic (act : VeilExecM m σ ρ α) (r₀ : ρ) (s₀ : σ) (post : RProp α ρ σ) : Prop :=
  match act r₀ s₀ with
  | .div => False
  | .res (.error _) => False
  | .res (.ok (a, s)) => post a r₀ s

def VeilExecM.operationalTriple (act : VeilExecM m σ ρ α) (pre : SProp ρ σ) (post : SProp ρ σ) : Prop :=
  ∀ r₀ s₀ res,
    pre r₀ s₀ ->
    act.operational r₀ s₀ res ->
    match res with
    | .ok s₁ => post r₀ s₁
    | .error _ => False


end OperationalSemantics

section DerivingSemantics

def VeilM.canRaise (ex : Set ExId) (act : VeilM m σ ρ α) (pre : SProp ρ σ) : Prop :=
  [CanRaise ex| triple pre act (fun _ => ⊤)]

def VeilSpecM.toTwoStateDerived (spec : VeilSpecM σ ρ α) : TwoState ρ σ :=
  fun r₀ s₀ s₁ => spec.inv (fun _ r s => r = r₀ ∧ s = s₁) r₀ s₀


def VeilM.toTwoStateDerived (act : VeilM m σ ρ α) : TwoState ρ σ :=
  [CanRaise (fun _ => True)| VeilSpecM.toTwoStateDerived <| wp act]

end DerivingSemantics
