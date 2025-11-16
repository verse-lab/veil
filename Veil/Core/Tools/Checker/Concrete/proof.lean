import Veil.Core.Tools.Checker.Concrete.State
import Veil.Core.Tools.Checker.Concrete.DataStructure

import Veil.Core.Semantics.TransitionSystem
/-

- `soundness`:
If the model checker reports a counterexample, then there exists a reachable
state from the initial state that violates the invariant.

- `completeness`:
If there exists a reachable counterexample, then the model checker will find it.
The completeness of the model checker is guaranteed via the `completeness` of
`VeilExecM`, i.e., we should extract all the `VeilExecM`.

-/

namespace Veil.Checker

variable {ℂ ℝ 𝔸 : Type}
variable {m : Mode}
variable {ρ σ α κ : Type}

/-! ## 1. Reachability Definition -/

/-- A state `s'` is reachable from state `s` in one step via label `label` -/
def oneStepReachable (nextExecM : κ → VeilExecM m ρ σ α)
(rd : ρ) (s : σ) (label : κ) (s' : σ) : Prop :=
  getStateFromExceptT (nextExecM label rd s) = some s'

/-- A state is reachable from an initial state via a sequence of labels -/
inductive Reachable (nextExecM : κ → VeilExecM m ρ σ α) (rd : ρ) : σ → List κ → σ → Prop where
  | refl (s : σ) : Reachable nextExecM rd s [] s
  | step {s s' s'' : σ} {label : κ} {labels : List κ} :
      Reachable nextExecM rd s labels s' →
      oneStepReachable nextExecM rd s' label s'' →
      Reachable nextExecM rd s (labels ++ [label]) s''

/-- Extending a reachability proof with one more step -/
theorem reachable_one_step
    {nextExecM : κ → VeilExecM m ρ σ α}
    {rd : ρ} {s₁ s₂ s₃ : σ} {path : List κ} {label : κ}
    (h_reach : Reachable nextExecM rd s₁ path s₂)
    (h_one : oneStepReachable nextExecM rd s₂ label s₃)
    : Reachable nextExecM rd s₁ (path ++ [label]) s₃ :=
  Reachable.step h_reach h_one

/-- Reachability is transitive -/
theorem reachable_trans {nextExecM : κ → VeilExecM m ρ σ α}
    {rd : ρ} {s₁ s₂ s₃ : σ} {path₁ path₂ : List κ}
    (h₁ : Reachable nextExecM rd s₁ path₁ s₂)
    (h₂ : Reachable nextExecM rd s₂ path₂ s₃)
    : Reachable nextExecM rd s₁ (path₁ ++ path₂) s₃ := by
  induction h₂ generalizing s₁ path₁ with
  | refl =>
    simp
    exact h₁
  | step h_rec h_one ih =>
    rw [← List.append_assoc]
    exact reachable_one_step (ih h₁) h_one
