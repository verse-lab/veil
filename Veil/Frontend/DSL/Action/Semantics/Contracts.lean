module

public import Veil.Frontend.DSL.Action.Semantics.Theorems

public section

namespace Veil

/-- A proved overapproximation of a particular concrete transition, under
explicit entry premises. The guarantee may combine postconditions and semantic
frames. Its type retains the concrete action and every occurrence binding. -/
structure TransitionSummary (concrete : Transition ρ σ)
    (precondition : SProp ρ σ) (guarantee : Transition ρ σ) : Prop where
  sound : ∀ th before after,
    precondition th before → concrete th before after → guarantee th before after

/-- Apply a certified summary while leaving the concrete verification
condition unchanged. The client proof mentions only the guarantee, and must
establish every entry premise of its provider certificate. -/
theorem TransitionSummary.preserves
    {concrete : Transition ρ σ} {precondition : SProp ρ σ}
    {guarantee : Transition ρ σ}
    (certificate : TransitionSummary concrete precondition guarantee)
    (assumptions : ρ → Prop) (invariants target : SProp ρ σ)
    (entry : ∀ th before, assumptions th → invariants th before → precondition th before)
    (stable : ∀ th before after, assumptions th → invariants th before →
      guarantee th before after → target th after) :
    concrete.meetsSpecificationIfSuccessfulAssuming assumptions invariants target := by
  intro th before after hpre hstep
  exact stable th before after hpre.1 hpre.2
    (certificate.sound th before after (entry th before hpre.1 hpre.2) hstep)

/-- Assertion freedom accompanies a successful-step summary. A false checked
ensure can remove successful transitions, so successful-step inclusion alone
must never be mistaken for an implementation certificate. -/
structure ActionSummary (act : VeilM m ρ σ α)
    (precondition : SProp ρ σ) (guarantee : Transition ρ σ) : Prop where
  doesNotThrow : act.doesNotThrow precondition
  transitions : TransitionSummary act.toTransitionDerived precondition guarantee

/-- An internal procedure contract keeps its actual result and its invocation
entry state. Owner invariants and other premises must be written in `precondition`;
none are supplied by this definition. -/
structure ProcedureContract (proc : VeilM .internal ρ σ α)
    (precondition : SProp ρ σ) (postcondition : σ → RProp α ρ σ) : Prop where
  checked : ∀ before, proc.succeedsAndMeetsSpecification
    (fun th state => precondition th state ∧ state = before) (postcondition before)

end Veil
