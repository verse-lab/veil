/-
   Reasoning about transition systems in Lean.
   We have both relationally-defined and functionally-defined transition systems.
-/

namespace RelationalTransitionSystem

/-- The type of an execution.
    Executions are known as "behaviours" in TLA. -/
def exec (σ : Type) := Nat → σ
/-- The type of predicates on executions -/
def pred (σ : Type) := exec σ → Prop

/-- The type of a predicate on states -/
def state_pred {σ : Type} (f : σ → Prop) : pred σ :=
  λ e => f (e 0)
notation "⌜" p "⌝" => state_pred p

/-- The type of actions -/
def action (σ : Type) := σ → σ → Prop
/-- The type of a predicate on actions -/
def action_pred {σ : Type} (a : action σ) : pred σ :=
  λ e => a (e 0) (e 1)
notation "⟨" a "⟩" => action_pred a

end RelationalTransitionSystem


namespace FunctionalTransitionSystem

/-- The type of an execution. -/
def exec := RelationalTransitionSystem.exec
/-- The type of predicates on executions -/
def pred := RelationalTransitionSystem.pred

/-- The type of a predicate on states -/
def state_pred {σ : Type} := @RelationalTransitionSystem.state_pred σ
notation "⌜" p "⌝" => state_pred p

/-- The type of actions.
    NOTE: this is a function, not a relation. -/
def action {σ : Type} := σ → σ
/-- The type of a predicate on actions -/
def action_pred {σ : Type} (a : @action σ) : pred σ :=
  λ e => a (e 0) = (e 1)
notation "⟨" a "⟩" => action_pred a

end FunctionalTransitionSystem
