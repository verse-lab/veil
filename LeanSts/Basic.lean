/-
   Reasoning about transition systems in Lean.
   We have both relationally-defined and functionally-defined transition systems.
-/

namespace RelationalTransitionSystem

/-- Executions are known as "behaviours" in TLA -/
def exec (σ : Type) := Nat → σ
def predicate (σ : Type) := exec σ → Prop

def state_pred {σ : Type} (f : σ → Prop) : predicate σ :=
  λ e => f (e 0)

notation "⌜" p "⌝" => state_pred p

def action (σ : Type) := σ → σ → Prop
def action_pred {σ : Type} (a : action σ) : predicate σ :=
  λ e => a (e 0) (e 1)

notation "⟨" a "⟩" => action_pred a

end RelationalTransitionSystem


namespace FunctionalTransitionSystem

def exec := RelationalTransitionSystem.exec
def predicate := RelationalTransitionSystem.predicate

def state_pred {σ : Type} := @RelationalTransitionSystem.state_pred σ
/-- NOTE: this is a function, not a relation. -/
def action {σ : Type} := σ → σ

end FunctionalTransitionSystem
