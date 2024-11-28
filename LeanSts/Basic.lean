/-
   Reasoning about transition systems in Lean.
   We have both relationally-defined and functionally-defined transition systems.
-/
import Lean

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

/-- A `Decidable` binary relation. -/
abbrev DecidableBinaryRel {α β : Sort u} (r : α → β → Prop) :=
  (a : α) → (b : β) → Decidable (r a b)

/-- A `Decidable` ternary relation. -/
abbrev DecidableTernaryRel {α β γ : Sort u} (r : α → β → γ → Prop) :=
  (a : α) → (b : β) → (c : γ) → Decidable (r a b c)

/-- Simplifiers to prepare a goal for SMT. See `SMT/Preparation.lean` -/
register_simp_attr smtSimp
/-- We specifically identify lemmas for quantifier elimination, since we run
  these in a loop and `smtSimp` is too large/expensive a set to run in a loop.
  See `SMT/Preparation.lean` -/
register_simp_attr quantifierElim
