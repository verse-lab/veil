
import Veil.Basic

/- ## Generic transition systems
  These can be either IO Automata or TLA-style relational transition systems. -/
class TransitionSystem
  /- Types of states and actions -/
  (σ : Type)
  (action : Type)

  /- Types of executions/traces/behaviours -/
  (exec : Type)

  /- Types of predicates over executions, states, and actions -/
  (pred : Type)
  (state_pred : (f : σ → Prop) → pred)
  (action_pred :  (a : action) → pred)

/- ## TLA-style transition systems -/
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

/-- The type of TLA-style actions -/
def action (σ : Type) := σ → σ → Prop
/-- The type of a predicate on TLA-style actions -/
def action_pred {σ : Type} (a : action σ) : pred σ :=
  λ e => a (e 0) (e 1)
notation "⟨" a "⟩" => action_pred a
end RelationalTransitionSystem

-- NOTE: if you change this, make sure you also change
-- `findStateType` in `Tactic/Util.lean`
class RelationalTransitionSystem (σ : Type) extends
  TransitionSystem σ
  (RelationalTransitionSystem.action σ)
  (RelationalTransitionSystem.exec σ)
  (RelationalTransitionSystem.pred σ)
  RelationalTransitionSystem.state_pred
  RelationalTransitionSystem.action_pred
  where
  init : σ → Prop
  assumptions : σ → Prop
  next : RelationalTransitionSystem.action σ
  safe : σ → Prop
  inv : σ → Prop

open RelationalTransitionSystem

/-- All states in the invariant are safe. -/
def invSafe [RelationalTransitionSystem σ] :=
  ∀ (s : σ), inv s -> safe s

/-- The set of initial states are in the invariant. -/
def invInit [RelationalTransitionSystem σ] :=
  ∀ (s : σ), init s -> inv s

/-- The invariant is preserved by transition. -/
def invConsecution [RelationalTransitionSystem σ] :=
  ∀ (s1 s2 : σ), next s1 s2 -> inv s1 -> inv s2

/-- The invariant is inductive. -/
def invInductive [sys: RelationalTransitionSystem σ] :=
  @invInit σ sys ∧ @invConsecution σ sys

def validStutteringExecution [RelationalTransitionSystem σ] (e : exec σ) :=
  init (e 0) ∧ ∀ (i : Nat), (next (e i) (e (i + 1))) ∨ (e i = e (i + 1))

/-- The set of all reachable states of the system. -/
def reachableStates [RelationalTransitionSystem σ] : σ → Prop :=
  (λ (s : σ) => ∃ (e : exec σ), validStutteringExecution e ∧ ∃ (step : Nat), s = e step)

theorem init_is_reachable [RelationalTransitionSystem σ] :
  ∀ (s : σ), init s -> reachableStates s := by
  intro s hinit; apply Exists.intro (λ _ => s)
  simp only [validStutteringExecution, or_true, implies_true, and_true, exists_const, hinit]

theorem valid_execution_in_inductive_inv [sys : RelationalTransitionSystem σ] (e : exec σ) :
  @invInductive σ sys → validStutteringExecution e → ∀ (i : Nat), inv (e i) := by
  intro ⟨h0, hinv⟩ hvalid i
  induction i with
  | zero => { apply h0; apply hvalid.left }
  | succ i ih => {
    rcases hvalid.right i with tr | stutter
    . apply (@hinv _ _ tr); apply ih
    . rw [stutter] at ih; apply ih
  }

/-- The inductive invariant is an over-approximation of the set of
reachable states. -/
theorem reachable_in_inductive_inv [sys : RelationalTransitionSystem σ] :
  @invInductive σ sys → ∀ (s : σ), reachableStates s → inv s := by
  intro hinv s ⟨exec, ⟨valid, ⟨i, hs⟩⟩⟩; subst s
  apply valid_execution_in_inductive_inv exec hinv valid i
