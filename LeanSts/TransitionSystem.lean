
import LeanSts.Basic

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


class RelationalTransitionSystem (σ : Type) extends
  TransitionSystem σ
  (RelationalTransitionSystem.action σ)
  (RelationalTransitionSystem.exec σ)
  (RelationalTransitionSystem.pred σ)
  RelationalTransitionSystem.state_pred
  RelationalTransitionSystem.action_pred
  where
  init : σ → Prop
  next : RelationalTransitionSystem.action σ
  -- safety : σ → Prop
  inv : σ → Prop

open RelationalTransitionSystem

def inv_init [RelationalTransitionSystem σ] :=
  ∀ (s : σ), init s -> inv s

def inv_inductive [RelationalTransitionSystem σ] :=
  ∀ (s1 s2 : σ), next s1 s2 -> inv s1 -> inv s2


class FunctionalTransitionSystem (σ : Type) extends
  TransitionSystem σ
  FunctionalTransitionSystem.action
  (FunctionalTransitionSystem.exec σ)
  (FunctionalTransitionSystem.pred σ)
  FunctionalTransitionSystem.state_pred
  FunctionalTransitionSystem.action_pred
