
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
  next : RelationalTransitionSystem.action σ
  safe : σ → Prop
  inv : σ → Prop

open RelationalTransitionSystem

def invInit [RelationalTransitionSystem σ] :=
  ∀ (s : σ), init s -> inv s

def invSafe [RelationalTransitionSystem σ] :=
  ∀ (s : σ), inv s -> safe s

def invInductive [RelationalTransitionSystem σ] :=
  ∀ (s1 s2 : σ), next s1 s2 -> inv s1 -> inv s2
