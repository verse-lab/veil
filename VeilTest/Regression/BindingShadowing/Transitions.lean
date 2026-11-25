module

public import Veil

veil module TransitionParameterShadowing

immutable individual limit : Bool
individual value : Bool
individual result : Bool

#gen_state

/--
warning: parameter `value` shadows mutable state component `value`
-/
#guard_msgs (warning, substring := true) in
transition fromStateParameter (value : Bool) { result' = value }

/--
warning: parameter `limit` shadows immutable theory component `limit`
-/
#guard_msgs (warning, substring := true) in
transition fromTheoryParameter (limit : Bool) { result' = limit }

def background : Theory := { limit := false }
def before : State FieldConcreteType := { value := false, result := false }
def after : State FieldConcreteType := { value := false, result := true }

-- Keep the pre-state field and the theory field false while passing true.
example : fromStateParameter.ext.tr true background before after := by
  unfold fromStateParameter.ext.tr
  rfl

example : fromTheoryParameter.ext.tr true background before after := by
  unfold fromTheoryParameter.ext.tr
  rfl

end TransitionParameterShadowing

veil module PrimedAliasWarning

individual value' : Nat
individual value : Bool

#gen_state

transition readsPostState { value' = true }

/--
warning: parameter `value'` shadows mutable state component `value`; references to this name resolve to the parameter
-/
#guard_msgs in
transition shadowsPostState (value' : Bool) { value' = true }

/--
warning: local `value'` shadows mutable state component `value`; references to this name resolve to the local
-/
#guard_msgs in
transition localShadowsPostState { let value' := true; value' = true }

-- A shadowing binder leaves both fields framed. A real reference elsewhere
-- in the same expression still allows the post-state value to change.
def before : State FieldConcreteType := { value := false, value' := 0 }
def after : State FieldConcreteType := { value := true, value' := 0 }

example : shadowsPostState.ext.tr true ({} : Theory) before before := by
  unfold shadowsPostState.ext.tr
  rfl
example : ¬ shadowsPostState.ext.tr true ({} : Theory) before after := by
  change false ≠ true
  decide
example : ¬ localShadowsPostState.ext.tr ({} : Theory) before after := by
  change false ≠ true
  decide

/-- warning: local `value'` shadows mutable state component `value` -/
#guard_msgs (warning, substring := true) in
transition mixedScopes { (let value' := true; value') ∧ value' = true }

example : mixedScopes.ext.tr ({} : Theory) before after := by
  unfold mixedScopes.ext.tr
  rfl

-- An explicit tautology intentionally leaves the post-state unconstrained.
transition havocValue { value' = value' }
example : havocValue.ext.tr ({} : Theory) before after := by
  unfold havocValue.ext.tr
  rfl

end PrimedAliasWarning

veil module ImmutablePrimedNames

immutable individual limit : Bool
immutable individual other : Bool
individual other' : Bool
individual result : Bool

#gen_state

transition fromParameter (limit' : Bool) { result' = limit' }
transition fromLocal { let limit' := true; result' = limit' }
transition fromField { result' = other' }

def background : Theory := { limit := false, other := false }
def before : State FieldConcreteType := { other' := true, result := false }
def after : State FieldConcreteType := { other' := true, result := true }

example : fromParameter.ext.tr true background before after := by unfold fromParameter.ext.tr; rfl
example : fromLocal.ext.tr background before after := by unfold fromLocal.ext.tr; rfl
example : fromField.ext.tr background before after := by unfold fromField.ext.tr; rfl

end ImmutablePrimedNames

veil module HygienicTransitionFrame

individual x : Bool
individual y : Bool

#gen_state

transition setBoth (True : Bool) { True = false ∧ x' = true ∧ y' = true }
transition keepBoth (And : Bool) { And = false }

def before : State FieldConcreteType := { x := false, y := false }
def after : State FieldConcreteType := { x := true, y := true }

example : setBoth.ext.tr false ({} : Theory) before after := by unfold setBoth.ext.tr; rfl
example : keepBoth.ext.tr false ({} : Theory) before before := by unfold keepBoth.ext.tr; rfl
example : ¬ keepBoth.ext.tr false ({} : Theory) before after := by
  change false ≠ true
  decide

end HygienicTransitionFrame
