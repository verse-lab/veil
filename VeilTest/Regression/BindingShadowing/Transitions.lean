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

end PrimedAliasWarning
