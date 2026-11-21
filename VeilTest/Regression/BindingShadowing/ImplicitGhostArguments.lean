module

public import Veil

veil module ImplicitTheoryUnderShadowing

immutable individual limit : Bool
individual value : Bool

theory ghost relation theoryIsFalse := limit = false

assumption limit = false
after_init { value := false }
action idle { pure () }

-- The bound variable is true while the actual theory field is false.
/-- shadows immutable theory component `limit` -/
#guard_msgs (warning, substring := true) in
invariant [readsTheory] ∀ limit : Bool, limit = true → theoryIsFalse

#gen_spec

def background : Theory := { limit := false }
def initial : State FieldConcreteType := { value := false }

example : readsTheory background initial := by
  intro localLimit isTrue
  subst localLimit
  rfl

/-- info: ✅ Satisfying trace found -/
#guard_msgs (substring := true) in
sat trace {
  assert (∀ limit : Bool, limit = true → theoryIsFalse)
}

end ImplicitTheoryUnderShadowing

veil module ImplicitStateUnderShadowing

individual value : Bool
individual result : Bool

#gen_state

ghost relation stateIsFalse := value = false

transition checkState {
  result' = true ∧ (∀ value : Bool, value = true → stateIsFalse)
}

def before : State FieldConcreteType := { value := false, result := false }
def after : State FieldConcreteType := { value := false, result := true }

-- The ghost sees the actual pre-state, including its false value field.
example : checkState.ext.tr ({} : Theory) before after := by
  unfold checkState.ext.tr
  rfl

end ImplicitStateUnderShadowing
