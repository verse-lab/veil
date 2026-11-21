module

public import Veil

veil module GhostParameterShadowing

immutable individual limit : Bool
individual value : Bool

#gen_state

/--
warning: parameter `value` shadows mutable state component `value`
-/
#guard_msgs (warning, substring := true) in
ghost relation readsStateParameter (value : Bool) := value = true

/--
warning: parameter `limit` shadows immutable theory component `limit`
-/
#guard_msgs (warning, substring := true) in
ghost relation readsTheoryParameter (limit : Bool) := limit = true

/--
warning: parameter `limit` shadows immutable theory component `limit`
-/
#guard_msgs (warning, substring := true) in
theory ghost relation theoryRelation (limit : Bool) := limit = true

/--
warning: parameter `value` shadows mutable state component `value`
-/
#guard_msgs (warning, substring := true) in
ghost function stateFunction (value : Bool) : Bool := value

/--
warning: parameter `limit` shadows immutable theory component `limit`
-/
#guard_msgs (warning, substring := true) in
theory ghost function theoryFunction (limit : Bool) : Bool := limit

def background : Theory := { limit := false }
def initial : State FieldConcreteType := { value := false }

-- Each argument disagrees with the field of the same name.
example : readsStateParameter true background initial := rfl
example : readsTheoryParameter true background initial := rfl
example : theoryRelation true background := rfl
example : stateFunction true background initial = true := rfl
example : theoryFunction true background = true := rfl

end GhostParameterShadowing

veil module UniqueFieldNames

immutable individual limit : Nat
/-- limit is already declared -/
#guard_msgs (error, substring := true) in
individual limit : Bool

individual value : Bool
/-- value is already declared -/
#guard_msgs (error, substring := true) in
immutable individual value : Nat

end UniqueFieldNames

veil module LocalParameterShadowing

individual value : Bool

#gen_state

/-- warning: parameter `value` shadows mutable state component `value` -/
#guard_msgs (warning, substring := true) in
ghost function readLocal (value : Bool) : Bool :=
  let value := !value
  value

example (input field : Bool) :
    readLocal input ({} : Theory) ({ value := field } : State FieldConcreteType) = !input := rfl

/-- warning: local `input` shadows parameter `input` -/
#guard_msgs (warning, substring := true) in
procedure localShadowsParameter (input : Bool) {
  let input := !input
  return input
}

/-- warning: local `input` shadows parameter `input` -/
#guard_msgs (warning, substring := true) in
procedure termLocalShadowsParameter (input : Bool) {
  return (fun input : Bool => !input) input
}

end LocalParameterShadowing

veil module InstanceFieldShadowing

instantiate flag : Inhabited Bool
individual flag : Bool

#gen_state

#guard_msgs in
ghost relation hasFlag := flag = true

example : hasFlag ({} : Theory) ({ flag := true } : State FieldConcreteType) := rfl

end InstanceFieldShadowing

veil module GhostFieldTypeInference

individual history : List (Nat × Nat)

#gen_state

ghost function selectedValue :=
  history.foldl (fun latest pair => if pair.1 < 2 then pair.2 else latest) (0 : Nat)

ghost function widenedOffset : Nat → Int :=
  fun offset : Nat => offset + history.length

def initial : State FieldConcreteType := { history := [(1, 7), (3, 9)] }

example : selectedValue ({} : Theory) initial = 7 := rfl
example : widenedOffset ({} : Theory) initial 3 = 5 := rfl

-- Lean callers can supply the implicit state through an ordinary field view.
example (state : State FieldConcreteType) :
    (let χ := FieldConcreteType
     let history := (instFieldRepresentation State.Label.history).get (show State χ from state).history
     selectedValue ({} : Theory)) = selectedValue ({} : Theory) state := by
  cases state
  rfl

end GhostFieldTypeInference
