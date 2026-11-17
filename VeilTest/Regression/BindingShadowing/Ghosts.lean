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

veil module FieldAndLocalShadowing

immutable individual shared : Nat

/-- warning: mutable state component `shared` shadows immutable theory component `shared` -/
#guard_msgs (warning, substring := true) in
individual shared : Bool

individual result : Bool

#gen_state

theory ghost function readTheory : Nat := shared
ghost relation readState := shared = true

/--
warning: parameter `shared` shadows mutable state component `shared`
-/
#guard_msgs (warning, substring := true) in
ghost function readLocal (shared : Bool) : Bool :=
  let shared := !shared
  shared

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

after_init {
  shared := false
  result := false
}

action updateShared {
  shared := true
}

transition updateSharedPrime { shared' = true }

invariant [readsState] readState ↔ shared

#gen_spec

def background : Theory := { shared := 5 }
def before : State FieldConcreteType := { shared := false, result := false }
def after : State FieldConcreteType := { shared := true, result := false }

example : readTheory background = 5 := rfl
example : readState background after := rfl
example : readLocal false background before = true := rfl
example : updateSharedPrime.ext.tr background before after := by
  unfold updateSharedPrime.ext.tr
  rfl

end FieldAndLocalShadowing
