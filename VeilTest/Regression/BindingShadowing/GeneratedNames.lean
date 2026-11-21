module

public import Veil

veil module GhostParametersWithGeneratedNames

immutable individual limit : Bool
individual value : Bool

#gen_state

theory ghost function theoryReceiver (th : Bool) : Bool := th
ghost function stateReceiver (st : Bool) : Bool := st
ghost function concreteBinder (value_conc : Bool) : Bool := value_conc

def background : Theory := { limit := false }
def initial : State FieldConcreteType := { value := false }

example : theoryReceiver true background = true := rfl
example : stateReceiver true background initial = true := rfl
example : concreteBinder true background initial = true := rfl

end GhostParametersWithGeneratedNames

veil module GhostFieldsWithGeneratedNames

immutable individual st : Bool
individual value : Bool

#gen_state

-- Opening the theory must leave the state receiver accessible.
ghost relation readsState := value = true
def background : Theory := { st := false }
def initial : State FieldConcreteType := { value := true }

example : readsState background initial := rfl

end GhostFieldsWithGeneratedNames

veil module TheoryFieldWithGeneratedName

immutable individual value_conc : Bool
individual value : Bool
individual __veil_value_conc : Bool

#gen_state

-- Opening the state must leave the immutable field accessible.
theory ghost relation theoryFieldIsTrue := value_conc = true
ghost relation readsTheory := theoryFieldIsTrue

def background : Theory := { value_conc := true }
def initial : State FieldConcreteType := { value := false, __veil_value_conc := false }

example : readsTheory background initial := rfl

end TheoryFieldWithGeneratedName

veil module FieldsNamedLikeEnvironmentTypes

immutable individual ρ : Bool
immutable individual σ : Nat
/-- warning: mutable state component `σ` shadows immutable theory component `σ`; references to this name resolve to the state component -/
#guard_msgs in
individual σ : Bool

#gen_state

theory ghost relation readsTheory := ρ = true
ghost relation readsState := σ = true
ghost relation readsBoth := readsTheory ∧ readsState

example : readsBoth ({ ρ := true, σ := 0 } : Theory)
    ({ σ := true } : State FieldConcreteType) := ⟨rfl, rfl⟩

after_init { σ := false }

action copyTheory { σ := ρ }

transition keepState { σ' = σ }

invariant True

#gen_spec

#guard_msgs in
temporal [readsFields] □ (⌞ ρ = true ⌟ → ⌜ σ = true ⌝)

example : readsFields ({ ρ := true, σ := 0 } : Theory)
    (fun _ => ({ σ := true } : State FieldConcreteType)) 0 :=
  fun _ _ => rfl

end FieldsNamedLikeEnvironmentTypes

veil module ActionFieldsWithGeneratedNames

immutable individual enabled : Bool
individual __veil_enabled : Bool
individual __veil_state : Bool

theory ghost relation canRun := enabled = true
ghost relation stateIsReady := __veil_state = true

assumption enabled = true

after_init {
  __veil_enabled := false
  __veil_state := true
}

action step {
  require canRun
  require stateIsReady
  __veil_state := __veil_enabled
}

invariant True

#gen_spec

/-- info: ✅ Satisfying trace found -/
#guard_msgs (substring := true) in
sat trace {
  step
  assert (¬ __veil_state)
}

end ActionFieldsWithGeneratedNames

veil module TraceBindersWithGeneratedNames

individual ActionTag : Bool
individual _tr1_tag : Bool
individual _tr1_arg0_value : Bool
individual _tr1_act_keep_arg0_value : Bool

after_init {
  ActionTag := false
  _tr1_tag := false
  _tr1_arg0_value := false
  _tr1_act_keep_arg0_value := false
}

action keep (value : Bool) { require value }

invariant True

#gen_spec

/-- info: ✅ Satisfying trace found -/
#guard_msgs (substring := true) in
sat trace {
  keep
  assert (¬ ActionTag ∧ ¬ _tr1_tag)
}

/-- info: ✅ Satisfying trace found -/
#guard_msgs (substring := true) in
sat trace {
  keep
  assert (¬ _tr1_arg0_value)
}

/-- info: ✅ Satisfying trace found -/
#guard_msgs (substring := true) in
sat trace {
  any action
  assert (¬ _tr1_act_keep_arg0_value)
}

end TraceBindersWithGeneratedNames
