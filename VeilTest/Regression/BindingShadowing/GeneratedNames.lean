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

#gen_state

-- Opening the state must leave the immutable field accessible.
ghost relation readsTheory := value_conc = true

def background : Theory := { value_conc := true }
def initial : State FieldConcreteType := { value := false }

example : readsTheory background initial := rfl

end TheoryFieldWithGeneratedName
