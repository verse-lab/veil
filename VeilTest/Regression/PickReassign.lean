module

public import Veil

/-!
`pick` must check the line of its optional type against its own position, not the
start of the surrounding block. Cover arrow assignments after another statement,
to both a mutable local and a state component. The inferred-type cases also check
that a bare `pick` leaves the following statement alone.
-/

set_option linter.unusedVariables false

veil module PickReassign

individual chosen : Bool

#gen_state

after_init {
  chosen := false
}

action local_typed {
  let mut x := false
  x ← pick Bool
  chosen := x
}

action state_typed {
  require True
  chosen ← pick Bool
  require True
}

action local_inferred {
  let mut x := false
  x ← pick
  chosen := x
}

action state_inferred {
  require True
  chosen ← pick
  require True
}

invariant true

#gen_spec

#gen_executable

def initial : State FieldConcreteType := { chosen := false }

/-- The value of `chosen` in each successful result; failures are recorded as `none`. -/
def outcomes (act : VeilMultiExecM Choice Int Theory (State FieldConcreteType) PUnit) :
    List (Option Bool) :=
  (act {} initial).map fun (_, result) => match result with
    | .res (.ok _, s) => some s.chosen
    | _ => none

#guard (letI : LogSwitch := ⟨false⟩; outcomes (local_typed.ext.extracted _ _)) ==
  [some true, some false]

#guard (letI : LogSwitch := ⟨false⟩; outcomes (state_typed.ext.extracted _ _)) ==
  [some true, some false]

#guard (letI : LogSwitch := ⟨false⟩; outcomes (local_inferred.ext.extracted _ _)) ==
  [some true, some false]

#guard (letI : LogSwitch := ⟨false⟩; outcomes (state_inferred.ext.extracted _ _)) ==
  [some true, some false]

end PickReassign
