module

public import Veil

veil module TemporalBinderShadowing

immutable individual limit : Bool
individual value : Bool

after_init { value := false }
action idle { value := value }

invariant True

#gen_spec

/-- shadows mutable state component `value` -/
#guard_msgs (warning, substring := true) in
temporal [stateField] ∀ value : Bool, □ ⌜ value = false ⌝

/-- shadows immutable theory component `limit` -/
#guard_msgs (warning, substring := true) in
temporal [theoryFieldInStateAtom] ∀ limit : Bool, □ ⌜ limit = false ⌝

/-- shadows immutable theory component `limit` -/
#guard_msgs (warning, substring := true) in
temporal [theoryFieldInPureAtom] ∀ limit : Bool, □ ⌞ limit = false ⌟

-- A state atom elsewhere in the formula does not put fields in scope here.
#guard_msgs in
temporal [pureQuantifier] (∀ value : Bool, □ ⌞ value = false ⌟) ∧ □ ⌜ value = false ⌝

#guard_msgs in
temporal [pureLocal] □ ⌞ let value := false; value = false ⌟ ∧ □ ⌜ value = false ⌝

-- The true quantifier instance violates each property even though both fields stay false.
/-- error: ❌ Violation: liveness_failure (violates: stateField) -/
#guard_msgs (substring := true) in
#temporal_check [stateField] interpreted {} { limit := false }

/-- error: ❌ Violation: liveness_failure (violates: theoryFieldInStateAtom) -/
#guard_msgs (substring := true) in
#temporal_check [theoryFieldInStateAtom] interpreted {} { limit := false }

/-- error: ❌ Violation: liveness_failure (violates: theoryFieldInPureAtom) -/
#guard_msgs (substring := true) in
#temporal_check [theoryFieldInPureAtom] interpreted {} { limit := false }

-- The proof-side state atom must also refer to the quantifier's value.
def background : Theory := { limit := false }
def execution : Lentil.exec (State FieldConcreteType) := fun _ => { value := false }

example : ¬ stateField background execution 0 := by
  intro holds
  have impossible : true = false := holds true 0
  cases impossible

end TemporalBinderShadowing
