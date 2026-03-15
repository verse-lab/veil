import Veil

set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

/-! # Test: `veil_set_field_representation`

Tests that field representation configuration correctly affects the concrete
types used by the model checker, and that `#gen_spec` and `#model_check`
work with each configuration.

Each module:
1. Checks definitional equality of `FieldConcreteType` against the expected
   `match` expression (via `rfl`).
2. Runs `#gen_spec` and `#model_check interpreted` to verify end-to-end.
-/

/-! ## Default representation (ExtTreeSet / ExtTreeMap) -/
veil module FieldRep_Default

type node
relation rel : node → node → Bool
function f : node → node
individual x : node

#gen_state

#check (rfl : @FieldRep_Default.FieldConcreteType = fun node [Ord node] f =>
  FieldRep_Default.State.Label.casesOn f
    (Std.ExtTreeSet (node × node))
    (Std.ExtTreeMap node node)
    node)

after_init {
  rel M N := false
  f N := N
  x := *
}

action act (n m : node) {
  rel n m := true
  f n := m
  x := n
}

invariant true

#gen_spec

#model_check interpreted { node := Fin 2 } {}

end FieldRep_Default

/-! ## Canonical representation for both relations and functions -/
veil module FieldRep_Canonical

type node
relation rel : node → node → Bool
function f : node → node
individual x : node

veil_set_field_representation relation Veil.CanonicalField
veil_set_field_representation function Veil.CanonicalField

#gen_state

#check (rfl : @FieldRep_Canonical.FieldConcreteType = fun node f =>
  FieldRep_Canonical.State.Label.casesOn f
    (node → node → Bool)
    (node → node)
    node)

after_init {
  rel M N := false
  f N := N
  x := *
}

action act (n m : node) {
  rel n m := true
  f n := m
  x := n
}

invariant true

#gen_spec

#model_check interpreted { node := Fin 2 } {}

end FieldRep_Canonical

/-! ## Array-based representation (ArrayAsFinset / ArrayAsFinmap) -/
veil module FieldRep_Array

type node
relation rel : node → node → Bool
function f : node → node
individual x : node

veil_set_field_representation relation Veil.ArrayAsFinset
veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

#check (rfl : @FieldRep_Array.FieldConcreteType = fun node [Veil.FinEncodable node] f =>
  FieldRep_Array.State.Label.casesOn f
    (Veil.ArrayAsFinset (node × node))
    (Veil.ArrayAsFinmap node node)
    node)

after_init {
  rel M N := false
  f N := N
  x := *
}

action act (n m : node) {
  rel n m := true
  f n := m
  x := n
}

invariant true

#gen_spec

#model_check interpreted { node := Fin 2 } {}

end FieldRep_Array

/-! ## Mixed: Canonical relations + default (ExtTreeMap) functions -/
veil module FieldRep_Mixed

type node
relation rel : node → node → Bool
function f : node → node
individual x : node

veil_set_field_representation relation Veil.CanonicalField

#gen_state

#check (rfl : @FieldRep_Mixed.FieldConcreteType = fun node [Ord node] f =>
  FieldRep_Mixed.State.Label.casesOn f
    (node → node → Bool)
    (Std.ExtTreeMap node node)
    node)

after_init {
  rel M N := false
  f N := N
  x := *
}

action act (n m : node) {
  rel n m := true
  f n := m
  x := n
}

invariant true

#gen_spec

#model_check interpreted { node := Fin 2 } {}

end FieldRep_Mixed
