module

public import Veil

set_option linter.unusedVariables false

/-!
# Regression: extraction simplifies `FieldRepresentation` writes

A field assignment elaborates to `FieldRepresentation.setSingle pattern value old`,
and a field read to `FieldRepresentation.get`. Before model checking, extraction
rewrites both into the representation's own operations, such as an array or
tree-map insert (`simpFieldRepresentationSetSingle` / `simpFieldRepresentationGet`).
When one of these simprocs does not fire, nothing fails: the extracted action just
goes through the module's `instFieldRepresentation` dictionary at runtime and calls
its generic `setSingle`/`get` indirectly.

This happened once. `setSingle` used to abbreviate a `set` that took a list of
updates, so the simproc's discrimination-tree key contained the type of that list,
which mentions `IteratedArrow`. Once `IteratedArrow` became a recursive definition,
concrete field types reduced it away and no term ever matched. The checks below
inspect the extracted definitions directly, for each concrete representation.
The state counts check that the simplified writes still update the right entries.
-/

open Lean Elab Command Meta

private meta def isFieldRepresentationOp : Expr → Bool
  | .const n _ =>
    n == ``Veil.FieldRepresentation.setSingle || n == ``Veil.FieldRepresentation.get ||
      (n matches .str _ "instFieldRepresentation")
  | _ => false

/-- Fail if the body of an extracted definition still goes through `FieldRepresentation`. -/
elab "#guard_no_field_representation " ext:ident : command => do
  let extName ← resolveGlobalConstNoOverload ext
  let value := (← getConstInfoDefn extName).value
  -- Parameter types may mention `FieldRepresentation` (e.g. the `Decidable`
  -- instance of a quantified `require`); only the body runs.
  let leftover? ← liftTermElabM <| lambdaTelescope value fun _ body =>
    return body.find? isFieldRepresentationOp
  if let some e := leftover? then
    throwError "{extName} still calls {e} at runtime: extraction did not simplify \
      its `FieldRepresentation` operations away"

/-! ## Default representations (`Std.ExtTreeSet` / `Std.ExtTreeMap`) -/

veil module ExtractionFieldRepDefault

type node
individual flag : Bool
relation marked : node → Bool
relation edge : node → node → Bool
function owner : node → node

#gen_state

after_init {
  flag := false
  marked N := false
  edge N M := false
  owner N := N
}

action toggle { flag := !flag }
action mark (n : node) { marked n := true }
action clearMarks { marked N := false }
action connectAll (n : node) { edge n M := true }
action setOwner (n m : node) { owner n := m }

invariant true

#gen_spec

/-- info: ✅ No violation (explored 128 states) -/
#guard_msgs in
#model_check interpreted { node := Fin 2 } {} (sequential := true)

#guard_no_field_representation initializer.ext.extracted
#guard_no_field_representation toggle.ext.extracted
#guard_no_field_representation mark.ext.extracted
#guard_no_field_representation clearMarks.ext.extracted
#guard_no_field_representation connectAll.ext.extracted
#guard_no_field_representation setOwner.ext.extracted

end ExtractionFieldRepDefault

/-! ## Array representations (`Veil.ArrayAsFinset` / `Veil.ArrayAsFinmap`) -/

veil module ExtractionFieldRepArray

type node
individual flag : Bool
relation marked : node → Bool
relation edge : node → node → Bool
function owner : node → node

veil_set_field_representation relation Veil.ArrayAsFinset
veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

after_init {
  flag := false
  marked N := false
  edge N M := false
  owner N := N
}

action toggle { flag := !flag }
action mark (n : node) { marked n := true }
action clearMarks { marked N := false }
action connectAll (n : node) { edge n M := true }
action setOwner (n m : node) { owner n := m }

invariant true

#gen_spec

/-- info: ✅ No violation (explored 128 states) -/
#guard_msgs in
#model_check interpreted { node := Fin 2 } {} (sequential := true)

#guard_no_field_representation initializer.ext.extracted
#guard_no_field_representation toggle.ext.extracted
#guard_no_field_representation mark.ext.extracted
#guard_no_field_representation clearMarks.ext.extracted
#guard_no_field_representation connectAll.ext.extracted
#guard_no_field_representation setOwner.ext.extracted

end ExtractionFieldRepArray

/-! ## Bit-vector representations (`Veil.BitVecAsFinset` / `Veil.BitVecAsFinmap`) -/

veil module ExtractionFieldRepBitVec

type node
individual flag : Bool
relation marked : node → Bool
relation edge : node → node → Bool
function owner : node → node

veil_set_field_representation relation Veil.BitVecAsFinset
veil_set_field_representation function Veil.BitVecAsFinmap

#gen_state

after_init {
  flag := false
  marked N := false
  edge N M := false
  owner N := N
}

action toggle { flag := !flag }
action mark (n : node) { marked n := true }
action clearMarks { marked N := false }
action connectAll (n : node) { edge n M := true }
action setOwner (n m : node) { owner n := m }

invariant true

#gen_spec

/-- info: ✅ No violation (explored 128 states) -/
#guard_msgs in
#model_check interpreted { node := Fin 2 } {} (sequential := true)

#guard_no_field_representation initializer.ext.extracted
#guard_no_field_representation toggle.ext.extracted
#guard_no_field_representation mark.ext.extracted
#guard_no_field_representation clearMarks.ext.extracted
#guard_no_field_representation connectAll.ext.extracted
#guard_no_field_representation setOwner.ext.extracted

end ExtractionFieldRepBitVec

/-! ## Canonical representation (plain functions) -/

veil module ExtractionFieldRepCanonical

type node
individual flag : Bool
relation marked : node → Bool
relation edge : node → node → Bool
function owner : node → node

veil_set_field_representation relation Veil.CanonicalField
veil_set_field_representation function Veil.CanonicalField

#gen_state

after_init {
  flag := false
  marked N := false
  edge N M := false
  owner N := N
}

action toggle { flag := !flag }
action mark (n : node) { marked n := true }
action clearMarks { marked N := false }
action connectAll (n : node) { edge n M := true }
action setOwner (n m : node) { owner n := m }

invariant true

#gen_spec

/-- info: ✅ No violation (explored 128 states) -/
#guard_msgs in
#model_check interpreted { node := Fin 2 } {} (sequential := true)

#guard_no_field_representation initializer.ext.extracted
#guard_no_field_representation toggle.ext.extracted
#guard_no_field_representation mark.ext.extracted
#guard_no_field_representation clearMarks.ext.extracted
#guard_no_field_representation connectAll.ext.extracted
#guard_no_field_representation setOwner.ext.extracted

end ExtractionFieldRepCanonical
