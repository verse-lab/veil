import Veil

/-!
Regression test: `#gen_spec` used to fail with `failed to synthesize
Enumeration ℕ` / `FinEncodableInjOnly ℕ` when an action parameter has a
non-enumerable concrete type such as `Nat`. The generated `Label` type
unconditionally derived `Veil.Enumeration` and `Veil.FinEncodableInjOnly`,
both of which require every action-parameter type to be enumerable.

These instances are now derived best-effort (`veil_try_deriving`): modules
with non-enumerable action parameters still elaborate and remain verifiable;
the missing `Enumeration Label` instance only surfaces if model checking is
attempted.
-/

open Lean Meta Elab Command in
/-- Assert that no instance of the given class application can be synthesized. -/
elab "#assert_no_instance " t:term : command => runTermElabM fun _ => do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  match ← trySynthInstance e with
  | .some _ => throwError "unexpectedly synthesized an instance of {e}"
  | _ => pure ()

-- Original bug-report shape: default field representation, mutable relation
-- over a `Nat` domain, action parameter of type `Nat`.
veil module NatActionParamDefaultRep
relation seen : Nat → Bool
#gen_state
after_init { seen X := false }
action mark(x : Nat) {
  seen x := true
}
invariant [triv] seen 0 ∨ ¬ seen 0
#gen_spec

-- Model checking legitimately remains unavailable: the transition labels
-- cannot be enumerated. The failure surfaces here, not at `#gen_spec`.
/--
error: failed to synthesize instance of type class
  Enumeration Label

Hint: Adding the command `deriving instance Veil.Enumeration for NatActionParamDefaultRep.Label` may allow Lean to derive the missing instance.
---
error: cannot evaluate code because 'sorryAx' uses 'sorry' and/or contains errors
-/
#guard_msgs in
#model_check interpreted {}
end NatActionParamDefaultRep

-- The label enumeration instances are (expectedly) unavailable, since `Nat`
-- cannot be enumerated. This is the graceful-degradation contract: the module
-- elaborates, and only model checking is unavailable.
#assert_no_instance Veil.Enumeration NatActionParamDefaultRep.Label
#assert_no_instance Veil.FinEncodableInjOnly NatActionParamDefaultRep.Label

-- Same shape with the canonical field representation.
veil module NatActionParamCanonicalRep
veil_set_field_representation relation Veil.CanonicalField
relation seen : Nat → Bool
#gen_state
after_init { seen X := false }
action mark(x : Nat) {
  seen x := true
}
invariant [triv] seen 0 ∨ ¬ seen 0
#gen_spec
end NatActionParamCanonicalRep

-- Mutable `function` over `Nat` alongside a relation (also from the report).
veil module NatActionParamWithFunction
relation r : Nat → Bool
function f : Nat → Nat
#gen_state
after_init {
  r X := false
  f X := 0
}
action upd(x : Nat) {
  r x := true
  f x := x
}
invariant [triv] r 0 ∨ ¬ r 0
#gen_spec
end NatActionParamWithFunction

-- Sanity check: when every action parameter is enumerable (concrete
-- enumerable types like `Bool`, or sorts), the `Label` instances are still
-- derived, so model checking keeps working.
veil module EnumerableActionParams
type node
relation r : node → Bool
#gen_state
after_init { r N := false }
action mark (b : Bool) (n : node) {
  r n := b
}
invariant [triv] r N ∨ ¬ r N
#gen_spec

/-- info: ✅ No violation (explored 4 states) -/
#guard_msgs in
#model_check interpreted { node := Fin 2 }
end EnumerableActionParams

example : Veil.Enumeration (EnumerableActionParams.Label (Fin 3)) := inferInstance
example : Veil.FinEncodableInjOnly (EnumerableActionParams.Label (Fin 3)) := inferInstance
