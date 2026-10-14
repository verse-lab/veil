module

public import Veil

/-! A `Decidable` instance that an atom of a model-checked temporal property needs but that cannot be
synthesized for the module's abstract sorts becomes an instance-implicit parameter of the property's
model-checking definition `p.ast`, which `#temporal_check` synthesizes at the concrete types. This
covers quantifiers over a sort, which need no `Enumeration` on the definition, and instances that exist
only at a concrete type. -/

public section

/-- A predicate that is decidable only at `Fin 2`. -/
class Special (α : Type) where
  special : α → Prop

instance : Special (Fin 2) where
  special n := n.val = 1

instance (n : Fin 2) : Decidable (Special.special n) :=
  inferInstanceAs (Decidable (n.val = 1))

end

veil module LivenessDecidableParams

type node
instantiate sp : Special node
immutable individual start : node
individual cur : node
relation visited : node → Bool

after_init {
  cur := start
  visited N := false
}

action move (n : node) {
  cur := n
  visited n := true
}

ghost relation wasVisited (n : node) := visited n

-- Decidable only at the concrete type
temporal [startsSpecial] ⌜ Special.special cur ⌝
-- Quantifiers over a sort, also around a ghost
temporal [visitedStable] □ (⌜ ∀ n, wasVisited n ⌝ → □ ⌜ ∀ n, wasVisited n ⌝)
temporal [eventuallyVisited] ◇ ⌜ ∃ n, wasVisited n ⌝

invariant true
#gen_spec

-- No definition asks for `Enumeration` on the sort
run_meta do
  for n in [``LivenessDecidableParams.startsSpecial.ast, ``LivenessDecidableParams.visitedStable.ast,
      ``LivenessDecidableParams.eventuallyVisited.ast] do
    if (← Lean.getConstInfo n).type.getUsedConstants.contains ``Veil.Enumeration then
      throwError "{n} asks for `Enumeration`"

/-- info: ✅ No liveness violation (checked 3 properties, explored 11 product states) -/
#guard_msgs in
#temporal_check interpreted { node := Fin 2 } { start := 1 }

/-- error: ❌ Violation: liveness_failure (violates: startsSpecial) -/
#guard_msgs (substring := true) in
#temporal_check [startsSpecial] interpreted { node := Fin 2 } { start := 0 }

end LivenessDecidableParams

/-! A formula that fails to elaborate leaves the other properties defined. -/

veil module LivenessDecidableParamsBroken

individual flag : Bool

#gen_state

after_init {
  flag := false
}

action raise {
  flag := true
}

ghost relation raised := flag = true

temporal (only := check) [bare] ◇ raised
temporal [wrapped] ◇ ⌜ raised ⌝

/--
error: a plain term is not an atomic proposition of a model-checked property; write `⌜ raised ⌝` for a state predicate
-/
#guard_msgs in
#gen_spec

/-- error: `bare` is not a model-checked temporal property of this module. Model checked: wrapped -/
#guard_msgs in
#temporal_check [bare] interpreted {}

/-- info: ✅ No liveness violation (checked 1 properties, explored 2 product states) -/
#guard_msgs in
#temporal_check [wrapped] interpreted {}

end LivenessDecidableParamsBroken
