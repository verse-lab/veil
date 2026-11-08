module

public import Veil

veil module MiniProtocol

type node
relation rel : Nat → Bool
-- relation rel3 : node → node → node → Bool
function f : Nat → Option Nat
immutable function nodeToNat : node → Nat

/--
warning: Field `rel` uses a hybrid representation. Updates over potentially unbounded domains (e.g. `f I := ...`) can switch it to the canonical case, where default `Hashable` or `BEq` instances can merge distinct states and miss reachable states during model checking. For meaningful hashing and equality in the canonical case, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation; see `docs/DSL-Reference.md#hybrid-field-representations`. If the field stays concrete, suppress this warning with `set_option veil.warnHybridFields false`. Alternatively, consider `TMap` if it better fits your model.
---
warning: Field `f` uses a hybrid representation. Updates over potentially unbounded domains (e.g. `f I := ...`) can switch it to the canonical case, where default `Hashable` or `BEq` instances can merge distinct states and miss reachable states during model checking. For meaningful hashing and equality in the canonical case, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation; see `docs/DSL-Reference.md#hybrid-field-representations`. If the field stays concrete, suppress this warning with `set_option veil.warnHybridFields false`. Alternatively, consider `TMap` if it better fits your model.
-/
#guard_msgs in
#gen_state

after_init {
  -- rel N := false
  pure ()
}

action trivial (a : node) {
  let n := nodeToNat a
  -- rel n := true
  f n := some (n + 100)
}

invariant [inv_11] ∃ i < 10, (f i).isSome = false
termination true = true

#gen_spec

/-- info: ✅ No violation (explored 512 states) -/
#guard_msgs in
#model_check interpreted { node := Fin 9 } { nodeToNat := fun n => n.val }

end MiniProtocol
