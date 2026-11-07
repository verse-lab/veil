module

public import Veil

veil module MiniProtocol

type node
relation rel : Nat → Bool
-- relation rel3 : node → node → node → Bool
function f : Nat → Option Nat
immutable function nodeToNat : node → Nat

/--
warning: Field `rel` uses a hybrid representation with default canonical `Hashable` or `BEq` instances, which can cause model checking to merge distinct states and miss reachable states. For meaningful hashing and equality, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation.
---
warning: Field `f` uses a hybrid representation with default canonical `Hashable` or `BEq` instances, which can cause model checking to merge distinct states and miss reachable states. For meaningful hashing and equality, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation.
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
