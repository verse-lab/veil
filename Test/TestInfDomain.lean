import Veil

veil module MiniProtocol

type node
relation rel : Nat → Bool
-- relation rel3 : node → node → node → Bool
function f : Nat → Option Nat
immutable function nodeToNat : node → Nat

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

#model_check interpreted { node := Fin 9 } { nodeToNat := fun n => n.val }

end MiniProtocol
