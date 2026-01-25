import Veil

-- Original TLA+ file, Copyright: Igor Konnov
-- https://github.com/konnov/cyclic-buffer-challenge/blob/1e499eeb2923d70f5269aca877dc3180f3baccf9/tla/BuggyCircularBuffer.tla


instance [NeZero N] : Inhabited { n : Nat // n ∈ List.range N } where
  default := ⟨0, by
    simp only [List.mem_range]
    have : N ≠ 0 := NeZero.ne N
    omega⟩

instance (n : Nat) (N : Nat) [NeZero N] :  Inhabited (Std.TreeMap (Fin n) { t // t ∈ List.range N } compare) := by
  infer_instance

instance :  Inhabited (Std.TreeMap (Fin 2) { n // n ∈ List.range 2 } compare) := by
  infer_instance

veil module BuggyCircularBuffer

abbrev BUFFER_ELEMS := (List.range 2 : List Nat)
abbrev ExtTreeElem := { n : Nat // n ∈ BUFFER_ELEMS }
abbrev BUFFER_SIZE := 2

function buffer : Fin BUFFER_SIZE → ExtTreeElem
individual head : Nat
individual tail : Fin BUFFER_SIZE
individual count : Nat

#gen_state

after_init {
  buffer := fun _ => ⟨0, by simp⟩
  head := (0 : Nat)
  tail := (0 : Fin BUFFER_SIZE)
  count := (0 : Nat)
}

/- There is not any high-bound guard condition
for this action, so it can be executed infinite times.-/
action Put {
  let x ← pick ExtTreeElem
  buffer tail := x
  head := head
  tail := Fin.mk ((tail.val + 1) % BUFFER_SIZE) (by grind)
  count := count + 1
}

action Get {
  require count > 0
  head := (head + 1) % BUFFER_SIZE
  tail := tail
  count := count - 1
}

safety count ≤ BUFFER_SIZE

#time #gen_spec

set_option veil.violationIsError false in
#model_check { } { }

end BuggyCircularBuffer
