module

public import Veil

-- Original TLA+ file, Copyright: Igor Konnov
-- https://github.com/konnov/cyclic-buffer-challenge/blob/1e499eeb2923d70f5269aca877dc3180f3baccf9/tla/BuggyCircularBuffer.tla


public instance [NeZero N] : Inhabited { n : Nat // n ∈ List.range N } where
  default := ⟨0, by
    simp only [List.mem_range]
    have : N ≠ 0 := NeZero.ne N
    omega⟩

public instance (n : Nat) (N : Nat) [NeZero N] :  Inhabited (Std.TreeMap (Fin n) { t // t ∈ List.range N } compare) := by
  infer_instance

public instance :  Inhabited (Std.TreeMap (Fin 2) { n // n ∈ List.range 2 } compare) := by
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

termination false

#time #gen_spec

-- TLC checks this spec with `Benchmarks/TLA/BuggyCircularBuffer.cfg`.
-- The check below finds the bug: `Put` has no guard, so `count` exceeds `BUFFER_SIZE` and
-- violates the unnamed `safety` clause above (reported as `safety_0`).
-- `set_option veil.violationIsError false in` reports that violation without failing the build.
--
-- The instantiation (first `{ ... }` argument) sets the module's `type`s and `param`s. There
-- are none, hence `{ }`.
-- The theory (second `{ ... }` argument) sets the module's `immutable` fields. There are none,
-- hence `{ }`.
-- The module fixes the cfg's constants itself:
-- * `BUFFER_SIZE = 2`: the `abbrev BUFFER_SIZE := 2` above.
-- * `BUFFER_ELEMS = {0, 1}`: the `abbrev BUFFER_ELEMS := (List.range 2 : List Nat)` above.
--
-- The other settings of the cfg:
-- * `INVARIANT SafeInv`: `#model_check` checks every `invariant` and `safety` clause of the
--   module. Here the only one is `SafeInv`, `count ≤ BUFFER_SIZE`.
-- * The cfg has no `CHECK_DEADLOCK`, so TLC checks for deadlocks. With `termination false`
--   above, Veil also reports every state without successors as a deadlock.
-- Options:
-- * The check names no mode, so its search starts in Lean's interpreter and moves to a compiled
--   checker once that is built.
set_option veil.violationIsError false in
#model_check { } { }

end BuggyCircularBuffer
