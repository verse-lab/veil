import Veil

instance [NeZero N] : Inhabited { n : Nat // n ∈ List.range N } where
  default := ⟨0, by
    simp only [List.mem_range]
    have : N ≠ 0 := NeZero.ne N
    omega⟩

instance (n : Nat) (N : Nat) [NeZero N] :  Inhabited (Veil.TotalTreeMap (Fin n) { t // t ∈ List.range N } compare) := by
  infer_instance

instance :  Inhabited (Veil.TotalTreeMap (Fin 2) { n // n ∈ List.range 2 } compare) := by
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

#gen_spec
#model_check { } { }

end BuggyCircularBuffer

/-
Origianl TLA+ file, Copyright: Igor Konnov

https://raw.githubusercontent.com/konnov/cyclic-buffer-challenge/refs/heads/main/tla/BuggyCircularBuffer.tla

===========================================================

----------------------------- MODULE BuggyCircularBuffer -----------------------------
(**
 * A very simple specification of a circular buffer with a bug.
 * Generated with ChatGPT and beautified by Igor Konnov, 2025.
 * ChatGPT learned abstraction so well that it omitted the actual buffer storage!
 *)
EXTENDS Integers

CONSTANTS
    \* Size of the circular buffer.
    \* @type: Int;
    BUFFER_SIZE,
    \* The set of possible buffer elements.
    \* @type: Set(Int);
    BUFFER_ELEMS

ASSUME BUFFER_SIZE > 0

VARIABLES
    \* The integer buffer of size BUFFER_SIZE.
    \* @type: Int -> Int;
    buffer,
    \* Index of the next element to POP.
    \* @type: Int;
    head,
    \* Index of the next free slot for PUSH.
    \* @type: Int;
    tail,
    \* Number of elements currently stored.
    \* @type: Int;
    count

\* Initial state
Init ==
  /\ buffer = [ i \in 0..(BUFFER_SIZE - 1) |-> 0 ]
  /\ head = 0
  /\ tail = 0
  /\ count = 0

\* Buggy PUT: Advance tail, increment count, but no fullness check!
Put(x) ==
  Put::
  LET nextTail == (tail + 1) % BUFFER_SIZE IN
  /\ buffer' = [buffer EXCEPT ![tail] = x]
  /\ head' = head
  /\ tail' = nextTail
  /\ count' = count + 1

\* GET: Only allowed when count > 0.
Get ==
  Get::
  LET nextHead == (head + 1) % BUFFER_SIZE IN
  /\ count > 0
  /\ UNCHANGED buffer
  /\ head' = nextHead
  /\ tail' = tail
  /\ count' = count - 1

\* Either Put or Get may happen in any step.
Next ==
    \/ \E x \in BUFFER_ELEMS:
        Put(x)
    \/ Get

vars == <<buffer, head, tail, count>>

\* Complete specification
Spec == Init /\ [][Next]_vars

\* Safety property we *intend* to hold, but it is violated:
\* count must never exceed the buffer capacity.
SafeInv == count <= BUFFER_SIZE

\* View for the model checker to observe the count variable.
\* @type: <<Int>>;
CountView == <<count>>

======================================================================================


-/
