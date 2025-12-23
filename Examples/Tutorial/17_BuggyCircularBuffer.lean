import Veil

veil module BuggyCircularBuffer



-- CONSTANTS
--     \* Size of the circular buffer.
--     \* @type: Int;
--     BUFFER_SIZE,
--     \* The set of possible buffer elements.
--     \* @type: Set(Int);
--     BUFFER_ELEMS
macro_rules
| `(term| BUFFER_ELEMS) => `(term| (List.range 2 : List Nat))
macro_rules
| `(term| ExtTreeElem) => `(term| ({ n : Nat // n ∈ BUFFER_ELEMS } : Type))
macro_rules
| `(term| BUFFER_SIZE) => `(term| (2 : Nat))
-- immutable individual BUFFER_SIZE : Nat
-- ASSUME BUFFER_SIZE > 0
-- VARIABLES
--     \* The integer buffer of size BUFFER_SIZE.
--     \* @type: Int -> Int;
--     buffer : `Fin BUFFER_SIZE` -> `{ n // n ∈ BUFFER_ELEMS}`
function buffer : Fin BUFFER_SIZE → ExtTreeElem
--     \* Index of the next element to POP.
--     \* @type: Int;
--     head,
individual head : Nat
--     \* Index of the next free slot for PUSH.
--     \* @type: Int;
--     tail,
individual tail : Fin BUFFER_SIZE
--     \* Number of elements currently stored.
--     \* @type: Int;
--     count
individual count : Nat

-- Changed: Make h an instance parameter [NeZero N] so it can be auto-inferred
instance [NeZero N] : Inhabited { n : Nat // n ∈ List.range N } where
  default := ⟨0, by
    simp only [List.mem_range]
    have : N ≠ 0 := NeZero.ne N
    omega⟩

instance (n : Nat) (N : Nat) [NeZero N] :  Inhabited (Veil.TotalTreeMap (Fin n) { t // t ∈ List.range N } compare) := by
  infer_instance

instance :  Inhabited (Veil.TotalTreeMap (Fin 2) { n // n ∈ List.range 2 } compare) := by
  infer_instance

#gen_state

-- \* Initial state
-- Init ==
--   /\ buffer = [ i \in 0..(BUFFER_SIZE - 1) |-> 0 ]
--   /\ head = 0
--   /\ tail = 0
--   /\ count = 0
after_init {
  buffer := fun _ => ⟨0, by simp⟩
  head := (0 : Nat)
  tail := (0 : Fin BUFFER_SIZE)
  count := (0 : Nat)
}

-- \* Buggy PUT: Advance tail, increment count, but no fullness check!
-- Put(x) ==
--   Put::
--   LET nextTail == (tail + 1) % BUFFER_SIZE IN
--   /\ buffer' = [buffer EXCEPT ![tail] = x]
--   /\ head' = head
--   /\ tail' = nextTail
--   /\ count' = count + 1
action Put {
  -- \E x \in BUFFER_ELEMS:
  let x ← pick ExtTreeElem
  -- Update buffer at current tail position
  buffer tail := x
  -- head remains unchanged
  head := head
  -- Advance tail: (tail + 1) % BUFFER_SIZE
  tail := Fin.mk ((tail.val + 1) % BUFFER_SIZE) (by
    apply Nat.mod_lt
    simp
  )
  -- Increment count (this is the bug - no check if buffer is full!)
  count := count + 1
}


-- \* GET: Only allowed when count > 0.
-- Get ==
--   Get::
--   LET nextHead == (head + 1) % BUFFER_SIZE IN
--   /\ count > 0
--   /\ UNCHANGED buffer
--   /\ head' = nextHead
--   /\ tail' = tail
--   /\ count' = count - 1
action Get {
  require count > 0
  head := (head + 1) % BUFFER_SIZE
  tail := tail
  count := count - 1
}

-- \* Either Put or Get may happen in any step.
-- Next ==
--     \/ \E x \in BUFFER_ELEMS:
--         Put(x)
--     \/ Get

-- vars == <<buffer, head, tail, count>>

-- \* Complete specification
-- Spec == Init /\ [][Next]_vars

-- \* Safety property we *intend* to hold, but it is violated:
-- \* count must never exceed the buffer capacity.
-- SafeInv == count <= BUFFER_SIZE
safety count ≤ BUFFER_SIZE
-- \* View for the model checker to observe the count variable.
-- \* @type: <<Int>>;
-- CountView == <<count>>

#gen_spec

#model_check { } { }

-- ======================================================================================
end BuggyCircularBuffer
