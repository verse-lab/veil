import Veil

veil module BuggyCircularBuffer



-- CONSTANTS
--     \* Size of the circular buffer.
--     \* @type: Int;
--     BUFFER_SIZE,
--     \* The set of possible buffer elements.
--     \* @type: Set(Int);
--     BUFFER_ELEMS
-- macro_rules
-- | `(term| BUFFER_ELEMS) => `(term| (List.range 2 : List Nat))
abbrev BUFFER_ELEMS := (List.range 2 : List Nat)
-- macro_rules
-- | `(term| ExtTreeElem) => `(term| ({ n : Nat // n ∈ BUFFER_ELEMS } : Type))
abbrev ExtTreeElem := ({ n : Nat // n ∈ BUFFER_ELEMS } : Type)
-- macro_rules
-- | `(term| BUFFER_SIZE) => `(term| (2 : Nat))
abbrev BUFFER_SIZE := (2 : Nat)

-- individual buffer : bufferMap
individual buffer : List (Nat × Nat)
--     \* Index of the next element to POP.
--     \* @type: Int;
--     head,
individual head : Nat
--     \* Index of the next free slot for PUSH.
--     \* @type: Int;
--     tail,
-- individual tail : Fin BUFFER_SIZE
individual tail : Nat
--     \* Number of elements currently stored.
--     \* @type: Int;
--     count
individual count : Nat




#gen_state

-- \* Initial state
-- Init ==
--   /\ buffer = [ i \in 0..(BUFFER_SIZE - 1) |-> 0 ]
--   /\ head = 0
--   /\ tail = 0
--   /\ count = 0
after_init {
  buffer := List.range BUFFER_SIZE |>.map (fun i => (i, 0))
  head := 0
  tail := 0
  count := 0
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
  let x ← pick ExtTreeElem
  buffer := buffer.map (fun (i, v) => if i == tail then (i, x.val) else (i, v))
  head := head
  tail := (tail + 1) % BUFFER_SIZE
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

invariant [typeOKofBuffer] buffer.all (fun (i, v) => i < BUFFER_SIZE ∧ v ∈ BUFFER_ELEMS)
safety count ≤ BUFFER_SIZE
-- \* View for the model checker to observe the count variable.
-- \* @type: <<Int>>;
-- CountView == <<count>>

#gen_spec

#model_check { } { }

-- ======================================================================================
end BuggyCircularBuffer
