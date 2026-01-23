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