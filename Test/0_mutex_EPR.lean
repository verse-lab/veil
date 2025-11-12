import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main
-- ----- MODULE 0_mutex -----

veil module Mutex
-- EXTENDS Integers, FiniteSets, Sequences, TLC

-- CONSTANTS NumProcs, NONE

-- Procs == 1..NumProcs

-- (*--algorithm mutex
-- {
-- variables locked = FALSE;
--           wait_queue_num_wakers = 0;
--           wait_queue_wakers = <<>>;
--           has_woken = [x \in Procs |-> FALSE];

-- procedure lock()
-- {
-- pre_check_lock:
--     if (locked = FALSE)
--     {
--         locked := TRUE;
--         return;
--     };
-- wait_until:
--     while (TRUE)
--     {
--     enqueue_waker:
--         wait_queue_num_wakers := wait_queue_num_wakers + 1;
--         wait_queue_wakers := Append(wait_queue_wakers, self);
--     check_lock:
--         if (locked = FALSE)
--         {
--             locked := TRUE;
--             return;
--         };
--     check_has_woken:
--         await has_woken[self];
--         has_woken[self] := FALSE;
--     };
-- }

-- procedure unlock()
-- variables waker = NONE;
-- {
-- release_lock:
--     locked := FALSE;
-- wake_one:
--     if (wait_queue_num_wakers = 0)
--     {
--         return;
--     };
-- wake_one_loop:
--     while (TRUE)
--     {
--         if (Len(wait_queue_wakers) /= 0)
--         {
--             waker := Head(wait_queue_wakers);
--             wait_queue_wakers := Tail(wait_queue_wakers);
--             wait_queue_num_wakers := wait_queue_num_wakers - 1;
--         }
--         else
--         {
--             return;
--         };
--     wake_up:
--         if (has_woken[waker] = FALSE)
--         {
--             has_woken[waker] := TRUE;
--             return;
--         }
--     }
-- }

-- fair process (proc \in Procs)
-- {
-- start:
-- \*    while (TRUE)
-- \*    {
--         call lock();
--     cs:
--         skip;
--         call unlock();
-- \*    };
-- }

-- }
-- *)
-- \* BEGIN TRANSLATION (chksum(pcal) = "b0b421b7" /\ chksum(tla) = "c2205e03")
-- VARIABLES
-- 1. locked,
-- 2. wait_queue_num_wakers,
-- 3. wait_queue_wakers,
-- 4. has_woken,
-- 5. pc,
-- 6. stack,
-- 7. waker
--
type process
type seq_t
individual locked : Bool
enum states = { pre_check_lock, wait_until, enqueue_waker,
                check_lock, check_has_woken,
                release_lock, wake_one, wake_one_loop,
                wake_up, start, cs, Done }

instantiate seq : TotalOrderWithZero seq_t
immutable individual one : seq_t

individual wait_queue_num_wakers : seq_t

relation wait_queue_wakers (index: seq_t) (th: process)
individual head_wait_queue : seq_t
individual tail_wait_queue : seq_t

relation has_woken (th: process)
relation pc (self: process) (st: states)



/-
Decompose the structure into two relations:
- `stack_pc` : process → seq_t → states
- `stack_waker` : process → seq_t → process.

To model the list, we use two individuals, which represent
the head and tail of the list respectively.

[ procedure |->  "unlock",
  pc        |->  "Done",
  waker     |->  waker[self] ]
-/
relation stack_pc (self: process) (index : seq_t) (pc: states)
individual head_stack_pc : seq_t
individual tail_stack_pc : seq_t

relation stack_waker (self: process) (index : seq_t) (waker: process)
individual head_stack_waker : seq_t
individual tail_stack_waker : seq_t

relation waker (self: process) (waker: process)

#gen_state

theory ghost relation lt (x y : seq_t) := (seq.le x y ∧ x ≠ y)
theory ghost relation next (x y : seq_t) := (lt x y ∧ ∀ z, lt x z → seq.le y z)
-- vars == << locked, wait_queue_num_wakers, wait_queue_wakers, has_woken, pc,
--            stack, waker >>

-- ProcSet == (Procs)

-- Init == (* Global variables *)
--         /\ locked = FALSE
--         /\ wait_queue_num_wakers = 0
--         /\ wait_queue_wakers = <<>>
--         /\ has_woken = [x \in Procs |-> FALSE]
--         (* Procedure unlock *)
--         /\ waker = [ self \in ProcSet |-> NONE]
--         /\ stack = [self \in ProcSet |-> << >>]
--         /\ pc = [self \in ProcSet |-> "start"]
after_init {
  locked := false
  wait_queue_num_wakers := seq.zero

  wait_queue_wakers I P := false
  head_wait_queue := seq.zero
  tail_wait_queue := seq.zero

  has_woken P := false
  waker P W := false

  stack_pc P I S := false
  head_stack_pc := seq.zero
  tail_stack_pc := seq.zero

  stack_waker P I W := false
  head_stack_waker := seq.zero
  tail_stack_waker := seq.zero

  pc P S := S == start
}

procedure succ (n : seq_t) {
  let k :| next n k
  return k
}

procedure dec (n : seq_t) {
  let k :| next k n
  return k
}

-- pre_check_lock(self) == /\ pc[self] = "pre_check_lock"
--                         /\ IF locked = FALSE
--                               THEN /\ locked' = TRUE
--                                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                               ELSE /\ pc' = [pc EXCEPT ![self] = "wait_until"]
--                                    /\ UNCHANGED << locked, stack >>
--                         /\ UNCHANGED << wait_queue_num_wakers,
--                                         wait_queue_wakers, has_woken, waker >>
action _pre_check_lock (self : process) {
  require pc self pre_check_lock
  if !locked then
    locked := true
    /- We use `tail_stack_pc_state` to keep track of the `top` of the stack -/
    let head_stack_pc_state :| stack_pc self tail_stack_pc head_stack_pc_state
    pc self head_stack_pc_state := true
    tail_stack_pc ← dec tail_stack_pc
    tail_stack_waker ← succ tail_stack_waker
  else
    pc self S := S == wait_until
}

-- wait_until(self) == /\ pc[self] = "wait_until"
--                     /\ pc' = [pc EXCEPT ![self] = "enqueue_waker"]
--                     /\ UNCHANGED << locked, wait_queue_num_wakers,
--                                     wait_queue_wakers, has_woken, stack, waker >>
action _wait_until (self : process) {
  require pc self wait_until
  pc self S := S == enqueue_waker
}

-- enqueue_waker(self) == /\ pc[self] = "enqueue_waker"
--                        /\ wait_queue_num_wakers' = wait_queue_num_wakers + 1
--                        /\ wait_queue_wakers' = Append(wait_queue_wakers, self)
--                        /\ pc' = [pc EXCEPT ![self] = "check_lock"]
--                        /\ UNCHANGED << locked, has_woken, stack, waker >>
action _enqueue_waker (self : process) {
  require pc self enqueue_waker

  wait_queue_wakers tail_wait_queue S := S == self
  tail_wait_queue ← succ tail_wait_queue
  wait_queue_num_wakers ← succ wait_queue_num_wakers

  pc self S := S == check_lock
}
-- check_lock(self) == /\ pc[self] = "check_lock"
--                     /\ IF locked = FALSE
--                           THEN /\ locked' = TRUE
--                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                           ELSE /\ pc' = [pc EXCEPT ![self] = "check_has_woken"]
--                                /\ UNCHANGED << locked, stack >>
--                     /\ UNCHANGED << wait_queue_num_wakers, wait_queue_wakers,
--                                     has_woken, waker >>
action _check_lock (self : process) {
  require pc self check_lock
  if !locked then
    locked := true
    let head_stack_pc_state :| stack_pc self tail_stack_pc head_stack_pc_state
    pc self S := S == head_stack_pc_state
    tail_stack_pc ← dec tail_stack_pc
    tail_stack_waker ← dec tail_stack_waker
  else
    pc self S := S == check_has_woken
}

-- check_has_woken(self) == /\ pc[self] = "check_has_woken"
--                          /\ has_woken[self]
--                          /\ has_woken' = [has_woken EXCEPT ![self] = FALSE]
--                          /\ pc' = [pc EXCEPT ![self] = "wait_until"]
--                          /\ UNCHANGED << locked, wait_queue_num_wakers,
--                                          wait_queue_wakers, stack, waker >>
action check_has_woken (self : process) {
  require pc self check_has_woken
  require has_woken self
  has_woken self := false
  pc self S := S == wait_until
}

-- lock(self) == pre_check_lock(self) \/ wait_until(self)
--                  \/ enqueue_waker(self) \/ check_lock(self)
--                  \/ check_has_woken(self)


-- release_lock(self) == /\ pc[self] = "release_lock"
--                       /\ locked' = FALSE
--                       /\ pc' = [pc EXCEPT ![self] = "wake_one"]
--                       /\ UNCHANGED << wait_queue_num_wakers, wait_queue_wakers,
--                                       has_woken, stack, waker >>
action _release_lock (self : process) {
  require pc self release_lock
  locked := false
  pc self S := S == wake_one
}


-- wake_one(self) == /\ pc[self] = "wake_one"
--                   /\ IF wait_queue_num_wakers = 0
--                         THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                              /\ waker' = [waker EXCEPT ![self] = Head(stack[self]).waker]
--                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                         ELSE /\ pc' = [pc EXCEPT ![self] = "wake_one_loop"]
--                              /\ UNCHANGED << stack, waker >>
--                   /\ UNCHANGED << locked, wait_queue_num_wakers,
--                                   wait_queue_wakers, has_woken >>
action _wake_one (self : process) {
  require pc self wake_one
  if wait_queue_num_wakers = seq.zero then
    let head_stack_pc_state :| stack_pc self tail_stack_pc head_stack_pc_state
    pc self S := S == head_stack_pc_state
    tail_stack_pc ← dec tail_stack_pc

    let headwaker_stack_waker :| stack_waker self tail_stack_waker headwaker_stack_waker
    waker self W := W == headwaker_stack_waker
    tail_stack_waker ← dec tail_stack_waker
  else
    pc self S := S == wake_one_loop
}

-- wake_one_loop(self) == /\ pc[self] = "wake_one_loop"
--                        /\ IF Len(wait_queue_wakers) /= 0
--                              THEN /\ waker' = [waker EXCEPT ![self] = Head(wait_queue_wakers)]
--                                   /\ wait_queue_wakers' = Tail(wait_queue_wakers)
--                                   /\ wait_queue_num_wakers' = wait_queue_num_wakers - 1
--                                   /\ pc' = [pc EXCEPT ![self] = "wake_up"]
--                                   /\ stack' = stack
--                              ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                                   /\ waker' = [waker EXCEPT ![self] = Head(stack[self]).waker]
--                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                                   /\ UNCHANGED << wait_queue_num_wakers,
--                                                   wait_queue_wakers >>
--                        /\ UNCHANGED << locked, has_woken >>

action _wake_one_loop (self : process) {
  require pc self wake_one_loop
  if ∃ idx, wait_queue_wakers idx self ∧ (idx ≠ seq.zero) then
    let head_waker :| wait_queue_wakers head_wait_queue head_waker
    waker self W := W == head_waker

    wait_queue_num_wakers ← dec wait_queue_num_wakers
    pc self S := S == wake_up
  else
    let head_stack_pc_state :| stack_pc self tail_stack_pc head_stack_pc_state
    pc self S := S == head_stack_pc_state
    tail_stack_pc ← dec tail_stack_pc

    let headwaker_stack_waker :| stack_waker self tail_stack_waker headwaker_stack_waker
    waker self W := W == headwaker_stack_waker
    tail_stack_waker ← dec tail_stack_waker
}
-- invariant [synchoronous_index] head_stack_pc = head_stack_waker
-- #gen_spec
-- #check_invariants


-- wake_up(self) == /\ pc[self] = "wake_up"
--                  /\ IF has_woken[waker[self]] = FALSE
--                        THEN /\ has_woken' = [has_woken EXCEPT ![waker[self]] = TRUE]
--                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                             /\ waker' = [waker EXCEPT ![self] = Head(stack[self]).waker]
--                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                        ELSE /\ pc' = [pc EXCEPT ![self] = "wake_one_loop"]
--                             /\ UNCHANGED << has_woken, stack, waker >>
--                  /\ UNCHANGED << locked, wait_queue_num_wakers,
--                                  wait_queue_wakers >>
action _wake_up (self : process) {
  require pc self wake_up
  let waker_self :| waker self waker_self
  if has_woken waker_self = false then
    has_woken waker_self := true
    let head_stack_pc_state :| stack_pc self tail_stack_pc head_stack_pc_state
    pc self S := S == head_stack_pc_state
    tail_stack_pc ← dec tail_stack_pc

    let headwaker_stack_waker :| stack_waker self tail_stack_waker headwaker_stack_waker
    waker self W := W == headwaker_stack_waker
    tail_stack_waker ← dec tail_stack_waker
  else
    pc self S := S == wake_one_loop
}


-- unlock(self) == release_lock(self) \/ wake_one(self) \/ wake_one_loop(self)
--                    \/ wake_up(self)

-- start(self) == /\ pc[self] = "start"
--                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
--                                                         pc        |->  "cs" ] >>
--                                                     \o stack[self]]
--                /\ pc' = [pc EXCEPT ![self] = "pre_check_lock"]
--                /\ UNCHANGED << locked, wait_queue_num_wakers,
--                                wait_queue_wakers, has_woken, waker >>
action _start (self : process) {
  require pc self start
  let head_stack_pc_state :| stack_pc self head_stack_pc head_stack_pc_state


  tail_stack_pc ← succ tail_stack_pc
  tail_stack_waker ← succ tail_stack_waker
  stack_pc self tail_stack_pc S := S == cs

  let random_waker ← pick process
  stack_waker self tail_stack_waker W := W == random_waker

  pc self S := S == pre_check_lock

}

-- cs(self) == /\ pc[self] = "cs"
--             /\ TRUE
--             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
--                                                      pc        |->  "Done",
--                                                      waker     |->  waker[self] ] >>
--                                                  \o stack[self]]
--             /\ waker' = [waker EXCEPT ![self] = NONE]
--             /\ pc' = [pc EXCEPT ![self] = "release_lock"]
--             /\ UNCHANGED << locked, wait_queue_num_wakers, wait_queue_wakers,
--                             has_woken >>
action _cs(self : process) {
  require pc self cs

  tail_stack_pc ← succ tail_stack_pc
  tail_stack_waker ← succ tail_stack_waker

  stack_pc self tail_stack_pc S := S == Done
  let waker_self :| waker self waker_self
  stack_waker self tail_stack_waker W := W == waker_self

  waker self W := false
  pc self S := S == release_lock
}

-- proc(self) == start(self) \/ cs(self)

-- (* Allow infinite stuttering to prevent deadlock on termination. *)
-- Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
--                /\ UNCHANGED vars

-- Next == (\E self \in ProcSet: lock(self) \/ unlock(self))
--            \/ (\E self \in Procs: proc(self))
--            \/ Terminating

-- Spec == /\ Init /\ [][Next]_vars
--         /\ \A self \in Procs : WF_vars(proc(self)) /\ WF_vars(lock(self)) /\ WF_vars(unlock(self))

-- Termination == <>(\A self \in ProcSet: pc[self] = "Done")

-- \* END TRANSLATION

-- MutualExclusion == \A i, j \in Procs :
--                      (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

-- Trying(i) == pc[i] \in { "pre_check_lock", "wait_until", "enqueue_waker", "check_lock", "check_has_woken"}

-- DeadAndLivelockFree == \E i \in Procs :
--                         Trying(i) ~> (\E j \in Procs : pc[j] = "cs")

-- StarvationFree == \A i \in Procs :
--                         Trying(i) ~> (pc[i] = "cs")

invariant [mutual_exclusion] pc I cs ∧ pc J cs → I = J
#gen_spec
-- #check_invariants
-- =============================================================================
end Mutex


-- instance [Ord α]: Repr (FieldConcreteType α states State.Label.locked) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Repr α] [Ord α]: Repr (FieldConcreteType α states State.Label.wait_queue_wakers) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Repr α] [Ord α]: Repr (FieldConcreteType α states State.Label.has_woken) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Repr α] [Ord α]: Repr (FieldConcreteType α states State.Label.pc) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Repr α] [Ord α]: Repr (FieldConcreteType α states State.Label.stack_pc) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Repr α] [Ord α]: Repr (FieldConcreteType α states State.Label.stack_waker) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Repr α] [Ord α]: Repr (FieldConcreteType α states State.Label.waker) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod


-- instance : Repr StateConcrete where
--   reprPrec st _:= Id.run do
--     let lock := st.locked
--     let wakers := st.wait_queue_wakers
--     let hw := st.has_woken
--     let pc_map := st.pc
--     let spc_map := st.stack_pc
--     let sw_map := st.stack_waker
--     let waker_map := st.waker
--     let s := "\n"
--           ++ "  locked: " ++ (if lock == true then "🔒" else "🔑") ++ "\n"
--           ++ "  wait_queue_wakers: " ++ repr wakers ++ "\n"
--           ++ "  has_woken: " ++ repr hw ++ "\n"
--           ++ "  pc: " ++ repr pc_map ++ "\n"
--           ++ "  stack_pc: " ++ repr spc_map ++ "\n"
--           ++ "  stack_waker: " ++ repr sw_map ++ "\n"
--           ++ "  waker: " ++ repr waker_map ++ "\n"
--     return s
