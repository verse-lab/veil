import Veil

/-

Reproduction of the mutex bug (Case Study 1) described in [Converos: Practical
Model Checking for Verifying Rust OS Kernel
Concurrency] by Ruize Tang. (https://www.usenix.org/system/files/atc25-tang.pdf)

The error existed in Rust code, which was converted to a TLA+ specification to
uncover the bug. This example models a mutex implementation in modern operating
systems, which uses a wait queue to manage processes waiting for the lock.

We use this example to demonstrate how Veil's model checker can find bugs in real-world
concurrent algorithms.

We model the stack in the algorithm using lean's `structure` definition
(`Cell`). Thus, we can use built-in primitives to manipulate the `stack`
(`append`, `head`, `tail`).

-/
veil module Mutex

type process
-- enum process = {NONE, P1, P2, P3}

individual locked : Bool
enum states = { pre_check_lock,
                prepare_wait_util,
                wait_until,
                enqueue_waker,
                check_lock,
                check_has_woken,
                release_lock,
                wake_one,
                wake_one_loop,
                wake_up,
                start,
                cs,
                Done }


individual wait_queue_wakers : List process

relation has_woken (th: process)
relation pc (self: process) (st: states)
immutable individual NONE : process


@[veil_decl]
structure Cell (states process : Type) where
  pc : states
  waker : process

function stack : process → List (Cell states process)

function waker : process → process


#gen_state


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
  wait_queue_wakers := []
  has_woken P := false
  /- Procedure unlock -/
  waker P := NONE
  stack P := []
  pc P S := S == start
}



-- pre_check_lock(self) == /\ pc[self] = "pre_check_lock"
--                         /\ IF locked = FALSE
--                               THEN /\ locked' = TRUE
--                                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                               ELSE /\ pc' = [pc EXCEPT ![self] = "prepare_wait_util"]
--                                    /\ UNCHANGED << locked, stack >>
--                         /\ UNCHANGED << wait_queue_num_wakers,
--                                         wait_queue_wakers, has_woken, waker >>
action _pre_check_lock (self : process) {
  require self ≠ NONE
  require pc self pre_check_lock
  if locked == false then
    locked := true
    let head_stack_pc_state := (stack self).head!.pc
    pc self S := S == head_stack_pc_state
    stack self := (stack self).tail
  else
    pc self S := S == prepare_wait_util
}


-- prepare_wait_util(self) == /\ pc[self] = "prepare_wait_util"
--              /\ locked' = FALSE
--              /\ pc' = [pc EXCEPT ![self] = "wait_until"]
--              /\ UNCHANGED << wait_queue_num_wakers, wait_queue_wakers,
--                              has_woken, stack, waker >>
action _prepare_wait_util (self : process) {
  require self ≠ NONE
  require pc self prepare_wait_util
  locked := false -- BUG: releases lock it doesn't own
  pc self S := S == wait_until
}



-- wait_until(self) == /\ pc[self] = "wait_until"
--                     /\ pc' = [pc EXCEPT ![self] = "enqueue_waker"]
--                     /\ UNCHANGED << locked, wait_queue_num_wakers,
--                                     wait_queue_wakers, has_woken, stack, waker >>
action _wait_until (self : process) {
  require self ≠ NONE
  require pc self wait_until
  pc self S := S == enqueue_waker
}


-- enqueue_waker(self) == /\ pc[self] = "enqueue_waker"
--                        /\ wait_queue_num_wakers' = wait_queue_num_wakers + 1
--                        /\ wait_queue_wakers' = Append(wait_queue_wakers, self)
--                        /\ pc' = [pc EXCEPT ![self] = "check_lock"]
--                        /\ UNCHANGED << locked, has_woken, stack, waker >>
action _enqueue_waker (self : process) {
  require self ≠ NONE
  require pc self enqueue_waker
  wait_queue_wakers := wait_queue_wakers.append [self]
  pc self S := S == check_lock
}


-- check_lock(self) == /\ pc[self] = "check_lock"
--                     /\ IF locked = FALSE
--                           THEN /\ locked' = TRUE
--                                /\ has_woken' = [has_woken EXCEPT ![self] = TRUE]
--                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                           ELSE /\ pc' = [pc EXCEPT ![self] = "check_has_woken"]
--                                /\ UNCHANGED << locked, has_woken, stack >>
--                     /\ UNCHANGED << wait_queue_num_wakers, wait_queue_wakers,
--                                     waker >>
action _check_lock (self : process) {
  require self ≠ NONE
  require pc self check_lock
  if locked == false then
    locked := true
    has_woken self := true
    let head_stack_pc_state := (stack self).head!.pc
    pc self S := S == head_stack_pc_state
    stack self := (stack self).tail
  else
    pc self S := S == check_has_woken
}


-- check_has_woken(self) == /\ pc[self] = "check_has_woken"
--                          /\ has_woken[self]
--                          /\ has_woken' = [has_woken EXCEPT ![self] = FALSE]
--                          /\ pc' = [pc EXCEPT ![self] = "wait_until"]
--                          /\ UNCHANGED << locked, wait_queue_num_wakers,
--                                          wait_queue_wakers, stack, waker >>
action _check_has_woken (self : process) {
  require self ≠ NONE
  require pc self check_has_woken
  require has_woken self
  has_woken self := false
  pc self S := S == wait_until
}


-- lock(self) == pre_check_lock(self) \/ prepare_wait_util(self) \/ wait_until(self)
--                  \/ enqueue_waker(self) \/ check_lock(self)
--                  \/ check_has_woken(self)



-- release_lock(self) == /\ pc[self] = "release_lock"
--                       /\ locked' = FALSE
--                       /\ pc' = [pc EXCEPT ![self] = "wake_one"]
--                       /\ UNCHANGED << wait_queue_num_wakers, wait_queue_wakers,
--                                       has_woken, stack, waker >>
action _release_lock (self : process) {
  require self ≠ NONE
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
  require self ≠ NONE
  require pc self wake_one
  if wait_queue_wakers.length == 0 then
    let head_stack_pc_state := (stack self).head!.pc
    pc self S := S == head_stack_pc_state
    let headwaker_stack_waker := (stack self).head!.waker
    waker self := headwaker_stack_waker
    stack self := (stack self).tail
  else
    pc self S := S == wake_one_loop
}



-- wake_one_loop(self) == /\ pc[self] = "wake_one_loop"
--                        /\ IF wait_queue_num_wakers /= 0
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
  require self ≠ NONE
  require pc self wake_one_loop
  if wait_queue_wakers.length != 0 then
    let head_waker := wait_queue_wakers.head!
    waker self := head_waker
    wait_queue_wakers := wait_queue_wakers.tail
    pc self S := S == wake_up
  else
    let head_stack := (stack self).head!
    let head_stack_pc_state := head_stack.pc
    pc self S := S == head_stack_pc_state
    let headwaker_stack_waker := head_stack.waker
    waker self := headwaker_stack_waker
    stack self := (stack self).tail
}



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
  require self ≠ NONE
  require pc self wake_up
  -- if ∃t, waker self t then
    -- let waker_self :| waker self waker_self
  let waker_self := waker self
  if !has_woken waker_self then
    has_woken waker_self := true
    let head_stack_pc_state := (stack self).head!.pc
    pc self S := S == head_stack_pc_state
    let headwaker_stack_waker := (stack self).head!.waker
    waker self := headwaker_stack_waker
    stack self := (stack self).tail
  else
    pc self S := S == wake_one_loop

}

-- unlock(self) == release_lock(self) \/ wake_one(self) \/ wake_one_loop(self)


-- start(self) == /\ pc[self] = "start"
--                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
--                                                         pc        |->  "cs" ] >>
--                                                     \o stack[self]]
--                /\ pc' = [pc EXCEPT ![self] = "pre_check_lock"]
--                /\ UNCHANGED << locked, wait_queue_num_wakers,
--                                wait_queue_wakers, has_woken, waker >>
action _start (self : process) {
  require self ≠ NONE
  require pc self start
  stack self := { pc := cs, waker := default } :: (stack self)
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
action _cs (self : process) {
  require self ≠ NONE
  require pc self cs
  let waker_self := waker self
  stack self := { pc := Done, waker := waker_self } :: (stack self)
  waker self := NONE
  pc self S := S == release_lock
}


/- Output log of TLC: <Terminating line 225, col 1 to line 225, col 11 of module MutexViolation>: 0:7
In TLA+, we specify the termination condition as follows:
`Terminating == /\ \A self \in ProcSet: pc[self] = "Done" /\ UNCHANGED vars`.
Intuitively, it can be taken as a property in veil, but it is also an action
naturally, whose require condition is `∀p ≠ NONE, pc p Done`.
We gave this empty action here to align the number `Found states` with TLC.
-/
action Terminating {
  require ∀p ≠ NONE, pc p Done
}

-- proc(self) == start(self) \/ cs(self)
-- Next == (\E self \in ProcSet: lock(self) \/ unlock(self))
--            \/ (\E self \in Procs: proc(self))
--            \/ Terminating

invariant [mutual_exclusion] ∀ I J, I ≠ J → ¬ (pc I cs ∧ pc J cs)
termination [AllDone] ∀s ≠ NONE, pc s Done = true

#time #gen_spec
-- NOTE: comment out the line containing `BUG:` to fix the violation

-- set_option veil.violationIsError false in
/- `Fin n` means `n-1` valid threads.-/
#model_check { process := Fin 4 } { NONE := 0 }

end Mutex
