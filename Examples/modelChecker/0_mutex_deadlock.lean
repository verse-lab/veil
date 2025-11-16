import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main
-- ----- MODULE 0_mutex -----

veil module Mutex

type process
-- type seq_t
individual locked : Bool
enum states = { pre_check_lock, wait_until, enqueue_waker,
                check_lock, check_has_woken,
                release_lock, wake_one, wake_one_loop,
                wake_up, start, cs, Done }

-- instantiate states_isEnum : @states_Enum states

-- instantiate seq : TotalOrderWithZero seq_t
-- immutable individual one : seq_t

-- individual wait_queue_num_wakers : seq_t

individual wait_queue_wakers : List process

relation has_woken (th: process)
relation pc (self: process) (st: states)
immutable individual none : process

function stack_pc : process → List states


function stack_waker : process → List process
relation waker (self: process) (waker: process)

#gen_state
-- theory ghost relation lt (x y : seq_t) := (seq.le x y ∧ x ≠ y)
-- theory ghost relation next (x y : seq_t) := (lt x y ∧ ∀ z, lt x z → seq.le y z)
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

  wait_queue_wakers := []
  has_woken P := false
  waker P W := W == none

  stack_pc P := []
  stack_waker P := []
  pc P S := S == start
}

-- start(self) == /\ pc[self] = "start"
--                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
--                                                         pc        |->  "cs" ] >>
--                                                     \o stack[self]]
--                /\ pc' = [pc EXCEPT ![self] = "pre_check_lock"]
--                /\ UNCHANGED << locked, wait_queue_num_wakers,
--                                wait_queue_wakers, has_woken, waker >>
action _start (self : process) {
  require pc self start
  -- let t := stack_pc self
  stack_pc self := cs :: (stack_pc self)
  let random_waker ← pick process
  stack_waker self := random_waker :: (stack_waker self)
  pc self S := S == pre_check_lock
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
  if locked == false then
    locked := true

    let head_stack_pc_state := (stack_pc self).head!
    pc self S := S == head_stack_pc_state
    stack_pc self := (stack_pc self).tail
    stack_waker self := (stack_waker self).tail
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
  wait_queue_wakers := wait_queue_wakers.append [self]
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
  if locked == false then
    locked := true
    let head_stack_pc_state := (stack_pc self).head!
    pc self S := S == head_stack_pc_state
    stack_pc self := (stack_pc self).tail
    stack_waker self := (stack_waker self).tail
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
  if wait_queue_wakers.length == 0 then
    let head_stack_pc_state := (stack_pc self).head!
    pc self S := S == head_stack_pc_state
    let headwaker_stack_waker := (stack_waker self).head!
    waker self W := W == headwaker_stack_waker

    stack_pc self := (stack_pc self).tail
    stack_waker self := (stack_waker self).tail
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
  if wait_queue_wakers.length != 0 then
    let head_waker := wait_queue_wakers.head!
    waker self W := W == head_waker
    wait_queue_wakers := wait_queue_wakers.tail
    pc self S := S == wake_up
  else
    let head_stack_pc_state := (stack_pc self).head!
    pc self S := S == head_stack_pc_state
    stack_pc self := (stack_pc self).tail

    let headwaker_stack_waker := (stack_waker self).head!
    waker self W := W == headwaker_stack_waker
    stack_waker self := (stack_waker self).tail
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
  require pc self wake_up

  if ∃t, waker self t then
    let waker_self :| waker self waker_self

    /- Condition 1: -/
    if has_woken waker_self == false then
      has_woken waker_self := true
      let head_stack_pc_state := (stack_pc self).head!
      pc self S := S == head_stack_pc_state
      stack_pc self := (stack_pc self).tail

      let headwaker_stack_waker := (stack_waker self).head!
      waker self W := W == headwaker_stack_waker
      stack_waker self := (stack_waker self).tail
    else
      pc self S := S == wake_one_loop

  else
    /- Exception handle -/
    let waker_self := none
    if has_woken waker_self == false then
      has_woken waker_self := true
      let head_stack_pc_state := (stack_pc self).head!
      pc self S := S == head_stack_pc_state
      stack_pc self := (stack_pc self).tail

      let headwaker_stack_waker := (stack_waker self).head!
      waker self W := W == headwaker_stack_waker
      stack_waker self := (stack_waker self).tail
    else
      pc self S := S == wake_one_loop

}


-- unlock(self) == release_lock(self) \/ wake_one(self) \/ wake_one_loop(self)
--                    \/ wake_up(self)



action _cs(self : process) {
  require pc self cs
  stack_pc self := Done :: (stack_pc self)
  if ∃t, waker self t then
    let waker_self :| waker self waker_self
    stack_waker self := waker_self :: (stack_waker self)
    -- waker self W := false
    waker self W := W == none

  else
    let waker_self := none
    stack_waker self := waker_self :: (stack_waker self)
    waker self W := W == none

  pc self S := S == release_lock
}


termination [allDone] pc P Done
invariant [mutual_exclusion] ∀ I J, I ≠ J → ¬ (pc I cs ∧ pc J cs)


#gen_spec

#gen_exec
#finitizeTypes (Fin 3), states

-- Step 3: Run the model checker
def view (st : StateConcrete) := hash st

def modelCheckerResult' :=
   (runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (fun ρ σ => mutual_exclusion ρ σ) ((fun ρ σ => allDone ρ σ)) {none := 0} view).snd

def statesJson : Lean.Json := Lean.toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM {none := 0} (collectTrace' modelCheckerResult'))
open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />


end Mutex
