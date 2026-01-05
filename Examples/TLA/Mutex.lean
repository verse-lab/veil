import Veil

open Std
/-
We use this example to demonstrate how our model checker can find bugs in real-world
concurrent algorithms, woriking as a standalone tool.
This example models a mutex implementation in modern operating
systems, which uses a wait queue to manage processes waiting for the lock.

We model the stack in the algorithm using lean's `structure` definition (Line 39).
Thus, we can use built-in primitives to manipulate the stack (`append`, `head`, `tail`).
-/
veil module Mutex

type process

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
immutable individual none : process


structure Cell (states process : Type) where
  pc : states
  waker : process
deriving DecidableEq, Inhabited, Hashable, Repr, Lean.ToJson

function stack : process → List (Cell states process)

relation waker (self: process) (waker: process)


#gen_state

after_init {
  locked := false
  wait_queue_wakers := []
  has_woken P := false
  waker P W := W == none
  stack P := []
  pc P S := S == start
}



action _pre_check_lock (self : process) {
  require pc self pre_check_lock
  if locked == false then
    locked := true
    let head_stack_pc_state := (stack self).head!.pc
    pc self S := S == head_stack_pc_state
    stack self := (stack self).tail
  else
    pc self S := S == prepare_wait_util
}


action _prepare_wait_util (self : process) {
  require pc self prepare_wait_util
  locked := false
  pc self S := S == wait_until
}



action _wait_until (self : process) {
  require pc self wait_until
  pc self S := S == enqueue_waker
}


action _enqueue_waker (self : process) {
  require pc self enqueue_waker
  wait_queue_wakers := wait_queue_wakers.append [self]
  pc self S := S == check_lock
}



action _check_lock (self : process) {
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


action _check_has_woken (self : process) {
  require pc self check_has_woken
  require has_woken self
  has_woken self := false
  pc self S := S == wait_until
}


action _release_lock (self : process) {
  require pc self release_lock
  locked := false
  pc self S := S == wake_one
}

action _wake_one (self : process) {
  require pc self wake_one
  if wait_queue_wakers.length == 0 then
    let head_stack_pc_state := (stack self).head!.pc
    pc self S := S == head_stack_pc_state
    let headwaker_stack_waker := (stack self).head!.waker
    waker self W := W == headwaker_stack_waker
    stack self := (stack self).tail
  else
    pc self S := S == wake_one_loop
}



action _wake_one_loop (self : process) {
  require pc self wake_one_loop
  if wait_queue_wakers.length != 0 then
    let head_waker := wait_queue_wakers.head!
    waker self W := W == head_waker
    wait_queue_wakers := wait_queue_wakers.tail
    pc self S := S == wake_up
  else
    let head_stack := (stack self).head!
    let head_stack_pc_state := head_stack.pc
    pc self S := S == head_stack_pc_state
    let headwaker_stack_waker := head_stack.waker
    waker self W := W == headwaker_stack_waker
    stack self := (stack self).tail
}



action _wake_up (self : process) {
  require pc self wake_up
  if ∃t, waker self t then
  -- assert ` ∃t, waker self t then`
    let waker_self :| waker self waker_self

    if has_woken waker_self == false then
      has_woken waker_self := true
      let head_stack_pc_state := (stack self).head!.pc
      pc self S := S == head_stack_pc_state
      let headwaker_stack_waker := (stack self).head!.waker
      waker self W := W == headwaker_stack_waker
      stack self := (stack self).tail
    else
      pc self S := S == wake_one_loop

}

action _start (self : process) {
  require pc self start
  let random_waker ← pick process
  stack self := { pc := cs, waker := random_waker } :: (stack self)
  pc self S := S == pre_check_lock
}


action _cs (self : process) {
  require pc self cs
  let waker_self :| waker self waker_self
  stack self := { pc := Done, waker := waker_self } :: (stack self)
  waker self W := W == none
  pc self S := S == release_lock
}

invariant [mutual_exclusion] ∀ I J, I ≠ J → ¬ (pc I cs ∧ pc J cs)
termination [AllDone] pc S Done = true

#time #gen_spec

#model_check { process := Fin 3 } { none := 0 }

end Mutex
