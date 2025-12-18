import Veil

veil module Mutex

set_option trace.veil.desugar true

type process
individual locked : Bool
enum states = { pre_check_lock, wait_until, enqueue_waker,
                check_lock, check_has_woken,
                release_lock, wake_one, wake_one_loop,
                wake_up, start, cs, Done }



individual wait_queue_wakers : List process

relation has_woken (th: process)
relation pc (self: process) (st: states)
immutable individual none : process

function stack_pc : process → List states
function stack_waker : process → List process
relation waker (self: process) (waker: process)

#gen_state


after_init {
  locked := false

  wait_queue_wakers := []
  has_woken P := false
  waker P W := W == none

  stack_pc P := []
  stack_waker P := []
  pc P S := S == start
}


action _start (self : process) {
  require pc self start
  -- let t := stack_pc self
  stack_pc self := cs :: (stack_pc self)
  let random_waker ← pick process
  stack_waker self := random_waker :: (stack_waker self)
  pc self S := S == pre_check_lock
}



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
    let head_stack_pc_state := (stack_pc self).head!
    pc self S := S == head_stack_pc_state
    stack_pc self := (stack_pc self).tail
    stack_waker self := (stack_waker self).tail
  else
    pc self S := S == check_has_woken
}


action check_has_woken (self : process) {
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
    let head_stack_pc_state := (stack_pc self).head!
    pc self S := S == head_stack_pc_state
    let headwaker_stack_waker := (stack_waker self).head!
    waker self W := W == headwaker_stack_waker

    stack_pc self := (stack_pc self).tail
    stack_waker self := (stack_waker self).tail
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
    let head_stack_pc_state := (stack_pc self).head!
    pc self S := S == head_stack_pc_state
    stack_pc self := (stack_pc self).tail

    let headwaker_stack_waker := (stack_waker self).head!
    waker self W := W == headwaker_stack_waker
    stack_waker self := (stack_waker self).tail
}



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
}


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


invariant [mutual_exclusion] pc T1 cs ∧ pc T2 cs → T1 = T2
termination [AllDone] ∀p, pc p Done = true

#gen_spec


#time #model_check { process := Fin 3 } {none := 0}

end Mutex
