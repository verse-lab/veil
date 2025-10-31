import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main
-- ----- MODULE 0_mutex -----

veil module Mutex
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


individual locked : Bool
enum states = { pre_check_lock, wait_until, enqueue_waker,
                check_lock, check_has_woken,
                release_lock, wake_one, wake_one_loop,
                wake_up, start, cs, Done }



-- individual wait_queue_num_wakers : seq_t
-- relation wait_queue_wakers (index: seq_t) (th: process)
relation domain_wait_queue_wakers : process -> Bool
relation edge_wait_queue : process -> process -> Bool
relation reachable_wait_queue : process -> process -> Bool


relation has_woken (th: process)
relation pc (self: process) (st: states)


-- relation stack_pc (self: process) (index : seq_t) (pc: states)
-- individual head_stack_pc : seq_t
-- individual tail_stack_pc : seq_t
relation domain_pc : process -> Bool
relation edge_pc : states -> states -> Bool
relation reachable_pc : states -> states -> Bool



-- relation stack_waker (self: process) (index : seq_t) (waker: process)
-- individual head_stack_waker : seq_t
-- individual tail_stack_waker : seq_t
relation domain_waker : process -> Bool
relation edge_waker : process -> process -> Bool
relation reachable_waker : states -> states -> Bool

relation waker (self: process) (waker: process)

#gen_state


-- assumption [zero_one] next seq.zero one


after_init {
  locked := false

  domain_wait_queue_wakers P := false
  edge_wait_queue P Q := false
  reachable_wait_queue P Q := false

  domain_pc S := false
  edge_pc S1 S2 := false
  reachable_pc S1 S2 := false

  domain_waker P := false
  edge_waker P Q := false
  reachable_waker S1 S2 := false

  has_woken P := false
  pc P S := S == start

  assume ∀ X Y1 Y2, edge_pc X Y1 ∧ edge_pc X Y2 → Y1 = Y2
  assume ∀ X, reachable_pc X X
  assume ∀ X Y Z, (reachable_pc X Y) ∧ (reachable_pc Y Z) → reachable_pc X Z
  assume ∀ X Y, (reachable_pc X Y) ∧ (reachable_pc Y X) → X = Y
  assume ∀ X Y Z, (reachable_pc X Y) ∧ (reachable_pc X Z) → (reachable_pc Y Z ∨ reachable_pc Z Y)

  assume ∀ X Y1 Y2, edge_waker X Y1 ∧ edge_waker X Y2 → Y1 = Y2
  assume ∀ X, reachable_waker X X
  assume ∀ X Y Z, (reachable_waker X Y) ∧ (reachable_waker Y Z) -> reachable_waker X Z
  assume ∀ X Y, (reachable_waker X Y) ∧ (reachable_waker Y X) -> X = Y
  assume ∀ X Y Z, (reachable_waker X Y) ∧ (reachable_waker X Z) -> (reachable_waker Y Z ∨ reachable_waker Z Y)

  assume ∀ P1 P2 P3, edge_wait_queue P1 P2 ∧ edge_wait_queue P1 P3 -> P2 = P3
  assume ∀ P, reachable_wait_queue P P
  assume ∀ P1 P2 P3, (reachable_wait_queue P1 P2) ∧ (reachable_wait_queue P2 P3) -> reachable_wait_queue P1 P3
  assume ∀ P1 P2, (reachable_wait_queue P1 P2) ∧ (reachable_wait_queue P2 P1) -> P1 = P2
  assume ∀ P1 P2 P3, (reachable_wait_queue P1 P2) ∧ (reachable_wait_queue P1 P3) -> (reachable_wait_queue P2 P3 ∨ reachable_wait_queue P3 P2)
}


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


action _wait_until (self : process) {
  require pc self wait_until
  pc self S := S == enqueue_waker
}

action _enqueue_waker (self : process) {
  require pc self enqueue_waker

  wait_queue_wakers tail_wait_queue S := S == self
  tail_wait_queue ← succ tail_wait_queue
  wait_queue_num_wakers ← succ wait_queue_num_wakers

  pc self S := S == check_lock
}


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



-- start(self) == /\ pc[self] = "start"
--                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
--                                                         pc        |->  "cs" ] >>
--                                                     \o stack[self]]
--                /\ pc' = [pc EXCEPT ![self] = "pre_check_lock"]
--                /\ UNCHANGED << locked, wait_queue_num_wakers,
--                                wait_queue_wakers, has_woken, waker >>
action _start (self : process) {
  require pc self start
  -- let head_stack_pc_state :| stack_pc self head_stack_pc head_stack_pc_state
  tail_stack_pc ← succ tail_stack_pc
  tail_stack_waker ← succ tail_stack_waker
  stack_pc self tail_stack_pc S := S == cs

  let random_waker ← pick process
  stack_waker self tail_stack_waker W := W == random_waker

  pc self S := S == pre_check_lock

}


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


invariant [mutual_exclusion] pc I cs ∧ pc J cs → I = J
#gen_spec


open Lean Meta Elab Command Veil in
scoped elab "⌞? " t:term " ⌟" : term => do
  let lenv ← localEnv.get
  let some mod := lenv.currentModule | throwError s!"Not in a module"
  Term.elabTerm (← `(term| $t $(← mod.sortIdents)*)) none



end Mutex
