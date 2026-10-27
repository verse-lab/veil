module

public import Veil

/-
Veil translation/adaptation of TLA+ material from tlaplus/Examples.
Copyright (c) 2016: The TLA+ project and other contributors.
Upstream MIT license: Benchmarks/TLA/TLAPlusExamples/LICENSE
-/

veil module Peterson

-- -----------------------------------------------------------------------------
-- This module contains the specification for Peterson's Lock Algorithm.
-- https://en.wikipedia.org/wiki/Peterson%27s_algorithm
--
-- TLA+ Source :
-- https://github.com/tlaplus/Examples/blob/9ece37b2e6d5cab0de16582ea81733ce5f586a84/specifications/locks_auxiliary_vars/Peterson.tla
-- ---------------------------------- -------------------------------------------


/-
Peterson Algorithm is a two-thread/process concurrent algorithm, so we only
need to define two processes, `P1` and `P2`, here.
* `turn` is used as a flag that indicates which process
has the right to enter the critical section.
* `wantEnter p` is used to indicate whether process `p` wants to enter the critical section.
* `pc` is short for program counter, which indicates the state of each process.
-/
enum Phase = { idle, request, yieldTurn, waiting, critical, release }
enum Process = { P1, P2 }
individual turn : Process
relation wantEnter : Process → Bool
relation pc : Process → Phase → Bool
#gen_state



after_init {
  wantEnter P := false
  turn := P1
  pc P S := S == idle

}

action beginRequest (self : Process) {
  require pc self idle
  pc self S := S == request
}


/-
This action states that the process begin to
have the willing to enter the critical section.
-/
action prepareYield (self : Process) {
  require pc self request
  wantEnter self := true
  pc self S := S == yieldTurn
}


/-
This is the key step to make it successful to achieve mutual exclusion.
When a process wants to enter the critical section,
it sets the `turn` flag to the other process politely,
indicating that it is willingness to yield
the right to enter the critical section to the other process.
 -/
action yieldAndWaiting (self : Process) {
  require pc self yieldTurn
  turn := if self = P1 then P2 else P1
  pc self S := S == waiting
}


/-
Now, finally the process can enter the critical section.
The condition is that either the other process does not want to enter
the critical section, or it is this process's turn.
-/
action enterCS (self : Process) {
  require pc self waiting
  require ¬ wantEnter (if self = P1 then P2 else P1) ∨ turn = self
  pc self S := S == critical
}


/- The process can leave the critical section whenever it would like to. -/
action releaseCS (self : Process) {
  require pc self critical
  pc self S := S == release
}


/-
After leaving the critical section, the process will return
to the initial state `idle`.
 -/
action returnIdle (self : Process) {
  require pc self release
  wantEnter self := false
  pc self S := S == idle
}


/-
This is usually one of the most important properties of
a concurrent programming algorithm, which says that
no two processes can be in their critical sections at the same time.
-/
ghost relation lockcs (i : Process) := pc i critical ∨ pc i release

safety [mutual_exclusion]
  ∀ i j, i ≠ j → ¬(lockcs i ∧ lockcs j)


-- Some helpful invariants
invariant [pc_total] pc P idle ∨ pc P request ∨ pc P yieldTurn ∨ pc P waiting ∨ pc P critical ∨ pc P release
invariant [unique_phase] pc P S ∧ pc P T → S = T
invariant [flag_consistency] ∀p, wantEnter p ↔ (pc p yieldTurn ∨ pc p waiting ∨ pc p critical ∨ pc p release)
invariant [progress_critical]
  ∀p, (pc p critical ∨ pc p release) →
  (turn = p ∨
    (pc (if p = P1 then P2 else P1) idle ∨
     pc (if p = P1 then P2 else P1) request ∨
     pc (if p = P1 then P2 else P1) yieldTurn))


termination false

#gen_spec

-- #check_invariants

-- TLC checks this spec with `Benchmarks/TLA/TLAPlusExamples/Peterson.cfg`, which sets no
-- constants: the TLA+ spec fixes its processes as `ProcSet == 1..2`.
--
-- The instantiation (first `{ ... }` argument) sets the module's `type`s and `param`s. It is
-- empty here: the two processes are the `enum Process = { P1, P2 }` above, and an `enum`
-- needs no instantiation.
-- The theory (second `{ ... }` argument) sets the module's `immutable` fields. There are none,
-- hence `{ }`.
--
-- The other settings of the cfg:
-- * `INVARIANTS TypeOK Inv`: `#model_check` checks every `invariant` and `safety` clause of the
--   module. `flag_consistency`, `progress_critical` and `mutual_exclusion` are the three
--   conjuncts of `Inv`. `pc_total` and `unique_phase` check that the relation `pc` gives each
--   process exactly one phase, which the TLA+ function `pc` does by its type (`TypeOK`).
-- * The cfg has no `CHECK_DEADLOCK`, so TLC checks for deadlocks. With `termination false`
--   above, Veil also reports every state without successors as a deadlock.
-- Options:
-- * The check names no mode, so its search starts in Lean's interpreter and moves to a compiled
--   checker once that is built.
#model_check{ }{ }

end Peterson
