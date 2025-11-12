import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main

import Veil.Core.Tools.Checker.Concrete.modelCheckerView
import ProofWidgets.Component.HtmlDisplay
-- ----- MODULE 0_mutex -----

veil module Mutex
-- EXTENDS Integers, FiniteSets, Sequences, TLC

-- CONSTANTS NumProcs, oNONE

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
-- type seq_t
individual locked : Bool
enum states = { pre_check_lock, wait_until, enqueue_waker,
                check_lock, check_has_woken,
                release_lock, wake_one, wake_one_loop,
                wake_up, start, cs, Done }

instantiate states_isEnum : @states_Enum states
#print states_Enum
-- instantiate seq : TotalOrderWithZero seq_t
-- immutable individual one : seq_t

-- individual wait_queue_num_wakers : seq_t

individual wait_queue_wakers : List process

relation has_woken (th: process)
relation pc (self: process) (st: states)
immutable individual none : process

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

termination [allDone] pc P Done
invariant [mutual_exclusion] ∀ I J, I ≠ J → ¬ (pc I cs ∧ pc J cs)


#gen_spec

open Lean Meta Elab Command Veil in
scoped elab "⌞? " t:term " ⌟" : term => do
  let lenv ← localEnv.get
  let some mod := lenv.currentModule | throwError s!"Not in a module"
  Term.elabTerm (← `(term| $t $(← mod.sortIdents)*)) none

-- #time #check_invariants

section

veil_variables

omit χ χ_rep χ_rep_lawful
-- open Veil Extract


-- variable [FinEnum process]
-- variable [FinEnum states]

-- variable [Hashable process]
-- variable [Hashable states]

-- variable [Ord process]
-- variable [Ord states]

-- variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
-- variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]

-- variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
-- variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states)))]


-- variable [Ord (process × states)]
-- variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]
-- variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]

-- -- variable [Ord (process × process)]
-- variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
-- variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]

-- -- variable [Ord (process × List process)]
-- variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × List process))))]
-- variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × List process))))]


/- `Done`, using `deriveFinEnumInstForToDomain ` -/
-- def instFinEnumForToDomain
--   [FinEnum process]
--   [FinEnum states]
--   (f : State.Label)
--   : (IteratedProd <| List.map FinEnum <| (⌞? State.Label.toDomain ⌟) f) := by
--   cases f <;>
--    infer_instance_for_iterated_prod


/- I'm not sure whether this instance is an `necessity` -/
-- instance instFinEnumForCodomain [FinEnum (List process)] [FinEnum (List states)] (f : State.Label)
--   : (FinEnum ((⌞? State.Label.toCodomain ⌟) f)) := by
--   cases f <;>
--     dsimp only [IteratedProd, List.foldr, State.Label.toCodomain, State.Label.toCtorIdx] <;>
--     infer_instance


/- `Done`, using `deriveFinEnumInstForToDomain' ` -/
/- instance instFinEnumForToDomain'
  [FinEnum process]
  [FinEnum states]
  (f : State.Label)
  : FinEnum (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', List.foldr, State.Label.toDomain] <;>
    infer_instance
-/


/- `BEq` instance for `(IteratedProd' <| (⌞? State.Label.toDomain ⌟) f`
is inferred from `FinEnum` instance. -/


/-
instance instDecidableEqForComponents' (f : State.Label)
  : DecidableEq (IteratedProd <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd, List.foldr, State.Label.toDomain] <;>
    infer_instance

instance instDecidableEqForComponents'' (f : State.Label)
  : DecidableEq (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain] <;>
    infer_instance
-/

-- instance instHashableForComponents (f : State.Label)
--   : Hashable (IteratedProd <| (⌞? State.Label.toDomain ⌟) f) := by
--   cases f <;>
--     dsimp only [IteratedProd, List.foldr, State.Label.toDomain] <;>
--     infer_instance

-- instance instHashableForComponents' (f : State.Label)
--   : Hashable (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
--   cases f <;>
--     dsimp only [IteratedProd', State.Label.toDomain] <;>
--     infer_instance

/- `Done`, using `deriveOrdInst (toDomain := true)` -/
-- instance instOrdForToDomain'
--   (f : State.Label)
--   [Ord process]
--   [Ord states]
--   : Ord (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
--   cases f <;> dsimp only [IteratedProd', State.Label.toDomain] <;>
--   infer_instance


/- It seems that we do not need this instance. -/
-- instance instOrdForToCodomain
--   [Ord process]
--   [Ord states]
--   (f : State.Label)
--   : Ord (⌞? State.Label.toCodomain ⌟ f) := by
--   cases f <;> dsimp only [State.Label.toCodomain] <;> infer_instance


/- `Done`, using `deriveToJsonInst mod (toDomain := true)` -/
-- instance instToJsonForToDomain'
--   [Lean.ToJson process]
--   [Lean.ToJson states]
--   (f : State.Label)
-- : Lean.ToJson (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
-- cases f <;>
--   dsimp only [Veil.IteratedProd', State.Label.toDomain, State.Label.toCodomain];
--   infer_instance_for_iterated_prod

/- `Done`, using `deriveToJsonInst mod (toDomain := false)` -/
-- instance instToJsonForCodomain
--   [Lean.ToJson process]
--   [Lean.ToJson states]
--   (f : State.Label)
-- : Lean.ToJson ((⌞? State.Label.toCodomain ⌟) f) := by
-- cases f <;>
--   dsimp only [Veil.IteratedProd', State.Label.toDomain, State.Label.toCodomain] <;>
--   infer_instance_for_iterated_prod
deriving_FinOrdToJson_Domain


/-`Done`, using `specify_FieldConcreteType` -/
-- abbrev FieldConcreteType
--   [Ord process]
--   [Ord states]
--   (f : State.Label)
--   : Type :=
--   match f with
--   | State.Label.locked =>
--     ((⌞? State.Label.toCodomain ⌟) State.Label.locked)
--   | State.Label.wait_queue_wakers =>
--     ((⌞? State.Label.toCodomain ⌟) State.Label.wait_queue_wakers)
--   | State.Label.has_woken =>
--     Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.has_woken)
--   | State.Label.pc =>
--     Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.pc)
--   /- `stack_pc` is a `function` field -/
--   | State.Label.stack_pc =>
--     Veil.TotalTreeMap (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.stack_pc)
--     ((⌞? State.Label.toCodomain ⌟) State.Label.stack_pc)
--   /- `stack_stack` is a `function` field -/
--   | State.Label.stack_waker =>
--     Veil.TotalTreeMap (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.stack_waker)
--     ((⌞? State.Label.toCodomain ⌟) State.Label.stack_waker)
--   /- `stack_` is a `relation` -/
--   | State.Label.waker =>
--     Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.waker)
specify_FieldConcreteType


/- `638`-`668`, replaced by command `deriving_BEq_FieldConcreteType` -/
/- It seems that all the type (mksorts, e.g., process, states) are `DeciableEq`. -/
-- instance [Ord process] [Ord states]
--   : BEq (FieldConcreteType process states State.Label.locked) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Ord process] [Ord states]
--   : BEq (FieldConcreteType process states State.Label.wait_queue_wakers) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Ord process] [Ord states]
--   : BEq (FieldConcreteType process states State.Label.has_woken) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Ord process] [Ord states]
--   : BEq (FieldConcreteType process states State.Label.pc) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Ord process] [Ord states]
--   : BEq (FieldConcreteType process states State.Label.stack_pc) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Ord process] [Ord states]
--   : BEq (FieldConcreteType process states State.Label.stack_waker) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Ord process] [Ord states]
--   : BEq (FieldConcreteType process states State.Label.waker) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod
deriving_BEq_FieldConcreteType


/- `675`-`706`, replaced by command `deriving_Hashable_FieldConcreteType` -/
-- instance [Ord process] [Ord states]
--   : Hashable (FieldConcreteType process states State.Label.locked) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Ord process] [Ord states] [Hashable states] [Hashable process]
--   : Hashable (FieldConcreteType process states State.Label.wait_queue_wakers) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Ord process] [Ord states] [Hashable process] [Hashable states]
--   : Hashable (FieldConcreteType process states State.Label.has_woken) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Ord process] [Ord states] [Hashable process] [Hashable states]
--   : Hashable (FieldConcreteType process states State.Label.pc) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Ord process] [Ord states] [Hashable process] [Hashable states]
--   : Hashable (FieldConcreteType process states State.Label.stack_pc) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Ord process] [Ord states] [Hashable process] [Hashable states]
--   : Hashable (FieldConcreteType process states State.Label.stack_waker) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Ord process] [Ord states] [Hashable process] [Hashable states]
--   : Hashable (FieldConcreteType process states State.Label.waker) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod
deriving_Hashable_FieldConcreteType


-- instance instReprForComponents
--   [Repr process]
--   [Repr states]
--   [Ord process]
--   [Ord states]
--   (f : State.Label)
--   : Repr ((⌞? FieldConcreteType ⌟) f) := by
--   cases f <;>
--     dsimp only [IteratedProd', FieldConcreteType, State.Label.toDomain, State.Label.toCodomain] <;>
--     infer_instance

/- `Done`, using `deriving_inhabited_state` -/
/- I am `not` sure here are the minimally required instances. -/
-- instance
--   [Ord process]
--   [Ord states]
--   [FinEnum process]
--   [FinEnum states]
--   [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
--   [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
--   [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
--   [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
--   : Inhabited ((⌞? State ⌟) (⌞? FieldConcreteType ⌟))
--   := by
--   constructor ; constructor <;>
--   dsimp only [FieldConcreteType, State.Label.toCodomain, IteratedProd'] <;>
--   try exact default
  -- exact default
  -- infer_instance_for_iterated_prod
  -- set_option trace.Meta.synthInstance.answer true in
  -- apply instInhabitedTotalTreeMapOfFinEnumOfLawfulEqCmpOfTransCmpOfDecidableEq.default
deriving_Inhabited_State



-- instance rep
--   [FinEnum process]
--   [FinEnum states]
--   [Ord process]
--   [Ord states]
--   [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
--   [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
--   [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
--   [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
--   (f : State.Label)
-- : FieldRepresentation ((⌞? State.Label.toDomain ⌟) f) ((⌞? State.Label.toCodomain ⌟) f) ((⌞? FieldConcreteType ⌟) f)
-- := by
--   cases f <;>
--   first
--   | (dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain]; infer_instance)
--   | (exact instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForToDomain ⌟) _))
--   | (exact instTotalMapLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForToDomain ⌟) _))
deriving_rep_FieldRepresentation


-- exact instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForToDomain ⌟) State.Label.has_woken)
  -- match f with
  -- | State.Label.locked => by
  --     dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
  --     infer_instance
  -- | State.Label.wait_queue_wakers =>by
  --     dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
  --     infer_instance
  -- | State.Label.has_woken =>
  --   instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForToDomain ⌟) State.Label.has_woken)
  -- | State.Label.pc =>
  --   instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForToDomain ⌟) State.Label.pc)
  -- | State.Label.stack_pc =>
  --   instTotalMapLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForToDomain ⌟) State.Label.stack_pc)
  -- | State.Label.stack_waker =>
  --   instTotalMapLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForToDomain ⌟) State.Label.stack_waker)
  -- | State.Label.waker =>
  --   instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForToDomain ⌟) State.Label.waker)


instance lawful
  [FinEnum process]
  [Ord process]
  [FinEnum states]
  [Ord states]
  [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
  [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
  [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
  [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
  -- [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]
  -- [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × states ))))]
-- variable [Ord (process × process)]
  -- [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × process ))))]
  -- [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
-- variable [Ord (process × List process)]
  -- [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × List process))))]
  -- [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × List process))))]
  -- [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × List process))))]
  (f : State.Label)
  : Veil.LawfulFieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f)
  ((⌞? instRepForFieldRepresentation ⌟) f) :=
by
  -- cases f <;>
  -- first
  -- | (dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, instRepForFieldRepresentation, id]; infer_instance)
  -- | (exact Veil.instFinsetLikeLawfulFieldRep (Veil.IteratedProd'.equiv) ((⌞? instFinEnumForToDomain ⌟) _))
  cases f <;>
    first
    |
      /- The term ord matters, why? -/
      (dsimp only [FieldConcreteType, State.Label.toDomain, State.Label.toCodomain, instRepForFieldRepresentation,
          Veil.IteratedProd', id];
        infer_instance)
    | (exact Veil.instFinsetLikeLawfulFieldRep Veil.IteratedProd'.equiv ((instFinEnumForToDomain process states) _))


deriving_lawful_FieldRepresentation

  -- match f with
  -- | State.Label.locked => by
  --     dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
  --     infer_instance
  -- | State.Label.wait_queue_wakers => by
  --     dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
  --     infer_instance
  -- | State.Label.has_woken =>
  --   instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForToDomain ⌟) State.Label.has_woken)
  -- | State.Label.pc =>
  --   instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForToDomain ⌟) State.Label.pc)
  -- | State.Label.stack_pc =>by
  --     dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
  --     infer_instance
  -- | State.Label.stack_waker =>by
  --     dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
  --     infer_instance
  -- | State.Label.waker =>
  --   instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForToDomain ⌟) State.Label.waker)
-- #synth states_Enum states

-- deriving_decidable_props


end

attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet] instFinEnumForToDomain in
-- attribute [local dsimpFieldRepresentationGet] FourNodes.equiv_IteratedProd in
#specialize_nextact with FieldConcreteType
  injection_begin
    [FinEnum process]
    [Hashable process]
    [Ord process]
    [FinEnum states]
    [Hashable states]
    [Ord states]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]

    -- [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (List process))))]
    -- [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (List process))))]

    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
    -- [Ord (process × states)]
    -- [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]
    -- [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]
    -- [Ord (process × process)]
    -- [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
    -- [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
  injection_end => NextAct'


#gen_executable_list! log_entry_being Std.Format
  targeting NextAct'
  injection_begin
    [FinEnum process]
    [Hashable process]
    [Ord process]
    [FinEnum states]
    [Hashable states]
    [Ord states]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]

    -- [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (List process))))]
    -- [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (List process))))]

    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
    -- [Ord (process × states)]
    -- [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]
    -- [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]
    -- [Ord (process × process)]
    -- [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
    -- [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
  injection_end


instance (α β :Type) [Ord α] [Ord β]
[Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord α)))]
[Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord α)))]
[Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord β)))]
[Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord β)))]
:  Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (α  × β)))) := by
  apply Std.TransCmp.mk
  unfold compare inferInstanceAs instOrdProd_veil
  intro a b c;
  intro ha hb;
  cases a <;> cases b <;> cases c <;>
    simp only at ha hb <;>
    infer_instance
    /- Here need manually prove -/
    (first | omega | assumption | contradiction)



set_option trace.veil.info true in
set_option trace.veil.debug true in

/- TODO: we need to derive FinEnum instances for all `enum` type. -/
-- deriving_enum_instance_for states



-- instance : FinEnum states :=
--       FinEnum.ofList
--         [states.pre_check_lock, states.wait_until, states.enqueue_waker, states.check_lock, states.check_has_woken,
--           states.release_lock, states.wake_one, states.wake_one_loop, states.wake_up, states.start, states.cs,
--           states.Done]
--         (by simp; exact Mutex.states_Enum.states_complete)
-- instance : Ord states where
--   compare s1 s2 :=
--     compare (s1.toCtorIdx) (s2.toCtorIdx)

-- instance : Hashable states where
--   hash s := hash s.toCtorIdx


-- instance : Std.OrientedCmp (Ord.compare (self := inferInstanceAs (Ord states))) := by
--   apply Std.OrientedCmp.mk
--   unfold compare inferInstanceAs instOrdStates
--   intro a b; cases a <;>
--     cases b <;> rfl


-- instance : Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states))) := by
--   apply Std.TransCmp.mk
--   unfold compare inferInstanceAs instOrdStates states.toCtorIdx
--   -- states.toCtorIdx
--   intro a b c;
--   intro ha hb;
--   cases a <;> cases b <;> cases c <;>
--     simp only at ha hb <;>
--     /- Here need manually prove -/
--     (first | omega | assumption | contradiction)


-- instance : Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states))) := by
--   apply Std.LawfulEqCmp.mk
--   unfold compare inferInstanceAs instOrdStates
--   intro a b; cases a <;>
--     cases b <;> simp

deriving_Enum_Insts


-- instance [BEq α] [Ord α] [Hashable α]
--   : BEq (FieldConcreteType α states State.Label.locked) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [BEq α] [Ord α] [Hashable α]
--   : BEq (FieldConcreteType α states State.Label.wait_queue_wakers) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [BEq α] [Ord α] [Hashable α]
--   : BEq (FieldConcreteType α states State.Label.has_woken) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [BEq α] [Ord α] [Hashable α]
--   : BEq (FieldConcreteType α states State.Label.pc) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [BEq α] [Ord α] [Hashable α]
--   : BEq (FieldConcreteType α states State.Label.stack_pc) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [BEq α] [Ord α] [Hashable α]
--   : BEq (FieldConcreteType α states State.Label.stack_waker) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [BEq α] [Ord α] [Hashable α]
--   : BEq (FieldConcreteType α states State.Label.waker) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

/- It makes no different to the context. -/
instance (f : State.Label) [BEq α] [Ord α] [Hashable α]
  : BEq (FieldConcreteType α states f) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  cases f <;>
  infer_instance_for_iterated_prod


-- instance [Ord α] [Hashable α]
--   : Hashable (FieldConcreteType α states State.Label.locked) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Ord α] [Hashable α]
--   : Hashable (FieldConcreteType α states State.Label.wait_queue_wakers) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [BEq α] [Ord α] [Hashable α]
--   : Hashable (FieldConcreteType α states State.Label.has_woken) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [BEq α] [Ord α] [Hashable α]
--   : Hashable (FieldConcreteType α states State.Label.pc) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [BEq α] [Ord α] [Hashable α]
--   : Hashable (FieldConcreteType α states State.Label.stack_pc) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [BEq α] [Ord α] [Hashable α]
--   : Hashable (FieldConcreteType α states State.Label.stack_waker) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [BEq α] [Ord α] [Hashable α]
--   : Hashable (FieldConcreteType α states State.Label.waker) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod


-- instance [BEq α] [Ord α] [Hashable α] (f : State.Label)
--   : Hashable (FieldConcreteType α states f) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   cases f <;>
--   infer_instance_for_iterated_prod


#Concretize (Fin 3), states

deriving_BEqHashable_ConcreteState
simple_deriving_repr_for' State
deriving instance Repr for Label
deriving instance Inhabited for Theory
deriving_toJson_for_state
deriving_DecidableProps_state



def view (st : StateConcrete) := hash st


def modelCheckerResult' :=
  (runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (fun ρ σ => mutual_exclusion ρ σ) ((fun ρ σ => allDone ρ σ)) {none := 0} view).snd

-- #eval modelCheckerResult'
-- #eval recoverTrace initVeilMultiExecM nextVeilMultiExecM {none := 0} (collectTrace' modelCheckerResult')


/- `Done`, using `deriveToJsonFor` -/
-- instance jsonOfState : ToJson StateConcrete where
--   toJson := fun s =>
--     Json.mkObj
--     [ ("locked",            Lean.toJson s.locked)
--     , ("wait_queue_wakers", Lean.toJson s.wait_queue_wakers)
--     , ("has_woken",         Lean.toJson s.has_woken)
--     , ("pc",                Lean.toJson s.pc)
--     , ("stack_pc",          Lean.toJson s.stack_pc)
--     , ("stack_waker",       Lean.toJson s.stack_waker)
--     , ("waker",             Lean.toJson s.waker)
--     ]
-- deriving_toJson_for_state

open Lean

def statesJson : Json :=
  toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM {none := 0} (collectTrace' modelCheckerResult'))

#check statesJson

#eval statesJson
open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />


end Mutex
