import Veil
import Lean.Data.Json
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main

import Test.modelCheckerView
import ProofWidgets.Component.HtmlDisplay


--------------------------------- MODULE 1_mutex -------------------------------

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
-- bug:
--     locked := FALSE;
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
--             has_woken[self] := TRUE;  \* drop
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
--         if (wait_queue_num_wakers /= 0)
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
-- \* BEGIN TRANSLATION (chksum(pcal) = "2541ee33" /\ chksum(tla) = "55930485")
-- VARIABLES locked, wait_queue_num_wakers, wait_queue_wakers, has_woken, pc,
--           stack, waker
type process
-- type seq_t
individual locked : Bool
enum states = { pre_check_lock,
                bug,
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

-- instantiate seq : TotalOrderWithZero seq_t
-- immutable individual one : seq_t

-- individual wait_queue_num_wakers : seq_t

individual wait_queue_wakers : List process

relation has_woken (th: process)
relation pc (self: process) (st: states)
immutable individual none : process

-- vars == << locked, wait_queue_num_wakers, wait_queue_wakers, has_woken, pc,
--            stack, waker >>
function stack_pc : process → List states
function stack_waker : process → List process

relation waker (self: process) (waker: process)

-- ProcSet == (Procs)
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
  -- Global variables
  locked := false
  wait_queue_wakers := []
  has_woken P := false
  pc P S := S == start
  -- Procedure unlock
  waker P W := W == none
  stack_pc P := []
  stack_waker P := []
}


-- pre_check_lock(self) == /\ pc[self] = "pre_check_lock"
--                         /\ IF locked = FALSE
--                               THEN /\ locked' = TRUE
--                                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                               ELSE /\ pc' = [pc EXCEPT ![self] = "bug"]
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
    pc self S := S == bug
}



-- bug(self) == /\ pc[self] = "bug"
--              /\ locked' = FALSE
--              /\ pc' = [pc EXCEPT ![self] = "wait_until"]
--              /\ UNCHANGED << wait_queue_num_wakers, wait_queue_wakers,
--                              has_woken, stack, waker >>
action _bug (self : process) {
  require pc self bug
  locked := false
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
--                                /\ has_woken' = [has_woken EXCEPT ![self] = TRUE]
--                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                           ELSE /\ pc' = [pc EXCEPT ![self] = "check_has_woken"]
--                                /\ UNCHANGED << locked, has_woken, stack >>
--                     /\ UNCHANGED << wait_queue_num_wakers, wait_queue_wakers,
--                                     waker >>
action _check_lock (self : process) {
  require pc self check_lock
  if locked == false then
    locked := true
    has_woken self := true
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
action _check_has_woken (self : process) {
  require pc self check_has_woken
  require has_woken self
  has_woken self := false
  pc self S := S == wait_until
}

-- lock(self) == pre_check_lock(self) \/ bug(self) \/ wait_until(self)
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
  -- assert ` ∃t, waker self t then`
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
  -- let t := stack_pc self
  stack_pc self := cs :: (stack_pc self)
  let random_waker ← pick process
  stack_waker self := random_waker :: (stack_waker self)
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
  require pc self cs
  stack_pc self := Done :: (stack_pc self)
  -- assert `∃t, waker self t`
  let waker_self :| waker self waker_self
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

-- =============================================================================

invariant [mutual_exclusion] ∀ I J, I ≠ J → ¬ (pc I cs ∧ pc J cs)

termination [AllDone] ∀ S, pc S Done

set_option maxHeartbeats 250000
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

open Veil Extract


variable [FinEnum process] [Hashable process] [Ord process]
variable [FinEnum states] [Hashable states] [Ord states]
variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]

variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states)))]

variable [Ord (seq_t × process)]
variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (seq_t × process))))]
variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (seq_t × process))))]

variable [Ord (process × states)]
variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]
variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]

variable [Ord (process × process)]
variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]

variable [Ord (process × List process)]
variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × List process))))]
variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × List process))))]



def instFinEnumForComponents (f : State.Label)
  : (IteratedProd <| List.map FinEnum <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    infer_instance_for_iterated_prod

instance instFinEnumForCodomain [FinEnum (List process)] [FinEnum (List states)] (f : State.Label)
  : (FinEnum ((⌞? State.Label.toCodomain ⌟) f)) := by
  cases f <;>
    dsimp only [IteratedProd, List.foldr, State.Label.toCodomain, State.Label.toCtorIdx] <;>
    infer_instance

instance instFinEnumForComponents' (f : State.Label)
  : FinEnum (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', List.foldr, State.Label.toDomain] <;>
    infer_instance

instance instDecidableEqForComponents' (f : State.Label)
  : DecidableEq (IteratedProd <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd, List.foldr, State.Label.toDomain] <;>
    infer_instance

-- instance instDecidableEqForComponents'' (f : State.Label)
--   : DecidableEq (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
--   cases f <;>
--     dsimp only [IteratedProd', State.Label.toDomain] <;>
--     infer_instance

instance instOrderForComponents' (f : State.Label)
  : Ord (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain] <;>
    infer_instance


#reduce (⌞? State.Label.toDomain ⌟) State.Label.stack_pc

abbrev FieldConcreteType (f : State.Label) : Type :=
  match f with
  | State.Label.locked =>
    ((⌞? State.Label.toCodomain ⌟) State.Label.locked)
  | State.Label.wait_queue_wakers =>
    ((⌞? State.Label.toCodomain ⌟) State.Label.wait_queue_wakers)
  | State.Label.has_woken =>
    Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.has_woken)
  | State.Label.pc =>
    Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.pc)
  /- `stack_pc` is a `function` field -/
  | State.Label.stack_pc =>
    TotalTreeMap (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.stack_pc)
    ((⌞? State.Label.toCodomain ⌟) State.Label.stack_pc)
  /- `stack_stack` is a `function` field -/
  | State.Label.stack_waker =>
    TotalTreeMap (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.stack_waker)
    ((⌞? State.Label.toCodomain ⌟) State.Label.stack_waker)
  /- `stack_` is a `relation` -/
  | State.Label.waker =>
    Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.waker)


instance instReprForComponents [Repr process] [Repr states] (f : State.Label)
  : Repr ((⌞? FieldConcreteType ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', FieldConcreteType, State.Label.toDomain, State.Label.toCodomain] <;>
    infer_instance


instance : Inhabited ((⌞? State ⌟) (⌞? FieldConcreteType ⌟)) := by
  constructor ; constructor <;>
  dsimp only [FieldConcreteType, State.Label.toCodomain] <;>
  -- exact default
  -- infer_instance_for_iterated_prod
  try exact default
  -- set_option trace.Meta.synthInstance.answer true in
  -- apply instInhabitedTotalTreeMapOfFinEnumOfLawfulEqCmpOfTransCmpOfDecidableEq.default



open TotalMapLike
#check instTotalMapLikeAsFieldRep
instance rep (f : State.Label) : FieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f) :=
  -- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
  | State.Label.locked => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
      infer_instance
  | State.Label.wait_queue_wakers =>by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
      infer_instance
  | State.Label.has_woken =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.has_woken)
  | State.Label.pc =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.pc)
  | State.Label.stack_pc =>
    instTotalMapLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.stack_pc)
  | State.Label.stack_waker =>
    instTotalMapLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.stack_waker)
  | State.Label.waker =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.waker)

#check instTotalMapLikeAsFieldRep

instance lawful (f : State.Label): LawfulFieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f)
  ((⌞? rep ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
  | State.Label.locked => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
      infer_instance
  | State.Label.wait_queue_wakers => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
      infer_instance
  | State.Label.has_woken =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.has_woken)
  | State.Label.pc =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.pc)
  | State.Label.stack_pc =>by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
      infer_instance
  | State.Label.stack_waker =>by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
      infer_instance
  | State.Label.waker =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.waker)
end

attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet]
  instFinEnumForComponents in
-- attribute [local dsimpFieldRepresentationGet] FourNodes.equiv_IteratedProd in
#specialize_nextact with FieldConcreteType
  injection_begin
    [FinEnum process] [Hashable process] [Ord process]
    [FinEnum states] [Hashable states] [Ord states]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states)))]

    [Ord (process × states)]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]

    [Ord (process × process)]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
  injection_end => NextAct'



#gen_executable_list! log_entry_being Std.Format
  targeting NextAct'
  injection_begin
    [FinEnum process] [Hashable process] [Ord process]
    [FinEnum states] [Hashable states] [Ord states]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states)))]

    [Ord (process × states)]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]

    [Ord (process × process)]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
  injection_end


set_option trace.veil.debug true in
set_option trace.veil.info true in
deriving_enum_instance_for states


-----------------------------------------------------------------------------
/- For each `enum` type, firstly we need to give its `Ord` instance,
then we can derive `Std.OrientedCmp`, `Std.TransCmp`, and `Std.LawfulEqCmp`  -/

instance : Ord states where
  compare s1 s2 :=
    compare (s1.toCtorIdx) (s2.toCtorIdx)

instance : Std.OrientedCmp (Ord.compare (self := inferInstanceAs (Ord states))) := by
  apply Std.OrientedCmp.mk
  unfold compare inferInstanceAs instOrdStates
  intro a b; cases a <;>
    cases b <;> rfl

instance : Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states))) := by
  apply Std.TransCmp.mk
  unfold compare inferInstanceAs instOrdStates states.toCtorIdx
  -- states.toCtorIdx
  intro a b c;
  intro ha hb;
  cases a <;> cases b <;> cases c <;>
    simp only at ha hb <;>
    /- Here need manually prove -/
    (first | omega | assumption | contradiction)

instance : Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states))) := by
  apply Std.LawfulEqCmp.mk
  unfold compare inferInstanceAs instOrdStates
  intro a b; cases a <;>
    cases b <;> simp

-----------------------------------------------------------------------------


-----------------------------------------------------------------------------
/- We need to give `BEq` instance for each `FieldConcreteType` explicitly. -/
instance [BEq α] [Ord α]
  : BEq (FieldConcreteType α states State.Label.locked) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance_for_iterated_prod

instance [BEq α] [Ord α]
  : BEq (FieldConcreteType α states State.Label.wait_queue_wakers) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance_for_iterated_prod


instance [BEq α] [Ord α]
  : BEq (FieldConcreteType α states State.Label.has_woken) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance_for_iterated_prod

instance [BEq α] [Ord α]
  : BEq (FieldConcreteType α states State.Label.pc) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance_for_iterated_prod

instance [BEq α] [Ord α]
  : BEq (FieldConcreteType α states State.Label.stack_pc) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance_for_iterated_prod

instance [BEq α] [Ord α]
  : BEq (FieldConcreteType α states State.Label.stack_waker) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance_for_iterated_prod

instance [BEq α] [Ord α]
  : BEq (FieldConcreteType α states State.Label.waker) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance_for_iterated_prod
-----------------------------------------------------------------------------


-----------------------------------------------------------------------------
/- We need to give `Hashable` instance for each `FieldConcreteType` explicitly. -/
instance : Hashable states where
  hash s := hash s.toCtorIdx

instance [Ord α] [Hashable α]
  : Hashable (FieldConcreteType α states State.Label.locked) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance_for_iterated_prod

instance [Ord α] [Hashable α]
  : Hashable (FieldConcreteType α states State.Label.wait_queue_wakers) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance_for_iterated_prod

instance [BEq α] [Hashable α] [Ord α]
  : Hashable (FieldConcreteType α states State.Label.has_woken) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance_for_iterated_prod

instance [BEq α] [Hashable α] [Ord α]
  : Hashable (FieldConcreteType α states State.Label.pc) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance_for_iterated_prod

instance [BEq α][Hashable α] [Ord α]
  : Hashable (FieldConcreteType α states State.Label.stack_pc) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance_for_iterated_prod

instance [BEq α] [Hashable α] [Ord α]
  : Hashable (FieldConcreteType α states State.Label.stack_waker) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance_for_iterated_prod

instance [BEq α] [Hashable α] [Ord α]
  : Hashable (FieldConcreteType α states State.Label.waker) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance_for_iterated_prod
-----------------------------------------------------------------------------

#Concretize (Fin 2), states
#assembleInsts

simple_deriving_repr_for' State
deriving instance Repr for Label
deriving instance Inhabited for Theory


def view (st : StateConcrete):=
    hash st
    -- st

instance : (rd : TheoryConcrete) → (st : StateConcrete)
    → Decidable ((fun ρ σ => mutual_exclusion ρ σ) rd st) := by
  intro rd st
  unfold mutual_exclusion
  infer_instance

instance : (rd : TheoryConcrete) → (st : StateConcrete)
    → Decidable ((fun ρ σ => AllDone ρ σ) rd st) := by
  intro rd st
  unfold AllDone
  infer_instance

def modelCheckerResult' := (runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (fun ρ σ => mutual_exclusion ρ σ) ((fun ρ σ => AllDone ρ σ)) {none := 0} view).snd
-- #time #eval modelCheckerResult'
-- #eval (collectTrace' modelCheckerResult')
#html createExpandedGraphDisplay (collectTrace modelCheckerResult').1 (collectTrace modelCheckerResult').2

def linearModelCheckerResult' := (runLinearChecker initVeilMultiExecM nextVeilMultiExecM labelList (fun ρ σ => mutual_exclusion ρ σ) {none := 0} (id) (collectTrace' modelCheckerResult')).snd
-- #time #eval linearModelCheckerResult'.log.reverse

#eval recoverTrace initVeilMultiExecM nextVeilMultiExecM {none := 0} (collectTrace' modelCheckerResult')
-- #check labSeq


open Lean
instance jsonOfTreeSet [Ord α] [ToJson α] : ToJson (Std.TreeSet α) where
  toJson s := Json.arr <| s.toArray.map toJson

instance jsonOfTreeMap [Ord α] [ToJson α] [ToJson β] : ToJson (Std.TreeMap α β) where
  toJson m := Json.arr <| m.toArray.map (fun (k, v) => Json.arr #[toJson k, toJson v])

instance jsonOfTotalTreeMap [Ord α] [ToJson α] [ToJson β] : ToJson (Veil.TotalTreeMap α β) where
  toJson m := Json.arr <| m.val.toArray.map (fun (k, v) => Json.arr #[toJson k, toJson v])

instance [Repr α]: ToJson α where
  toJson := fun a => Json.str (toString (repr a))

instance [ToJson α] [ToJson β]: ToJson (α × β) where
  toJson := fun ⟨a, b⟩ => Json.arr #[toJson a, toJson b]

instance [ToJson α]: ToJson (List α) where
  toJson := fun xs => Json.arr (xs.toArray.map toJson)

instance [Ord α] [ToJson α] : ToJson (Std.TreeSet α) where
  toJson s := Json.arr (s.toArray.map toJson)

instance [Ord α] [ToJson α] [ToJson β]: ToJson (Std.TreeMap α β) where
  toJson m := Json.arr (m.toArray.map (fun (k,v) => Json.arr #[toJson k, toJson v]))

instance [Ord α] [ToJson α] [ToJson β]: ToJson (Veil.TotalTreeMap α β) where
  toJson m := Json.arr (m.val.toArray.map (fun (k,v) => Json.arr #[toJson k, toJson v]))

-- instance : ToJson (FieldConcreteType (Fin 2) states State.Label.locked) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod


-- instance [ToJson α]: ToJson (Veil.IteratedProd' (State.Label.toDomain α states State.Label.pc)) := by
--   dsimp only [Veil.IteratedProd', State.Label.toDomain];
--   infer_instance_for_iterated_prod

-- instance [ToJson α]: ToJson (Veil.IteratedProd' (State.Label.toDomain α states State.Label.has_woken)) := by
--   dsimp only [Veil.IteratedProd', State.Label.toDomain];
--   infer_instance_for_iterated_prod

-- instance [ToJson α] : ToJson (Veil.IteratedProd' (State.Label.toDomain α states State.Label.waker)) := by
--   dsimp only [Veil.IteratedProd', State.Label.toDomain];
--   infer_instance_for_iterated_prod

-- instance [ToJson α] : ToJson (Veil.IteratedProd' (State.Label.toDomain α states State.Label.stack_pc)) := by
--   dsimp only [Veil.IteratedProd', State.Label.toDomain];
--   infer_instance_for_iterated_prod

-- instance [ToJson α] : ToJson (Veil.IteratedProd' (State.Label.toDomain α states State.Label.stack_waker)) := by
--   dsimp only [Veil.IteratedProd', State.Label.toDomain];
--   infer_instance_for_iterated_prod

-- instance [ToJson α] : ToJson (State.Label.toCodomain α states State.Label.stack_waker) := by
--   dsimp only [State.Label.toCodomain];
--   infer_instance_for_iterated_prod

-- instance [ToJson α] : ToJson (State.Label.toCodomain α states State.Label.stack_pc) := by
--   dsimp only [State.Label.toCodomain];
--   infer_instance_for_iterated_prod

instance (f : State.Label) [ToJson α] : ToJson (State.Label.toCodomain α states f) := by
cases f <;>
  dsimp only [State.Label.toCodomain];
  infer_instance_for_iterated_prod

instance (f : State.Label) [ToJson α] : ToJson (Veil.IteratedProd' (State.Label.toDomain α states f)) := by
cases f <;>
  dsimp only [Veil.IteratedProd', State.Label.toDomain];
  infer_instance_for_iterated_prod


def jsonOfTrace {σₛ κ : Type} [ToJson σₛ] [ToJson κ] [Repr κ] (tr : Trace σₛ κ) : Json :=
  let states : Array Json :=
    #[ Json.mkObj [("index", toJson 0), ("fields", toJson tr.start),  ("action", "after_init") ]] ++
    (tr.steps.toArray.mapIdx (fun i st =>
      let idx := i + 1
      Json.mkObj [("index", toJson idx), ("fields", toJson st.next), ("action", toString (repr st.label))]
    ))
  Json.arr states


instance jsonOfState : ToJson StateConcrete where
  toJson := fun s =>
    Json.mkObj
    [ ("locked",            Lean.toJson s.locked)
    , ("wait_queue_wakers", Lean.toJson s.wait_queue_wakers)
    , ("has_woken",         Lean.toJson s.has_woken)
    , ("pc",                Lean.toJson s.pc)
    , ("stack_pc",          Lean.toJson s.stack_pc)
    , ("stack_waker",       Lean.toJson s.stack_waker)
    , ("waker",             Lean.toJson s.waker)
    ]

def labelToJson {κ} [ToString κ] (k : κ) : Json := Lean.toJson (toString k)

#time #eval jsonOfTrace (recoverTrace initVeilMultiExecM nextVeilMultiExecM {none := 0} (collectTrace' modelCheckerResult'))

def statesJson : Json :=
  jsonOfTrace (recoverTrace initVeilMultiExecM nextVeilMultiExecM {none := 0} (collectTrace' modelCheckerResult'))


open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />

end Mutex
