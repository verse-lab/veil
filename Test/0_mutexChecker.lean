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


assumption [zero_one] next seq.zero one


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


action _pre_check_lock (self : process) {
  require pc self pre_check_lock
  if !locked then
    locked := true
    /- We use `tail_stack_pc_state` to keep track of the `top` of the stack -/
    -- let head_stack_pc_state :| stack_pc self tail_stack_pc head_stack_pc_state
    -- pc self head_stack_pc_state := true
    -- tail_stack_pc ← dec tail_stack_pc
    -- tail_stack_waker ← succ tail_stack_waker
  else
    pc self S := S == wait_until
}


action _wait_until (self : process) {
  require pc self wait_until
  pc self S := S == enqueue_waker
}

action _enqueue_waker (self : process) {
  require pc self enqueue_waker

  -- wait_queue_wakers tail_wait_queue S := S == self
  -- tail_wait_queue ← succ tail_wait_queue
  -- wait_queue_num_wakers ← succ wait_queue_num_wakers

  pc self S := S == check_lock
}


action _check_lock (self : process) {
  require pc self check_lock
  if !locked then
    locked := true
    -- let head_stack_pc_state :| stack_pc self tail_stack_pc head_stack_pc_state
    -- pc self S := S == head_stack_pc_state
    -- tail_stack_pc ← dec tail_stack_pc
    -- tail_stack_waker ← dec tail_stack_waker
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

    -- let headwaker_stack_waker :| stack_waker self tail_stack_waker headwaker_stack_waker
    -- waker self W := W == headwaker_stack_waker
    -- tail_stack_waker ← dec tail_stack_waker
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
  -- else
    -- let head_stack_pc_state :| stack_pc self tail_stack_pc head_stack_pc_state
    -- pc self S := S == head_stack_pc_state
    -- tail_stack_pc ← dec tail_stack_pc

    -- let headwaker_stack_waker :| stack_waker self tail_stack_waker headwaker_stack_waker
    -- waker self W := W == headwaker_stack_waker
    -- tail_stack_waker ← dec tail_stack_waker
}


action _wake_up (self : process) {
  require pc self wake_up
  let waker_self :| waker self waker_self
  if has_woken waker_self = false then
    has_woken waker_self := true
    -- let head_stack_pc_state :| stack_pc self tail_stack_pc head_stack_pc_state
    -- pc self S := S == head_stack_pc_state
    -- tail_stack_pc ← dec tail_stack_pc

    -- let headwaker_stack_waker :| stack_waker self tail_stack_waker headwaker_stack_waker
    -- waker self W := W == headwaker_stack_waker
    -- tail_stack_waker ← dec tail_stack_waker
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

  -- let random_waker ← pick process
  -- stack_waker self tail_stack_waker W := W == random_waker

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

-- #time #check_invariants

section

veil_variables


omit χ χ_rep χ_rep_lawful

open Veil Extract


variable [FinEnum process] [Hashable process] [Ord process]
variable [FinEnum seq_t] [Hashable seq_t] [Ord seq_t]
variable [FinEnum states] [Hashable states] [Ord states]
variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord seq_t)))]
variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord seq_t)))]
variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
variable [Ord (seq_t × process)]
variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (seq_t × process))))]
variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (seq_t × process))))]

variable [Ord (process × states)]
variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]
variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]

variable [Ord (process × seq_t × states)]
variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × seq_t × states))))]
variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × seq_t × states))))]

variable [Ord (process × seq_t × process)]
variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × seq_t × process))))]
variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × seq_t × process))))]

variable [Ord (process × process)]
variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]


def instFinEnumForComponents (f : State.Label)
  : (IteratedProd <| List.map FinEnum <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    infer_instance_for_iterated_prod

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

instance instHashableForComponents (f : State.Label)
  : Hashable (IteratedProd <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd, List.foldr, State.Label.toDomain] <;>
    infer_instance

instance instHashableForComponents' (f : State.Label)
  : Hashable (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain] <;>
    infer_instance


instance [Ord α] [Ord β] : Ord (α × β) where
  compare x y := match x, y with
    | (a, b), (a', b') => compare a a' |>.then (compare b b')

instance instOrderForComponents' (f : State.Label)
  : Ord (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain] <;>
    infer_instance


instance (f : State.Label) : Ord (IteratedProd' (State.Label.toDomain process seq_t states f)) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain] <;>
    infer_instance

-- instance :  Ord (IteratedProd' (State.Label.toDomain node rmStateType tmStateType State.Label.rmState)) := by
--   dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain]
--   infer_instance

-- instance : Ord (IteratedProd' (State.Label.toDomain node rmStateType tmStateType  State.Label.tmState)) := by
--   dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain]
--   infer_instance

-- instance :  Ord (IteratedProd' (State.Label.toDomain node rmStateType tmStateType  State.Label.preparedRM)) := by
--   dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain]
--   infer_instance

-- instance :  Ord (IteratedProd' (State.Label.toDomain node rmStateType tmStateType  State.Label.tmPrepared)) := by
--   dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain]
--   infer_instance

-- instance :  Ord (IteratedProd' (State.Label.toDomain node rmStateType tmStateType  State.Label.commitMsg)) := by
--   dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain]
--   infer_instance

-- instance : Ord (IteratedProd' (State.Label.toDomain node rmStateType tmStateType  State.Label.abortMsg)) := by
--   dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain]
--   infer_instance


-- individual locked : Bool
-- individual wait_queue_num_wakers : seq_t
-- relation wait_queue_wakers (index: seq_t) (th: process)
-- individual head_wait_queue : seq_t
-- individual tail_wait_queue : seq_t
-- relation has_woken (th: process)
-- relation pc (self: process) (st: states)
-- relation stack_pc (self: process) (index : seq_t) (pc: states)
-- individual head_stack_pc : seq_t
-- individual tail_stack_pc : seq_t
-- relation stack_waker (self: process) (index : seq_t) (waker: process)
-- individual head_stack_waker : seq_t
-- individual tail_stack_waker : seq_t
-- relation waker (self: process) (waker: process)

#print State
abbrev FieldConcreteType (f : State.Label) : Type :=
  match f with
  | State.Label.locked =>
    ((⌞? State.Label.toCodomain ⌟) State.Label.locked)
  | State.Label.wait_queue_num_wakers =>
    ((⌞? State.Label.toCodomain ⌟) State.Label.wait_queue_num_wakers)
  | State.Label.wait_queue_wakers => Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.wait_queue_wakers)
  | State.Label.head_wait_queue =>
    ((⌞? State.Label.toCodomain ⌟) State.Label.head_wait_queue)
  | State.Label.tail_wait_queue =>
    ((⌞? State.Label.toCodomain ⌟) State.Label.tail_wait_queue)
  | State.Label.has_woken => Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.has_woken)
  | State.Label.pc => Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.pc)
  | State.Label.stack_pc => Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.stack_pc)
  | State.Label.head_stack_pc =>
    ((⌞? State.Label.toCodomain ⌟) State.Label.head_stack_pc)
  | State.Label.tail_stack_pc =>
    ((⌞? State.Label.toCodomain ⌟) State.Label.tail_stack_pc)
  | State.Label.stack_waker => Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.stack_waker)
  | State.Label.head_stack_waker =>
    ((⌞? State.Label.toCodomain ⌟) State.Label.head_stack_waker)
  | State.Label.tail_stack_waker =>
    ((⌞? State.Label.toCodomain ⌟) State.Label.tail_stack_waker)
  | State.Label.waker => Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.waker)


instance instReprForComponents [Repr process] [Repr seq_t] [Repr states] (f : State.Label)
  : Repr ((⌞? FieldConcreteType ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', FieldConcreteType, State.Label.toDomain, State.Label.toCodomain] <;>
    infer_instance

instance : Inhabited ((⌞? State ⌟) (⌞? FieldConcreteType ⌟)) := by
  constructor ; constructor <;>
  dsimp only [FieldConcreteType, State.Label.toCodomain] <;>
  exact default


instance rep (f : State.Label) : FieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f) :=
  -- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
  | State.Label.locked => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
      infer_instance
  | State.Label.wait_queue_num_wakers => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
      infer_instance
  | State.Label.wait_queue_wakers =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.wait_queue_wakers)
  | State.Label.head_wait_queue => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
      infer_instance
  | State.Label.tail_wait_queue => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
      infer_instance
  | State.Label.has_woken =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.has_woken)
  | State.Label.pc =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.pc)
  | State.Label.stack_pc =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.stack_pc)
  | State.Label.head_stack_pc => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
      infer_instance
  | State.Label.tail_stack_pc => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
      infer_instance
  | State.Label.stack_waker =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.stack_waker)
  | State.Label.head_stack_waker => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
      infer_instance
  | State.Label.tail_stack_waker => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
      infer_instance
  | State.Label.waker =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.waker)



instance lawful (f : State.Label): LawfulFieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f)
  ((⌞? rep ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
  | State.Label.locked => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
      infer_instance
  | State.Label.wait_queue_num_wakers => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
      infer_instance
  | State.Label.wait_queue_wakers =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.wait_queue_wakers)
  | State.Label.head_wait_queue => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
      infer_instance
  | State.Label.tail_wait_queue => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
      infer_instance
  | State.Label.has_woken =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.has_woken)
  | State.Label.pc =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.pc)
  | State.Label.stack_pc =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.stack_pc)
  | State.Label.head_stack_pc => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
      infer_instance
  | State.Label.tail_stack_pc => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
      infer_instance
  | State.Label.stack_waker =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.stack_waker)
  | State.Label.head_stack_waker => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
      infer_instance
  | State.Label.tail_stack_waker => by
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
    [FinEnum seq_t] [Hashable seq_t] [Ord seq_t]
    [FinEnum states] [Hashable states] [Ord states]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord seq_t)))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord seq_t)))]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
    [Ord (seq_t × process)]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (seq_t × process))))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (seq_t × process))))]

    [Ord (process × states)]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]

    [Ord (process × seq_t × states)]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × seq_t × states))))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × seq_t × states))))]

    [Ord (process × seq_t × process)]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × seq_t × process))))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × seq_t × process))))]

    [Ord (process × process)]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
  injection_end => NextAct'


#gen_executable_list! log_entry_being Std.Format
  targeting NextAct'
  injection_begin
    [FinEnum process] [Hashable process] [Ord process]
    [FinEnum seq_t] [Hashable seq_t] [Ord seq_t]
    [FinEnum states] [Hashable states] [Ord states]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord seq_t)))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord seq_t)))]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
    [Ord (seq_t × process)]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (seq_t × process))))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (seq_t × process))))]

    [Ord (process × states)]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]

    [Ord (process × seq_t × states)]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × seq_t × states))))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × seq_t × states))))]

    [Ord (process × seq_t × process)]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × seq_t × process))))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × seq_t × process))))]

    [Ord (process × process)]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
    [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
  injection_end

set_option trace.veil.debug true in
set_option trace.veil.info true in
deriving_enum_instance_for states

-- inductive states where
--       | pre_check_lock
--       | wait_until
--       | enqueue_waker
--       | check_lock
--       | check_has_woken
--       | release_lock
--       | wake_one
--       | wake_one_loop
--       | wake_up
--       | start
--       | cs
--       | Done
-- deriving DecidableEq, Repr, Inhabited, Nonempty


-- instance : Mutex.states_Enum states where
--       pre_check_lock := states.pre_check_lock
--       wait_until := states.wait_until
--       enqueue_waker := states.enqueue_waker
--       check_lock := states.check_lock
--       check_has_woken := states.check_has_woken
--       release_lock := states.release_lock
--       wake_one := states.wake_one
--       wake_one_loop := states.wake_one_loop
--       wake_up := states.wake_up
--       start := states.start
--       cs := states.cs
--       Done := states.Done
--       states_distinct := (by simp_all) /- `decide` can not prove the goal -/
--       states_complete := (by intro x; cases x <;> decide)


instance : FinEnum states :=
      FinEnum.ofList
        [states.pre_check_lock, states.wait_until, states.enqueue_waker, states.check_lock, states.check_has_woken,
          states.release_lock, states.wake_one, states.wake_one_loop, states.wake_up, states.start, states.cs,
          states.Done]
        (by simp; exact Mutex.states_Enum.states_complete)


instance : Ord states where
  compare s1 s2 :=
    compare (s1.toCtorIdx) (s2.toCtorIdx)

instance : Hashable states where
  hash s := hash s.toCtorIdx

instance [Ord α] [FinEnum α]: BEq (Std.TreeSet α) where
  beq s1 s2 :=
    s1.toArray == s2.toArray


instance :  Std.OrientedCmp (Ord.compare (self := inferInstanceAs (Ord states))) := by
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

instance (n : Nat): TotalOrderWithZero (Fin n.succ) where
  le := fun x y => x.val ≤ y.val
  le_refl := by simp
  le_trans := by simp ; omega
  le_antisymm := by simp ; omega
  le_total := by simp ; omega
  zero := ⟨0, by simp⟩
  zero_le := by simp

instance (n : Nat) : DecidableRel (TotalOrderWithZero.le (t := Fin n.succ)) := by
  dsimp [TotalOrderWithZero.le] ; infer_instance_for_iterated_prod

variable {n_process n_seq_t : Nat}

local macro "⌞ " t:term " ⌟" : term =>
  `(((($t (Fin n_process.succ) (Fin n_seq_t.succ.succ) states))))

local macro "⌞State⌟" : term =>
  `(((⌞ State ⌟) ⌞ FieldConcreteType ⌟))

local macro "⌞_ " t:term " _⌟" : term =>
  `((⌞ $t (⌞ Theory ⌟) (⌞State⌟) ⌟))

local instance (th : ⌞ Theory ⌟) : Decidable (lt x y th) := by
  dsimp [lt]
  infer_instance

local instance  (th : ⌞ Theory ⌟) : Decidable (next x y th) := by
  infer_instance


#Concretize (Fin 2), (Fin 2), states

#print State


instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : BEq (FieldConcreteType α β states State.Label.locked) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance_for_iterated_prod


instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : BEq (FieldConcreteType α β states State.Label.wait_queue_num_wakers) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : BEq (FieldConcreteType α β states State.Label.wait_queue_wakers) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : BEq (FieldConcreteType α β states State.Label.head_wait_queue) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : BEq (FieldConcreteType α β states State.Label.tail_wait_queue) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance


instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : BEq (FieldConcreteType α β states State.Label.has_woken) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : BEq (FieldConcreteType α β states State.Label.pc) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance


instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : BEq (FieldConcreteType α β states State.Label.stack_pc) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance


instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : BEq (FieldConcreteType α β states State.Label.head_stack_pc) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : BEq (FieldConcreteType α β states State.Label.tail_stack_pc) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : BEq (FieldConcreteType α β states State.Label.stack_waker) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : BEq (FieldConcreteType α β states State.Label.head_stack_waker) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : BEq (FieldConcreteType α β states State.Label.tail_stack_waker) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : BEq (FieldConcreteType α β states State.Label.waker) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance



instance [Hashable α] [BEq α] [Ord α]: Hashable (Std.TreeSet α) where
  hash s := hash s.toArray

/- ad-hoc -/
instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : Hashable (FieldConcreteType α β states State.Label.locked) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance_for_iterated_prod


instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : Hashable (FieldConcreteType α β states State.Label.wait_queue_num_wakers) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : Hashable (FieldConcreteType α β states State.Label.wait_queue_wakers) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : Hashable (FieldConcreteType α β states State.Label.head_wait_queue) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : Hashable (FieldConcreteType α β states State.Label.tail_wait_queue) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance


instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : Hashable (FieldConcreteType α β states State.Label.has_woken) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : Hashable (FieldConcreteType α β states State.Label.pc) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance


instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : Hashable (FieldConcreteType α β states State.Label.stack_pc) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance


instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : Hashable (FieldConcreteType α β states State.Label.head_stack_pc) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : Hashable (FieldConcreteType α β states State.Label.tail_stack_pc) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : Hashable (FieldConcreteType α β states State.Label.stack_waker) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : Hashable (FieldConcreteType α β states State.Label.head_stack_waker) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : Hashable (FieldConcreteType α β states State.Label.tail_stack_waker) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [Ord α] [Hashable α] [FinEnum β] [Ord β] [Hashable β]
  : Hashable (FieldConcreteType α β states State.Label.waker) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance



#assembleInsts


simple_deriving_repr_for' State
deriving instance Repr for Label
deriving instance Inhabited for Theory


def TreeSet.ofList [Ord α] (xs : List α) : Std.TreeSet α :=
  xs.foldl (fun s a => s.insert a) .empty

def mapTreeSet [Ord α ] [Ord β] (f : α → β) (s : Std.TreeSet α)
  : Std.TreeSet β :=
  TreeSet.ofList (s.toList.map f)


-- def applyPermutate (e : StateConcrete)
--   (σ : Equiv.Perm (Fin 2)) : StateConcrete :=
-- {
--   rmState := mapTreeSet (fun (p1, p2) => (σ p1, p2)) e.rmState,
--   tmState := e.tmState,
--   tmPrepared := mapTreeSet (fun p => σ p) e.tmPrepared,
--   preparedRM := mapTreeSet (fun p => σ p) e.preparedRM,
--   commitMsg := e.commitMsg,
--   abortMsg := e.abortMsg
-- }


-- def showPermuted (xs : List α) (σs : List (Equiv.Perm α)) : List (List α) :=
--   σs.map (fun σ => xs.map σ)

-- def permutationDomain := permsOfList (FinEnum.toList (Fin 2))

-- #eval showPermuted [0, 1, 2, 3, 4] permutationDomain


instance [FinEnum α] [Ord α] : Ord (Std.TreeSet α) where
  compare s1 s2 := compare s1.toArray s2.toArray

instance [FinEnum α] [FinEnum β] [Ord α] [Ord β]
  : Ord (FieldConcreteType α β states State.Label.locked) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance_for_iterated_prod


instance [FinEnum α] [FinEnum β] [Ord α] [Ord β]
  : Ord (FieldConcreteType α β states State.Label.wait_queue_num_wakers) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [FinEnum β] [Ord α] [Ord β]
  : Ord (FieldConcreteType α β states State.Label.wait_queue_wakers) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [FinEnum β] [Ord α] [Ord β]
  : Ord (FieldConcreteType α β states State.Label.head_wait_queue) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [FinEnum β] [Ord α] [Ord β]
  : Ord (FieldConcreteType α β states State.Label.tail_wait_queue) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [FinEnum β] [Ord α] [Ord β]
  : Ord (FieldConcreteType α β states State.Label.has_woken) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [FinEnum β] [Ord α] [Ord β]
  : Ord (FieldConcreteType α β states State.Label.pc) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [FinEnum β] [Ord α] [Ord β]
  : Ord (FieldConcreteType α β states State.Label.stack_pc) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [FinEnum β] [Ord α] [Ord β]
  : Ord (FieldConcreteType α β states State.Label.head_stack_pc) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [FinEnum β] [Ord α] [Ord β]
  : Ord (FieldConcreteType α β states State.Label.tail_stack_pc) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [FinEnum β] [Ord α] [Ord β]
  : Ord (FieldConcreteType α β states State.Label.stack_waker) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [FinEnum β] [Ord α] [Ord β]
  : Ord (FieldConcreteType α β states State.Label.head_stack_waker) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [FinEnum β] [Ord α] [Ord β]
  : Ord (FieldConcreteType α β states State.Label.tail_stack_waker) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [FinEnum α] [FinEnum β] [Ord α] [Ord β]
  : Ord (FieldConcreteType α β states State.Label.waker) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance



instance: Ord StateConcrete where
  compare a b :=
    compare a.locked b.locked |>.then
    (compare a.wait_queue_num_wakers b.wait_queue_num_wakers) |>.then
    (compare a.wait_queue_wakers b.wait_queue_wakers) |>.then
    (compare a.head_wait_queue b.head_wait_queue) |>.then
    (compare a.tail_wait_queue b.tail_wait_queue) |>.then
    (compare a.has_woken b.has_woken) |>.then
    (compare a.pc b.pc) |>.then
    (compare a.stack_pc b.stack_pc) |>.then
    (compare a.head_stack_pc b.head_stack_pc) |>.then
    (compare a.tail_stack_pc b.tail_stack_pc) |>.then
    (compare a.stack_waker b.stack_waker) |>.then
    (compare a.head_stack_waker b.head_stack_waker) |>.then
    (compare a.tail_stack_waker b.tail_stack_waker) |>.then
    (compare a.waker b.waker)


def minOrd? [Ord α] : List α → Option α
  | []      => none
  | x :: xs =>
    let cmpf := (fun m a => if (compare a m).isLE then a else m)
    some <| xs.foldl cmpf x


def view (st : StateConcrete):=
    -- let group := permutationDomain.map (fun σ => applyPermutate st σ)
    -- let lexicographicallySmall := group |> minOrd?
    -- match lexicographicallySmall with
    -- | none => hash st
    -- | .some smallest => hash smallest
    hash st
    -- st

-- def st₀ := (((afterInit initVeilMultiExecM {} default |>.map Prod.snd).map getStateFromExceptT)[0]!).getD default
-- #eval st₀

-- def st₀ := (((afterInit initVeilMultiExecM {} default |>.map Prod.snd).map getStateFromExceptT)[0]!).getD default

-- #eval st₀
-- #eval labelList

instance : (rd : TheoryConcrete) → (st : StateConcrete)
    → Decidable ((fun ρ σ => mutual_exclusion ρ σ) rd st) := by
  intro rd st
  unfold mutual_exclusion
  infer_instance

#check mutual_exclusion


def modelCheckerResult' := (runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (fun ρ σ => mutual_exclusion ρ σ) {one := 1} view).snd
#time #eval modelCheckerResult'

end Mutex
