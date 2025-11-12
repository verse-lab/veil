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
-- type seq_t
individual locked : Bool
enum states = { pre_check_lock, wait_until, enqueue_waker,
                check_lock, check_has_woken,
                release_lock, wake_one, wake_one_loop,
                wake_up, start, cs, Done }

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

structure Cell (states process : Type) where
  pc : states
  waker : process
deriving DecidableEq, Inhabited, BEq, Hashable, Ord, Repr, Lean.ToJson

function stack : process → List (Cell states process)
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

  -- stack_pc P := []
  -- stack_waker P := []
  stack P := []
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
  -- stack_pc self := cs :: (stack_pc self)
  let random_waker ← pick process
  -- stack_waker self := random_waker :: (stack_waker self)
  stack self := { pc := cs, waker := random_waker } :: (stack self)
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
    -- assert stack self ≠ []
    let head_stack_pc_state := (stack self).head!.pc
    pc self S := S == head_stack_pc_state
    stack self := (stack self).tail
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
    -- assert stack self ≠ []
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
    -- assert stack self ≠ []
    let head_stack_pc_state := (stack self).head!.pc
    pc self S := S == head_stack_pc_state
    let headwaker_stack_waker := (stack self).head!.waker
    waker self W := W == headwaker_stack_waker
    stack self := (stack self).tail
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
    let head_stack_pc_state := (stack self).head!.pc
    pc self S := S == head_stack_pc_state
    -- stack self := (stack self).tail

    let headwaker_stack_waker := (stack self).head!.waker
    waker self W := W == headwaker_stack_waker
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
  require pc self wake_up

  if ∃t, waker self t then
    let waker_self :| waker self waker_self

    /- Condition 1: -/
    if has_woken waker_self == false then
      has_woken waker_self := true
      let head_stack_pc_state := (stack self).head!.pc
      pc self S := S == head_stack_pc_state

      let headwaker_stack_waker := (stack self).head!.waker
      waker self W := W == headwaker_stack_waker

      stack self := (stack self).tail
    else
      pc self S := S == wake_one_loop

  -- else
  --   /- Exception handle -/
  --   let waker_self := none
  --   if has_woken waker_self == false then
  --     has_woken waker_self := true
  --     let head_stack_pc_state := (stack_pc self).head!
  --     pc self S := S == head_stack_pc_state
  --     stack_pc self := (stack_pc self).tail

  --     let headwaker_stack_waker := (stack_waker self).head!
  --     waker self W := W == headwaker_stack_waker
  --     stack_waker self := (stack_waker self).tail
  --   else
  --     pc self S := S == wake_one_loop

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
  -- stack_pc self := Done :: (stack_pc self)
  if ∃t, waker self t then
    let waker_self :| waker self waker_self
    -- stack_waker self := waker_self :: (stack_waker self)
    -- waker self W := false
    waker self W := W == none
    stack self := { pc := Done, waker := waker_self } :: (stack self)
  -- else
  --   let waker_self := none
  --   stack_waker self := waker_self :: (stack_waker self)
  --   waker self W := W == none

  pc self S := S == release_lock
}

termination [allDone] pc S Done
invariant [mutual_exclusion] ∀ I J, I ≠ J → ¬ (pc I cs ∧ pc J cs)


#gen_spec

-- open Lean Meta Elab Command Veil in
-- scoped elab "⌞? " t:term " ⌟" : term => do
--   let lenv ← localEnv.get
--   let some mod := lenv.currentModule | throwError s!"Not in a module"
--   Term.elabTerm (← `(term| $t $(← mod.sortIdents)*)) none

-- -- #time #check_invariants

-- section

-- veil_variables


-- omit χ χ_rep χ_rep_lawful

-- open Veil Extract


-- variable [FinEnum process] [Hashable process] [Ord process]
-- variable [FinEnum states] [Hashable states] [Ord states]
-- -- variable [FinEnum Cell] [Hashable Cell] [Ord Cell]
-- variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
-- variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]

-- variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
-- variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states)))]

-- variable [Ord (process × states)]
-- variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]
-- variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]

-- variable [Ord (process × process)]
-- variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
-- variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]

-- -- variable [Ord (process × List Cell)]
-- -- variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × List Cell))))]
-- -- variable [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × List Cell))))]


-- #print State.Label.toDomain

-- -- example (f : State.Label) : (⌞? State.Label.toDomain ⌟) f = [ℕ]:= by
-- --   unfold State.Label.toDomain

-- -- example (f : State.Label) : ((⌞? State.Label.toCodomain ⌟) f) = ℕ := by
-- --   unfold State.Label.toCodomain
-- --   simp

-- def instFinEnumForComponents (f : State.Label)
--   : (IteratedProd <| List.map FinEnum <| (⌞? State.Label.toDomain ⌟) f) := by
--   cases f <;>
--     infer_instance_for_iterated_prod

-- instance instFinEnumForCodomain [FinEnum (List (Cell states process))][FinEnum (List process)] (f : State.Label)
--   : (FinEnum ((⌞? State.Label.toCodomain ⌟) f)) := by
--   cases f <;>
--     dsimp only [IteratedProd, List.foldr, State.Label.toCodomain, State.Label.toCtorIdx] <;>
--     infer_instance

-- instance instFinEnumForComponents' (f : State.Label)
--   : FinEnum (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
--   cases f <;>
--     dsimp only [IteratedProd', List.foldr, State.Label.toDomain] <;>
--     infer_instance

-- instance instDecidableEqForComponents' (f : State.Label)
--   : DecidableEq (IteratedProd <| (⌞? State.Label.toDomain ⌟) f) := by
--   cases f <;>
--     dsimp only [IteratedProd, List.foldr, State.Label.toDomain] <;>
--     infer_instance

-- instance instDecidableEqForComponents'' (f : State.Label)
--   : DecidableEq (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
--   cases f <;>
--     dsimp only [IteratedProd', State.Label.toDomain] <;>
--     infer_instance

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


-- instance [Ord α] [Ord β] : Ord (α × β) where
--   compare x y := match x, y with
--     | (a, b), (a', b') => compare a a' |>.then (compare b b')

-- instance instOrderForComponents' (f : State.Label)
--   : Ord (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
--   cases f <;>
--     dsimp only [IteratedProd', State.Label.toDomain] <;>
--     infer_instance


-- instance (f : State.Label) : Ord (IteratedProd' (State.Label.toDomain process states f)) := by
--   cases f <;>
--     dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain] <;>
--     infer_instance


-- abbrev FieldConcreteType (f : State.Label) : Type :=
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
--   | State.Label.stack =>
--     -- Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.stack_pc)
--     -- Std.TreeSet (process × List process)
--     TotalTreeMap (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.stack)
--     ((⌞? State.Label.toCodomain ⌟) State.Label.stack)
--   /- `stack_stack` is a `function` field -/
--   /- `stack_` is a `relation` -/
--   | State.Label.waker =>
--     Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.waker)


-- instance instReprForComponents [Repr process] [Repr states] [Repr (TotalTreeMap process (List (Cell states process)) compare)] (f : State.Label)
--   : Repr ((⌞? FieldConcreteType ⌟) f) := by
--   cases f <;>
--     dsimp only [IteratedProd', FieldConcreteType, State.Label.toDomain, State.Label.toCodomain] <;>
--     infer_instance


-- instance : Inhabited ((⌞? State ⌟) (⌞? FieldConcreteType ⌟)) := by
--   constructor ; constructor <;>
--   dsimp only [FieldConcreteType, State.Label.toCodomain] <;>
--   -- exact default
--   -- infer_instance_for_iterated_prod
--   try exact default
--   -- set_option trace.Meta.synthInstance.answer true in
--   -- apply instInhabitedTotalTreeMapOfFinEnumOfLawfulEqCmpOfTransCmpOfDecidableEq.default



-- open TotalMapLike
-- #check instTotalMapLikeAsFieldRep
-- instance rep (f : State.Label) : FieldRepresentation
--   ((⌞? State.Label.toDomain ⌟) f)
--   ((⌞? State.Label.toCodomain ⌟) f)
--   ((⌞? FieldConcreteType ⌟) f) :=
--   -- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
--   match f with
--   | State.Label.locked => by
--       dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
--       infer_instance
--   | State.Label.wait_queue_wakers =>by
--       dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
--       infer_instance
--   | State.Label.has_woken =>
--     instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.has_woken)
--   | State.Label.pc =>
--     instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.pc)
--   | State.Label.stack =>
--     instTotalMapLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.stack)
--   | State.Label.waker =>
--     instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.waker)

-- #check instTotalMapLikeAsFieldRep

-- instance lawful (f : State.Label): LawfulFieldRepresentation
--   ((⌞? State.Label.toDomain ⌟) f)
--   ((⌞? State.Label.toCodomain ⌟) f)
--   ((⌞? FieldConcreteType ⌟) f)
--   ((⌞? rep ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
--   match f with
--   | State.Label.locked => by
--       dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
--       infer_instance
--   | State.Label.wait_queue_wakers => by
--       dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
--       infer_instance
--   | State.Label.has_woken =>
--     instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.has_woken)
--   | State.Label.pc =>
--     instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.pc)
--   | State.Label.stack =>by
--       dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
--       infer_instance
--   | State.Label.waker =>
--     instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.waker)
-- end

-- attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet]
--   instFinEnumForComponents in
-- -- attribute [local dsimpFieldRepresentationGet] FourNodes.equiv_IteratedProd in
-- #specialize_nextact with FieldConcreteType
--   injection_begin
--     -- [FinEnum process] [Hashable process] [Ord process]
--     -- [FinEnum states] [Hashable states] [Ord states]
--     -- [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
--     -- [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
--     -- [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
--     -- [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states)))]

--     -- [Ord (process × states)]
--     -- [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]
--     -- [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]

--     -- [Ord (process × process)]
--     -- [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
--     -- [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
--     [FinEnum process] [Hashable process] [Ord process]
--     [FinEnum states] [Hashable states] [Ord states]
--     [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
--     [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
--     [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
--     [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states)))]

--     [Ord (process × states)]
--     [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]
--     [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]

--     [Ord (process × process)]
--     [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
--     [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
--   injection_end => NextAct'



-- #gen_executable_list! log_entry_being Std.Format
--   targeting NextAct'
--   injection_begin
--     [FinEnum process] [Hashable process] [Ord process]
--     [FinEnum states] [Hashable states] [Ord states]
--     [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
--     [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
--     [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
--     [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states)))]

--     [Ord (process × states)]
--     [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]
--     [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × states))))]

--     [Ord (process × process)]
--     [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
--     [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × process))))]
--   injection_end

#gen_spec


deriving_FinOrdToJson_Domain

specify_FieldConcreteType

deriving_BEq_FieldConcreteType

deriving_Hashable_FieldConcreteType

deriving_rep_FieldRepresentation

deriving_lawful_FieldRepresentation


set_option pp.explicit true in
set_option pp.instances true in
#print instLawfulFieldRepForFieldRepresentation

/- I'm confused about what's the `minimal instance` set needed to derive this instance. -/
-- instance instLawfulFieldRepForFieldRepresentation [FinEnum process] [FinEnum states] [Ord process] [Ord states]
--     [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
--     [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
--     [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
--     [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
--     -- [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (Bool))))]
--     -- [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (Bool))))]
--     -- [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (List process))))]
--     -- [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (List process))))]
--     [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process))))]
--     [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process))))]
--     [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × (states)))))]
--     [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × (states)))))]
--     -- [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × (List (Cell states process))))))]
--     -- [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × (List (Cell states process))))))]
--     [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord (process × (process)))))]
--     [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord (process × (process)))))]
--     (f : State.Label) :
--     Veil.LawfulFieldRepresentation ((State.Label.toDomain process states) f) ((State.Label.toCodomain process states) f)
--       ((FieldConcreteType process states) f) ((instRepForFieldRepresentation process states) f) :=
--   by
--   cases f <;>
--     first
--     |
--       (dsimp only [FieldConcreteType,  State.Label.toCodomain,State.Label.toDomain, instRepForFieldRepresentation,
--           Veil.IteratedProd', id];
--         infer_instance)
--     | (exact Veil.instFinsetLikeLawfulFieldRep Veil.IteratedProd'.equiv ((instFinEnumForToDomain process states) _))

deriving_Inhabited_State


theorem Mutex.instLawfulFieldRepForFieldRepresentation : ∀ {process states : Type} [inst : FinEnum process]
  [inst_1 : FinEnum states] [inst_2 : Ord process] [inst_3 : Ord states]
  [inst_4 : @Std.LawfulEqCmp process (@compare process (@inferInstanceAs (Ord process) inst_2))]
  [inst_5 : @Std.LawfulEqCmp states (@compare states (@inferInstanceAs (Ord states) inst_3))]
  [inst_6 : @Std.TransCmp process (@compare process (@inferInstanceAs (Ord process) inst_2))]
  [inst_7 : @Std.TransCmp states (@compare states (@inferInstanceAs (Ord states) inst_3))] (f : State.Label),
  Veil.LawfulFieldRepresentation (State.Label.toDomain process states f) (State.Label.toCodomain process states f)
    (@FieldConcreteType process states inst_2 inst_3 f)
    (@instRepForFieldRepresentation process states inst inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 f) :=
fun {process states} [inst : FinEnum process] [inst_1 : FinEnum states] [inst_2 : Ord process] [inst_3 : Ord states]
    [inst_4 : @Std.LawfulEqCmp process (@compare process (@inferInstanceAs (Ord process) inst_2))]
    [inst_5 : @Std.LawfulEqCmp states (@compare states (@inferInstanceAs (Ord states) inst_3))]
    [inst_6 : @Std.TransCmp process (@compare process (@inferInstanceAs (Ord process) inst_2))]
    [inst_7 : @Std.TransCmp states (@compare states (@inferInstanceAs (Ord states) inst_3))] f =>
  @State.Label.casesOn
    (fun t =>
      @Eq State.Label f t →
        Veil.LawfulFieldRepresentation (State.Label.toDomain process states f) (State.Label.toCodomain process states f)
          (@FieldConcreteType process states inst_2 inst_3 f)
          (@instRepForFieldRepresentation process states inst inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 f))
    f
    (fun h =>
      @Eq.ndrec State.Label State.Label.locked
        (fun f =>
          Veil.LawfulFieldRepresentation (State.Label.toDomain process states f)
            (State.Label.toCodomain process states f) (@FieldConcreteType process states inst_2 inst_3 f)
            (@instRepForFieldRepresentation process states inst inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 f))
        (@id
          (Veil.LawfulFieldRepresentation (State.Label.toDomain process states State.Label.locked)
            (State.Label.toCodomain process states State.Label.locked)
            (@FieldConcreteType process states inst_2 inst_3 State.Label.locked)
            (@instRepForFieldRepresentation process states inst inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7
              State.Label.locked))
          (@inferInstance
            (Veil.LawfulFieldRepresentation (@List.nil Type) Bool Bool
              (@inferInstance (Veil.FieldRepresentation (@List.nil Type) Bool Bool)
                (Veil.instFieldRepresentationNil Bool)))
            (Veil.instLawfulFieldRepresentationNilInferInstanceFieldRepresentation Bool)))
        f (@Eq.symm State.Label f State.Label.locked h))
    (fun h =>
      @Eq.ndrec State.Label State.Label.wait_queue_wakers
        (fun f =>
          Veil.LawfulFieldRepresentation (State.Label.toDomain process states f)
            (State.Label.toCodomain process states f) (@FieldConcreteType process states inst_2 inst_3 f)
            (@instRepForFieldRepresentation process states inst inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 f))
        (@id
          (Veil.LawfulFieldRepresentation (State.Label.toDomain process states State.Label.wait_queue_wakers)
            (State.Label.toCodomain process states State.Label.wait_queue_wakers)
            (@FieldConcreteType process states inst_2 inst_3 State.Label.wait_queue_wakers)
            (@instRepForFieldRepresentation process states inst inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7
              State.Label.wait_queue_wakers))
          (@inferInstance
            (Veil.LawfulFieldRepresentation (@List.nil Type) (List process) (List process)
              (@inferInstance (Veil.FieldRepresentation (@List.nil Type) (List process) (List process))
                (Veil.instFieldRepresentationNil (List process))))
            (Veil.instLawfulFieldRepresentationNilInferInstanceFieldRepresentation (List process))))
        f (@Eq.symm State.Label f State.Label.wait_queue_wakers h))
    (fun h =>
      @Eq.ndrec State.Label State.Label.has_woken
        (fun f =>
          Veil.LawfulFieldRepresentation (State.Label.toDomain process states f)
            (State.Label.toCodomain process states f) (@FieldConcreteType process states inst_2 inst_3 f)
            (@instRepForFieldRepresentation process states inst inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 f))
        (@id
          (Veil.LawfulFieldRepresentation (State.Label.toDomain process states State.Label.has_woken)
            (State.Label.toCodomain process states State.Label.has_woken)
            (@FieldConcreteType process states inst_2 inst_3 State.Label.has_woken)
            (@instRepForFieldRepresentation process states inst inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7
              State.Label.has_woken))
          (@inferInstance
            (Veil.LawfulFieldRepresentation (@List.cons Type process (@List.nil Type)) Bool
              (Std.TreeSet process
                (@compare process (@instOrdForToDomain' process states inst_2 inst_3 State.Label.has_woken)))
              (@Veil.instFinsetLikeAsFieldRep process
                (Std.TreeSet process
                  (@compare process (@instOrdForToDomain' process states inst_2 inst_3 State.Label.has_woken)))
                (@List.cons Type process (@List.nil Type))
                (@Std.TreeSet.instMembership process
                  (@compare process (@instOrdForToDomain' process states inst_2 inst_3 State.Label.has_woken)))
                (@Veil.instFinsetLikeTreeSet process
                  (@compare process (@instOrdForToDomain' process states inst_2 inst_3 State.Label.has_woken)))
                (@Std.TreeSet.instDecidableMem process
                  (@compare process (@instOrdForToDomain' process states inst_2 inst_3 State.Label.has_woken)))
                (@Veil.IteratedProd'.equiv (@List.cons Type process (@List.nil Type)))
                (@instFinEnumForToDomain process states inst inst_1 State.Label.has_woken)))
            (@Veil.instFinsetLikeLawfulFieldRep process
              (Std.TreeSet process
                (@compare process (@instOrdForToDomain' process states inst_2 inst_3 State.Label.has_woken)))
              (@List.cons Type process (@List.nil Type)) (fun a b => @FinEnum.decEq process inst a b)
              (@Std.TreeSet.instMembership process
                (@compare process (@instOrdForToDomain' process states inst_2 inst_3 State.Label.has_woken)))
              (@Veil.instFinsetLikeTreeSet process
                (@compare process (@instOrdForToDomain' process states inst_2 inst_3 State.Label.has_woken)))
              (@Veil.instLawfulFinsetLikeTreeSetOfLawfulEqCmpOfTransCmp process
                (@compare process (@instOrdForToDomain' process states inst_2 inst_3 State.Label.has_woken)) inst_4
                inst_6 fun a b => @FinEnum.decEq process inst a b)
              (@Std.TreeSet.instDecidableMem process
                (@compare process (@instOrdForToDomain' process states inst_2 inst_3 State.Label.has_woken)))
              (@Veil.IteratedProd'.equiv (@List.cons Type process (@List.nil Type)))
              (@instFinEnumForToDomain process states inst inst_1 State.Label.has_woken))))
        f (@Eq.symm State.Label f State.Label.has_woken h))
    (fun h =>
      @Eq.ndrec State.Label State.Label.pc
        (fun f =>
          Veil.LawfulFieldRepresentation (State.Label.toDomain process states f)
            (State.Label.toCodomain process states f) (@FieldConcreteType process states inst_2 inst_3 f)
            (@instRepForFieldRepresentation process states inst inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 f))
        (@id
          (Veil.LawfulFieldRepresentation (State.Label.toDomain process states State.Label.pc)
            (State.Label.toCodomain process states State.Label.pc)
            (@FieldConcreteType process states inst_2 inst_3 State.Label.pc)
            (@instRepForFieldRepresentation process states inst inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7
              State.Label.pc))
          (@inferInstance
            (Veil.LawfulFieldRepresentation (@List.cons Type process (@List.cons Type states (@List.nil Type))) Bool
              (Std.TreeSet (Prod process states)
                (@compare (Prod process states) (@instOrdForToDomain' process states inst_2 inst_3 State.Label.pc)))
              (@Veil.instFinsetLikeAsFieldRep (Prod process states)
                (Std.TreeSet (Prod process states)
                  (@compare (Prod process states) (@instOrdForToDomain' process states inst_2 inst_3 State.Label.pc)))
                (@List.cons Type process (@List.cons Type states (@List.nil Type)))
                (@Std.TreeSet.instMembership (Prod process states)
                  (@compare (Prod process states) (@instOrdForToDomain' process states inst_2 inst_3 State.Label.pc)))
                (@Veil.instFinsetLikeTreeSet (Prod process states)
                  (@compare (Prod process states) (@instOrdForToDomain' process states inst_2 inst_3 State.Label.pc)))
                (@Std.TreeSet.instDecidableMem (Prod process states)
                  (@compare (Prod process states) (@instOrdForToDomain' process states inst_2 inst_3 State.Label.pc)))
                (@Veil.IteratedProd'.equiv (@List.cons Type process (@List.cons Type states (@List.nil Type))))
                (@instFinEnumForToDomain process states inst inst_1 State.Label.pc)))
            (@Veil.instFinsetLikeLawfulFieldRep (Prod process states)
              (Std.TreeSet (Prod process states)
                (@compare (Prod process states) (@instOrdForToDomain' process states inst_2 inst_3 State.Label.pc)))
              (@List.cons Type process (@List.cons Type states (@List.nil Type)))
              (fun a b =>
                @instDecidableEqProd process states (fun a b => @FinEnum.decEq process inst a b)
                  (fun a b => @FinEnum.decEq states inst_1 a b) a b)
              (@Std.TreeSet.instMembership (Prod process states)
                (@compare (Prod process states) (@instOrdForToDomain' process states inst_2 inst_3 State.Label.pc)))
              (@Veil.instFinsetLikeTreeSet (Prod process states)
                (@compare (Prod process states) (@instOrdForToDomain' process states inst_2 inst_3 State.Label.pc)))
              (@Veil.instLawfulFinsetLikeTreeSetOfLawfulEqCmpOfTransCmp (Prod process states)
                (@compare (Prod process states) (@instOrdForToDomain' process states inst_2 inst_3 State.Label.pc))
                (@Std.instLawfulEqOrdProd process states inst_2 inst_3 inst_4 inst_5)
                (@Std.instTransOrdProd process states inst_2 inst_3 inst_6 inst_7) fun a b =>
                @instDecidableEqProd process states (fun a b => @FinEnum.decEq process inst a b)
                  (fun a b => @FinEnum.decEq states inst_1 a b) a b)
              (@Std.TreeSet.instDecidableMem (Prod process states)
                (@compare (Prod process states) (@instOrdForToDomain' process states inst_2 inst_3 State.Label.pc)))
              (@Veil.IteratedProd'.equiv (@List.cons Type process (@List.cons Type states (@List.nil Type))))
              (@instFinEnumForToDomain process states inst inst_1 State.Label.pc))))
        f (@Eq.symm State.Label f State.Label.pc h))
    (fun h =>
      @Eq.ndrec State.Label State.Label.stack
        (fun f =>
          Veil.LawfulFieldRepresentation (State.Label.toDomain process states f)
            (State.Label.toCodomain process states f) (@FieldConcreteType process states inst_2 inst_3 f)
            (@instRepForFieldRepresentation process states inst inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 f))
        (@id
          (Veil.LawfulFieldRepresentation (State.Label.toDomain process states State.Label.stack)
            (State.Label.toCodomain process states State.Label.stack)
            (@FieldConcreteType process states inst_2 inst_3 State.Label.stack)
            (@instRepForFieldRepresentation process states inst inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7
              State.Label.stack))
          (@inferInstance
            (Veil.LawfulFieldRepresentation (@List.cons Type process (@List.nil Type)) (List (Cell states process))
              (Veil.TotalTreeMap process (List (Cell states process))
                (@compare process (@instOrdForToDomain' process states inst_2 inst_3 State.Label.stack)))
              (@Veil.instTotalMapLikeAsFieldRep process
                (Veil.TotalTreeMap process (List (Cell states process))
                  (@compare process (@instOrdForToDomain' process states inst_2 inst_3 State.Label.stack)))
                (@List.cons Type process (@List.nil Type)) (List (Cell states process))
                (@Veil.instTotalMapLikeTotalTreeMapOfTransCmp (List (Cell states process)) process
                  (@compare process (@instOrdForToDomain' process states inst_2 inst_3 State.Label.stack)) inst_6)
                (@Veil.IteratedProd'.equiv (@List.cons Type process (@List.nil Type)))
                (@instFinEnumForToDomain process states inst inst_1 State.Label.stack)))
            (@Veil.instTotalMapLikeLawfulFieldRep process
              (Veil.TotalTreeMap process (List (Cell states process))
                (@compare process (@instOrdForToDomain' process states inst_2 inst_3 State.Label.stack)))
              (@List.cons Type process (@List.nil Type)) (List (Cell states process))
              (fun a b => @FinEnum.decEq process inst a b)
              (@Veil.instTotalMapLikeTotalTreeMapOfTransCmp (List (Cell states process)) process
                (@compare process (@instOrdForToDomain' process states inst_2 inst_3 State.Label.stack)) inst_6)
              (@Veil.instLawfulTotalMapLikeTotalTreeMapOfLawfulEqCmp (List (Cell states process)) process
                (@compare process (@instOrdForToDomain' process states inst_2 inst_3 State.Label.stack)) inst_4 inst_6
                fun a b => @FinEnum.decEq process inst a b)
              (@Veil.IteratedProd'.equiv (@List.cons Type process (@List.nil Type)))
              (@instFinEnumForToDomain process states inst inst_1 State.Label.stack))))
        f (@Eq.symm State.Label f State.Label.stack h))
    (fun h =>
      @Eq.ndrec State.Label State.Label.waker
        (fun f =>
          Veil.LawfulFieldRepresentation (State.Label.toDomain process states f)
            (State.Label.toCodomain process states f) (@FieldConcreteType process states inst_2 inst_3 f)
            (@instRepForFieldRepresentation process states inst inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 f))
        (@id
          (Veil.LawfulFieldRepresentation (State.Label.toDomain process states State.Label.waker)
            (State.Label.toCodomain process states State.Label.waker)
            (@FieldConcreteType process states inst_2 inst_3 State.Label.waker)
            (@instRepForFieldRepresentation process states inst inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7
              State.Label.waker))
          (@inferInstance
            (Veil.LawfulFieldRepresentation (@List.cons Type process (@List.cons Type process (@List.nil Type))) Bool
              (Std.TreeSet (Prod process process)
                (@compare (Prod process process) (@instOrdForToDomain' process states inst_2 inst_3 State.Label.waker)))
              (@Veil.instFinsetLikeAsFieldRep (Prod process process)
                (Std.TreeSet (Prod process process)
                  (@compare (Prod process process)
                    (@instOrdForToDomain' process states inst_2 inst_3 State.Label.waker)))
                (@List.cons Type process (@List.cons Type process (@List.nil Type)))
                (@Std.TreeSet.instMembership (Prod process process)
                  (@compare (Prod process process)
                    (@instOrdForToDomain' process states inst_2 inst_3 State.Label.waker)))
                (@Veil.instFinsetLikeTreeSet (Prod process process)
                  (@compare (Prod process process)
                    (@instOrdForToDomain' process states inst_2 inst_3 State.Label.waker)))
                (@Std.TreeSet.instDecidableMem (Prod process process)
                  (@compare (Prod process process)
                    (@instOrdForToDomain' process states inst_2 inst_3 State.Label.waker)))
                (@Veil.IteratedProd'.equiv (@List.cons Type process (@List.cons Type process (@List.nil Type))))
                (@instFinEnumForToDomain process states inst inst_1 State.Label.waker)))
            (@Veil.instFinsetLikeLawfulFieldRep (Prod process process)
              (Std.TreeSet (Prod process process)
                (@compare (Prod process process) (@instOrdForToDomain' process states inst_2 inst_3 State.Label.waker)))
              (@List.cons Type process (@List.cons Type process (@List.nil Type)))
              (fun a b =>
                @instDecidableEqProd process process (fun a b => @FinEnum.decEq process inst a b)
                  (fun a b => @FinEnum.decEq process inst a b) a b)
              (@Std.TreeSet.instMembership (Prod process process)
                (@compare (Prod process process) (@instOrdForToDomain' process states inst_2 inst_3 State.Label.waker)))
              (@Veil.instFinsetLikeTreeSet (Prod process process)
                (@compare (Prod process process) (@instOrdForToDomain' process states inst_2 inst_3 State.Label.waker)))
              (@Veil.instLawfulFinsetLikeTreeSetOfLawfulEqCmpOfTransCmp (Prod process process)
                (@compare (Prod process process) (@instOrdForToDomain' process states inst_2 inst_3 State.Label.waker))
                (@Std.instLawfulEqOrdProd process process inst_2 inst_2 inst_4 inst_4)
                (@Std.instTransOrdProd process process inst_2 inst_2 inst_6 inst_6) fun a b =>
                @instDecidableEqProd process process (fun a b => @FinEnum.decEq process inst a b)
                  (fun a b => @FinEnum.decEq process inst a b) a b)
              (@Std.TreeSet.instDecidableMem (Prod process process)
                (@compare (Prod process process) (@instOrdForToDomain' process states inst_2 inst_3 State.Label.waker)))
              (@Veil.IteratedProd'.equiv (@List.cons Type process (@List.cons Type process (@List.nil Type))))
              (@instFinEnumForToDomain process states inst inst_1 State.Label.waker))))
        f (@Eq.symm State.Label f State.Label.waker h))
    (@Eq.refl State.Label f)

gen_NextAct
-- attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet] instFinEnumForToDomain in
-- #specialize_nextact with FieldConcreteType
--   injection_begin[FinEnum
--       process][FinEnum
--       states][Hashable
--       process][Hashable
--       states][Ord
--       process][Ord
--       states][Std.LawfulEqCmp
--       (Ord.compare (self :=
--         inferInstanceAs
--           (Ord
--             process)))][Std.LawfulEqCmp
--       (Ord.compare (self :=
--         inferInstanceAs
--           (Ord
--             states)))][Std.TransCmp
--       (Ord.compare (self :=
--         inferInstanceAs
--           (Ord
--             process)))][Std.TransCmp
--       (Ord.compare (self :=
--         inferInstanceAs
--           (Ord
--             states)))][Std.LawfulEqCmp
--       (Ord.compare (self :=
--         inferInstanceAs
--           (Ord
--             (Bool))))][Std.TransCmp
--       (Ord.compare (self :=
--         inferInstanceAs
--           (Ord
--             (Bool))))][Std.LawfulEqCmp
--       (Ord.compare (self :=
--         inferInstanceAs
--           (Ord
--             (List
--               process))))][Std.TransCmp
--       (Ord.compare (self :=
--         inferInstanceAs
--           (Ord
--             (List
--               process))))][Std.LawfulEqCmp
--       (Ord.compare (self :=
--         inferInstanceAs
--           (Ord
--             (process))))][Std.TransCmp
--       (Ord.compare (self :=
--         inferInstanceAs
--           (Ord
--             (process))))][Std.LawfulEqCmp
--       (Ord.compare (self :=
--         inferInstanceAs
--           (Ord
--             (process ×
--               (states)))))][Std.TransCmp
--       (Ord.compare (self :=
--         inferInstanceAs
--           (Ord
--             (process ×
--               (states)))))][Std.LawfulEqCmp
--       (Ord.compare (self :=
--         inferInstanceAs
--           (Ord
--             (process ×
--               (process)))))][Std.TransCmp
--       (Ord.compare (self := inferInstanceAs (Ord (process × (process)))))]
--       injection_end=>NextAct'


gen_executable_NextAct


-- deriving_enum_instance_for states
-- deriving_ord_hashable_for_enum states
-- deriving_propCmp_for_enum states
deriving_Enum_Insts


-- instance {process states : Type}
-- [states_ord: Ord states] [process_ord: Ord process]
-- : Std.OrientedCmp (Ord.compare (self := inferInstanceAs (Ord (Cell states process)))) := by
--   apply Std.OrientedCmp.mk
--   unfold compare inferInstanceAs
--   intro a b; cases a <;>
--     cases b <;> rfl

-- instance [FinEnum states] : Std.OrientedCmp (Ord.compare (self := inferInstanceAs (Ord states))) := by
--   apply Std.OrientedCmp.mk
--   unfold compare inferInstanceAs instOrdstates
--   intro a b; cases a <;>
--     cases b <;> rfl

-- instance : Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord states))) := by
--   apply Std.TransCmp.mk
--   unfold compare inferInstanceAs instOrdstates
--   decide

-- instance : Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states))) := by
--   apply Std.LawfulEqCmp.mk
--   unfold compare inferInstanceAs
--   intro a b; cases a <;>
--     cases b <;> simp <;> decide



-- instance (α β : Type)
-- [a_ord: Ord α]
-- [b_ord: Ord β]
-- [cell_ord : Ord (Cell α β)]
-- [a_oriented: Std.OrientedCmp (Ord.compare (self := a_ord))]
-- [b_oriented: Std.OrientedCmp (Ord.compare (self := b_ord))]
--  : Std.OrientedCmp (Ord.compare (self := inferInstanceAs (Ord (Cell α β)))) := by
--   apply Std.OrientedCmp.mk
--   unfold compare inferInstanceAs
--   intro a b
--   cases a <;>
--     cases b <;>
--     unfold ordCell

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


open Lean

def statesJson : Json :=
  toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM {none := 0} (collectTrace' modelCheckerResult'))

#check statesJson

#eval statesJson
open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />

end Mutex
