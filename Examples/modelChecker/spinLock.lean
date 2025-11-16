import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main
-- ----- MODULE 0_mutex -----

veil module spinLock
----- MODULE spin -----
-- EXTENDS Integers, FiniteSets, Sequences, TLC
-- CONSTANTS NumProcs

-- Procs == 1..NumProcs

-- (*--algorithm spinlock
-- {
-- variables lock = FALSE;

-- procedure acquire_lock()
-- variables current = FALSE;
--           new = TRUE;
-- {
-- compare_exchange:+
--     if (lock = current)
--     {
--         lock := new;
--         return;
--     }
--     else
--     {
--         goto compare_exchange;
--     };
-- };

-- procedure release_lock()
-- {
-- release:
--     lock := FALSE;
--     return;
-- }

-- fair process (P \in Procs)
-- {
-- loop:-
--     while (TRUE)
--     {
--         call acquire_lock();
--     cs:
--         skip;
--     drop_lock:
--         call release_lock();
--     };
-- };

-- }
-- *)
-- \* BEGIN TRANSLATION (chksum(pcal) = "cd6ac6d7" /\ chksum(tla) = "ed17eb2f")
-- VARIABLES lock, pc, stack, current, new
type process
-- vars == << lock, pc, stack, current, new >>
-- ProcSet == (Procs)
enum states = {
  loop,
  compare_exchange,
  cs,
  drop_lock,
  release
}
-- Init == (* Global variables *)
--         /\ lock = FALSE
--         (* Procedure acquire_lock *)
--         /\ current = [ self \in ProcSet |-> FALSE]
--         /\ new = [ self \in ProcSet |-> TRUE]
--         /\ stack = [self \in ProcSet |-> << >>]
--         /\ pc = [self \in ProcSet |-> "loop"]
individual lock : Bool
relation current : process -> Bool
relation new : process -> Bool
relation pc : process -> states → Bool
function stack_pc : process -> List states
function stack_current : process -> List Bool
function stack_new : process -> List Bool

#gen_state
after_init {
  -- Global variables
  lock := false
  -- Procedure acquire_lock
  current P := false
  new P := true
  stack_pc P := []
  stack_current P := []
  stack_new P := []
  pc P S := S == loop
}
-- compare_exchange(self) == /\ pc[self] = "compare_exchange"
--                           /\ IF lock = current[self]
--                                 THEN /\ lock' = new[self]
--                                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                                      /\ current' = [current EXCEPT ![self] = Head(stack[self]).current]
--                                      /\ new' = [new EXCEPT ![self] = Head(stack[self]).new]
--                                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                                 ELSE /\ pc' = [pc EXCEPT ![self] = "compare_exchange"]
--                                      /\ UNCHANGED << lock, stack, current, new >>
action _compare_exchange (self : process) {
  require pc self compare_exchange
  if lock == current self then
    lock := new self
    let head_stk_pc := (stack_pc self).head!
    pc self S := S == head_stk_pc

    let head_stk_current := (stack_current self).head!
    current self := head_stk_current

    let head_stk_new := (stack_new self).head!
    new self := head_stk_new

    stack_pc self := (stack_pc self).tail
    stack_current self := (stack_current self).tail
    stack_new self := (stack_new self).tail
  else
    pc self S := S == compare_exchange
}

-- acquire_lock(self) == compare_exchange(self)

-- release(self) == /\ pc[self] = "release"
--                  /\ lock' = FALSE
--                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
--                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
--                  /\ UNCHANGED << current, new >>
action _release (self : process) {
  require pc self release
  lock := false

  -- assert `(stack_pc self) ≠ []`"
  let head_stk_pc := (stack_pc self).head!
  pc self S := S == head_stk_pc

  stack_pc self := (stack_pc self).tail
  stack_current self := (stack_current self).tail
  stack_new self := (stack_new self).tail
}


-- release_lock(self) == release(self)

-- loop(self) == /\ pc[self] = "loop"
--               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "acquire_lock",
--                                                        pc        |->  "cs",
--                                                        current   |->  current[self],
--                                                        new       |->  new[self] ] >>
--                                                    \o stack[self]]
--               /\ current' = [current EXCEPT ![self] = FALSE]
--               /\ new' = [new EXCEPT ![self] = TRUE]
--               /\ pc' = [pc EXCEPT ![self] = "compare_exchange"]
--               /\ lock' = lock
action _loop (self : process) {
  require pc self loop
  stack_pc self := cs :: (stack_pc self)
  stack_current self := (current self) :: (stack_current self)
  stack_new self := (new self) :: (stack_new self)
  current self := false
  new self := true
  pc self S := S == compare_exchange
}


-- cs(self) == /\ pc[self] = "cs"
--             /\ TRUE
--             /\ pc' = [pc EXCEPT ![self] = "drop_lock"]
--             /\ UNCHANGED << lock, stack, current, new >>
action _cs (self : process) {
  require pc self cs
  pc self S := S == drop_lock
}


-- drop_lock(self) == /\ pc[self] = "drop_lock"
--                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "release_lock",
--                                                             pc        |->  "loop" ] >>
--                                                         \o stack[self]]
--                    /\ pc' = [pc EXCEPT ![self] = "release"]
--                    /\ UNCHANGED << lock, current, new >>
action _drop_lock (self : process) {
  require pc self drop_lock
  stack_pc self := loop :: (stack_pc self)
  let rdm_current ← pick Bool
  let rdm_new ← pick Bool
  stack_current self := rdm_current :: (stack_current self)
  stack_new self := rdm_new :: (stack_new self)
  pc self S := S == release
}

-- P(self) == loop(self) \/ cs(self) \/ drop_lock(self)

-- Next == (\E self \in ProcSet: acquire_lock(self) \/ release_lock(self))
--            \/ (\E self \in Procs: P(self))

-- Spec == /\ Init /\ [][Next]_vars
--         /\ \A self \in Procs : /\ WF_vars((pc[self] # "loop") /\ P(self))
--                                /\ WF_vars(acquire_lock(self))
--                                /\ SF_vars(compare_exchange(self))                               /\ WF_vars(release_lock(self))
invariant [MutualExclusion] P1 ≠ P2 → ¬ (pc P1 cs ∧ pc P2 cs)
-- invariant [termination] ∀ S, pc S Done

-- termination [allDone] pc P Done

#gen_spec
-- \* END TRANSLATION

-- MutualExclusion == \A i, j \in Procs :
--                      (i # j) => ~ /\ pc[i] = "cs"
--                                   /\ pc[j] = "cs"

-- Trying(i) == pc[i] \in { "compare_exchange", "loop_check"}

-- DeadAndLivelockFree == \E i \in Procs :
--                         Trying(i) ~> (\E j \in Procs : pc[j] = "cs")

-- StarvationFree == \A i \in Procs :
--                         Trying(i) ~> (pc[i] = "cs")

-- =============================================================================

#gen_exec
#finitizeTypes (Fin 3), states



def view (st : StateConcrete) := hash st
def detect_prop : TheoryConcrete → StateConcrete → Bool := (fun ρ σ => MutualExclusion ρ σ)
def terminationC : TheoryConcrete → StateConcrete → Bool := (fun ρ σ => true)
def cfg : TheoryConcrete := {}

def modelCheckerResult' :=(runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (detect_prop) (terminationC) cfg view).snd
def statesJson : Lean.Json := Lean.toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM cfg (collectTrace' modelCheckerResult'))
open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />




end spinLock
