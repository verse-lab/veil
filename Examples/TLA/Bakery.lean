import Veil

veil module Bakery
type process
type seq_t
enum pc_state = { ncs, e1, e2, e3, e4, w1, w2, cs, exit }
instantiate seq : TotalOrderWithZero seq_t
instantiate thread : TotalOrderWithZero process

immutable individual one_th: process
immutable individual one: seq_t

-- relation num: process → seq_t → Bool
function num : process → seq_t
-- relation flag: process → Bool
function flag : process → Bool

/- Local variables -/
relation unchecked: process → process → Bool
-- relation max: process → seq_t → Bool
function max : process → seq_t
-- relation nxt: process → process → Bool
function nxt : process → process
-- relation pc: process → pc_state → Bool
function pc : process → pc_state

#gen_state

theory ghost relation lt (x y : seq_t) := (seq.le x y ∧ x ≠ y)
theory ghost relation next (x y : seq_t) := (lt x y ∧ ∀ z, lt x z → seq.le y z)

theory ghost relation lt_thread (x y : process) := (thread.le x y ∧ x ≠ y)
theory ghost relation next_thread (x y : process) := (lt_thread x y ∧ ∀ z, lt_thread x z → thread.le y z)


assumption [zero_one_th] next_thread thread.zero one_th
assumption [one_index_th] ∀i, thread.le thread.zero i
assumption [nat_gt_zero] ∀n, seq.le seq.zero n
assumption [zero_one] next seq.zero one


ghost relation prec (a1 b1 : seq_t) (a2 b2 : process) :=
  (lt a1 b1 ∨ (a1 = b1 ∧ lt_thread a2 b2))

 ghost relation num_gt_zero (i : process) := lt seq.zero (num i)

ghost relation pc_ncs_e1_exit (j : process) := pc j = ncs ∨ pc j = e1 ∨ pc j = exit

ghost relation pc_ex (i j : process) :=
  pc j = e2 ∧ (unchecked j i ∨ (seq.le (num i) (max j)))

ghost relation pc_e3 (i j : process) :=
  pc j = e3 ∧ (seq.le (num i) (max j))

ghost relation pc_e4_w1_w2 (i j : process) :=
  (pc j = e4 ∨ pc j = w1 ∨ pc j = w2) ∧
  (prec (num i) (num j) i j) ∧
  (pc j = w1 ∨ pc j = w2 → unchecked j i)

ghost relation before (i j : process) :=
  num_gt_zero i ∧ (pc_ncs_e1_exit j ∨ pc_ex i j ∨ pc_e3 i j ∨ pc_e4_w1_w2 i j)

-- VARIABLES num, flag, pc, unchecked, max, nxt

-- vars == << num, flag, pc, unchecked, max, nxt >>

-- ProcSet == (Procs)



-- p(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
--               \/ w1(self) \/ w2(self) \/ cs(self) \/ exit(self)

-- Next == (\E self \in Procs: p(self))

-- Spec == /\ Init /\ [][Next]_vars
--         /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))


-- Init == (* Global variables *)
--         /\ num = [i \in Procs |-> 0]
--         /\ flag = [i \in Procs |-> FALSE]
--         (* Process p *)
--         /\ unchecked = [self \in Procs |-> {}]
--         /\ max = [self \in Procs |-> 0]
--         /\ nxt = [self \in Procs |-> 1]
--         /\ pc = [self \in ProcSet |-> "ncs"]
after_init {
  num P := seq.zero
  flag P := false
  unchecked P Q := false
  max P := seq.zero
  nxt P := thread.zero
  pc P := ncs
}


-- ncs(self) == /\ pc[self] = "ncs"
--              /\ pc' = [pc EXCEPT ![self] = "e1"]
--              /\ UNCHANGED << num, flag, unchecked, max, nxt >>
action evtNCS (self : process) {
  require pc self = ncs
  pc self := e1
}


-- e1(self) == /\ pc[self] = "e1"
--             /\ \/ /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
--                   /\ pc' = [pc EXCEPT ![self] = "e1"]
--                   /\ UNCHANGED <<unchecked, max>>
--                \/ /\ flag' = [flag EXCEPT ![self] = TRUE]
--                   /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
--                   /\ max' = [max EXCEPT ![self] = 0]
--                   /\ pc' = [pc EXCEPT ![self] = "e2"]
--             /\ UNCHANGED << num, nxt >>
action evtE1_branch1 (self : process) {
  require pc self = e1
  flag self := !(flag self)
  pc self := e1
}



action _evtE1_branch2 (self : process) {
  require pc self = e1
  flag self := true
  -- unchecked self self := false
  unchecked self Q := if Q = self then false else true
  max self := seq.zero
  pc self := e2
}


-- e2(self) == /\ pc[self] = "e2"
--             /\ IF unchecked[self] # {}
--                   THEN /\ \E i \in unchecked[self]:
--                             /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
--                             /\ IF num[i] > max[self]
--                                   THEN /\ max' = [max EXCEPT ![self] = num[i]]
--                                   ELSE /\ TRUE
--                                        /\ max' = max
--                        /\ pc' = [pc EXCEPT ![self] = "e2"]
--                   ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
--                        /\ UNCHANGED << unchecked, max >>
--             /\ UNCHANGED << num, flag, nxt >>
action evtE2 (self : process) {
  require pc self = e2
  if (∃i, unchecked self i) then
    let i :| unchecked self i
    unchecked self i := false
    let num_i := num i
    let max_self := max self
    if lt max_self num_i then
      max self := num_i
    pc self := e2
  else
    pc self := e3
}




-- e3(self) == /\ pc[self] = "e3"
--             /\ \/ /\ \E k \in Nat:
--                        num' = [num EXCEPT ![self] = k]
--                   /\ pc' = [pc EXCEPT ![self] = "e3"]
--                \/ /\ \E i \in {j \in Nat : j > max[self]}:
--                        num' = [num EXCEPT ![self] = i]
--                   /\ pc' = [pc EXCEPT ![self] = "e4"]
--             /\ UNCHANGED << flag, unchecked, max, nxt >>
action evtE3_branch1 (self : process) {
  require pc self = e3
  let k ← pick seq_t
  num self := k
  pc self := e3
}


action evtE3_branch2 (self : process) {
  require pc self = e3
  let max_self := max self
  let j ← pick seq_t
  assume lt max_self j
  num self := j
  pc self := e4
}



-- e4(self) == /\ pc[self] = "e4"
--             /\ \/ /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
--                   /\ pc' = [pc EXCEPT ![self] = "e4"]
--                   /\ UNCHANGED unchecked
--                \/ /\ flag' = [flag EXCEPT ![self] = FALSE]
--                   /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
--                   /\ pc' = [pc EXCEPT ![self] = "w1"]
--             /\ UNCHANGED << num, max, nxt >>
action evtE4_branch1 (self : process) {
  require pc self = e4
  flag self := !flag self
  pc self := e4
}


action evtE4_branch2 (self : process) {
  require pc self = e4
  flag self := false
  unchecked self Q := if Q = self then false else true
  pc self := w1
}


-- w1(self) == /\ pc[self] = "w1"
--             /\ IF unchecked[self] # {}
--                   THEN /\ \E i \in unchecked[self]:
--                             nxt' = [nxt EXCEPT ![self] = i]
--                        /\ ~ flag[nxt'[self]]
--                        /\ pc' = [pc EXCEPT ![self] = "w2"]
--                   ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
--                        /\ nxt' = nxt
--             /\ UNCHANGED << num, flag, unchecked, max >>
action evtW1 (self : process) {
  require pc self = w1
  if (∃i, unchecked self i) then
    let i ← pick process
    assume unchecked self i
    nxt self := i
    require ¬ flag i
    pc self := w2
  else
    pc self := cs
}



-- w2(self) == /\ pc[self] = "w2"
--             /\ \/ num[nxt[self]] = 0
--                \/ <<num[self], self>> \prec <<num[nxt[self]], nxt[self]>>
--             /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
--             /\ pc' = [pc EXCEPT ![self] = "w1"]
--             /\ UNCHANGED << num, flag, max, nxt >>
action evtW2 (self : process) {
  require pc self = w2
  let nxt_self := nxt self
  let num_self := num self
  let num_nxt_self := num nxt_self
  require (num_nxt_self = seq.zero) ∨ (prec num_self num_nxt_self self nxt_self)
  unchecked self nxt_self := false
  pc self := w1
}



-- cs(self) == /\ pc[self] = "cs"
--             /\ TRUE
--             /\ pc' = [pc EXCEPT ![self] = "exit"]
--             /\ UNCHANGED << num, flag, unchecked, max, nxt >>
action evtCS (self : process) {
  require pc self = cs
  pc self := exit
}


-- exit(self) == /\ pc[self] = "exit"
--               /\ \/ /\ \E k \in Nat:
--                          num' = [num EXCEPT ![self] = k]
--                     /\ pc' = [pc EXCEPT ![self] = "exit"]
--                  \/ /\ num' = [num EXCEPT ![self] = 0]
--                     /\ pc' = [pc EXCEPT ![self] = "ncs"]
--               /\ UNCHANGED << flag, unchecked, max, nxt >>
action evtExit_branch1 (self : process) {
  require pc self = exit
  let k ← pick seq_t
  num self := k
  pc self := exit
}

action evtExit_branch2 (self : process) {
  require pc self = exit
  num self := seq.zero
  pc self := ncs
}



invariant [p1_non_zero_num] pc I = e4 ∨ pc I = w1 ∨ pc I = w2 ∨ pc I = cs → ¬(num I = seq.zero)
invariant [p2_flag_e2_e3] pc I = e2 ∨ pc I = e3 → flag I
invariant [p3_nxt_not_self] pc I = w2 → ¬ (nxt I = I)
invariant [p4_unchecked_not_self] pc I = w1 ∨ pc I = w2 → ¬(unchecked I I)
invariant [p5_critical_section] pc I = w1 ∨ pc I = w2 → ∀j, (j ≠ I ∧ ¬unchecked I j) → before I j
invariant [p6_nxt_e2_e3]
  pc I = w2 ∧
  ((pc (nxt I) = e2 ∧ ¬unchecked (nxt I) I) ∨ (pc (nxt I) = e3)) →
    (seq.le (num I) (max (nxt I)))
invariant [p7_cs_precedes_all] pc I = cs → ∀j, (j ≠ I) → before I j

/- Ensures no two processes are in critical section simultaneously. -/
safety [mutual_exclusion] pc I = cs ∧ pc J = cs → I = J

set_option maxHeartbeats 2500000
#gen_spec
/-
Note that:
`process := Fin 2` corresponds to `N = 2`
`seq_t := Fin 3` corresponds to Nat = `MaxNat = 2`

So the corresponding parameters here are:
`2-3`, `3-4`
-/
#model_check
{ process := Fin 2,
  seq_t := Fin 3,
  pc_state := pc_state_IndT }
{ one_th := 1,
  one := 1 }


end Bakery
