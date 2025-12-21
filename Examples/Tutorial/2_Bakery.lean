import Veil

veil module Bakery
type process
type seq_t
enum pc_state = { ncs, e1, e2, e3, e4, w1, w2, cs, exit }
instantiate seq : TotalOrderWithZero seq_t
instantiate thread : TotalOrderWithZero process

immutable individual one_th: process
immutable individual one: seq_t

-- @[actSimp, invSimp]
-- abbrev lt (x y : seq_t) : Prop := (seq.le x y ∧ x ≠ y)

-- @[actSimp, invSimp]
-- abbrev lt_thread (x y : process) : Prop := (thread.le x y ∧ x ≠ y)

-- @[actSimp, invSimp]
-- abbrev next (x y : seq_t) : Prop := (lt seq_t x y ∧ ∀ z, lt seq_t x z → seq.le y z)

-- @[actSimp, invSimp]
-- abbrev next_thread (x y : process) : Prop := (lt_thread process x y ∧ ∀ z, lt_thread process x z → thread.le y z)

/- Global variables -/
relation num: process → seq_t → Bool
relation flag: process → Bool

/- Local variables -/
relation unchecked: process → process → Bool
relation max: process → seq_t → Bool
relation nxt: process → process → Bool
relation pc: process → pc_state → Bool

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

 ghost relation num_gt_zero (i : process) := (∃n, num i n ∧ lt seq.zero n)
-- (∀n, num i n ∧ n ≠ seq.zero)
-- (∃n, num i n ∧ lt seq_t seq.zero n)

ghost relation pc_ncs_e1_exit (j : process) := pc j ncs ∨ pc j e1 ∨ pc j exit

ghost relation pc_ex (i j : process) :=
  pc j e2 ∧ (unchecked j i ∨ (∃mj ni, (max j mj) ∧ (num i ni) ∧ seq.le ni mj))

ghost relation pc_e3 (i j : process) :=
  pc j e3 ∧ (∃mj ni, (max j mj) ∧ (num i ni)∧ seq.le ni mj)

ghost relation pc_e4_w1_w2 (i j : process) :=
  (pc j e4 ∨ pc j w1 ∨ pc j w2) ∧
  (∃ni nj, num i ni ∧ num j nj ∧ prec ni nj i j) ∧
  (pc j w1 ∨ pc j w2 → unchecked j i)

ghost relation before (i j : process) :=
  num_gt_zero i ∧ (pc_ncs_e1_exit j ∨ pc_ex i j ∨ pc_e3 i j ∨ pc_e4_w1_w2 i j)

-- Init == (* Global variables *)
--         /\ num = [i \in Procs |-> 0]
--         /\ flag = [i \in Procs |-> FALSE]
--         (* Process p *)
--         /\ unchecked = [self \in Procs |-> {}]
--         /\ max = [self \in Procs |-> 0]
--         /\ nxt = [self \in Procs |-> 1]
--         /\ pc = [self \in ProcSet |-> "ncs"]
after_init {
  num P N := N == seq.zero
  flag P := false
  unchecked P Q := false
  max P N := N == seq.zero
  nxt P N := N == thread.zero
  pc P S := S == ncs
}


-- ncs(self) == /\ pc[self] = "ncs"
--              /\ pc' = [pc EXCEPT ![self] = "e1"]
--              /\ UNCHANGED << num, flag, unchecked, max, nxt >>
action evtNCS (self : process) {
  require pc self ncs
  pc self S := S == e1
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
  require pc self e1
  flag self := !(flag self)
  pc self S := S == e1
}


action _evtE1_branch2 (self : process) {
  require pc self e1
  flag self := true
  -- unchecked self self := false
  unchecked self Q := if Q = self then false else true
  max self N := N == seq.zero
  pc self S := S == e2
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
  require pc self e2
  if (∃i, unchecked self i) then
    let i :| unchecked self i
    unchecked self i := false
    let num_i :| num i num_i
    let max_self :| max self max_self
    if lt max_self num_i then
      max self N := N == num_i
    pc self S := S == e2
  else
    pc self S := S == e3
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
  require pc self e3
  let k ← pick seq_t
  num self N := decide $ N = k
  pc self S := decide $ S = e3
}



action evtE3_branch2 (self : process) {
  require pc self e3
  let max_self :| max self max_self
  let i :| lt max_self i
  num self N := N == i
  pc self S := S == e4
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
  require pc self e4
  flag self := !flag self
  pc self S := decide $ S = e4
}


action evtE4_branch2 (self : process) {
  require pc self e4
  flag self := false
  unchecked self Q := if Q = self then false else true
  pc self S := decide $ S = w1  -- w1 == p5
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
  require pc self w1
  if (∃i, unchecked self i) then
    let i :| unchecked self i
    nxt self N := decide $ N = i
    require ¬ flag i
    pc self S := decide $ S = w2 -- w2 == p6
  else
    pc self S := decide $ S = cs
}


-- w2(self) == /\ pc[self] = "w2"
--             /\ \/ num[nxt[self]] = 0
--                \/ <<num[self], self>> \prec <<num[nxt[self]], nxt[self]>>
--             /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
--             /\ pc' = [pc EXCEPT ![self] = "w1"]
--             /\ UNCHANGED << num, flag, max, nxt >>
action evtW2 (self : process) {
  require pc self w2
  let nxt_self :| nxt self nxt_self
  let num_self :| num self num_self
  let num_nxt_self :| num nxt_self num_nxt_self
  require (num_nxt_self = seq.zero) ∨ (prec num_self num_nxt_self self nxt_self)
  unchecked self nxt_self := false
  pc self S := decide $ S = w1
}


-- cs(self) == /\ pc[self] = "cs"
--             /\ TRUE
--             /\ pc' = [pc EXCEPT ![self] = "exit"]
--             /\ UNCHANGED << num, flag, unchecked, max, nxt >>
action evtCS (self : process) {
  require pc self cs
  pc self S := decide $ S = exit
}


-- exit(self) == /\ pc[self] = "exit"
--               /\ \/ /\ \E k \in Nat:
--                          num' = [num EXCEPT ![self] = k]
--                     /\ pc' = [pc EXCEPT ![self] = "exit"]
--                  \/ /\ num' = [num EXCEPT ![self] = 0]
--                     /\ pc' = [pc EXCEPT ![self] = "ncs"]
--               /\ UNCHANGED << flag, unchecked, max, nxt >>
action evtExit_branch1 (self : process) {
  require pc self exit
  let k ← pick seq_t
  num self N := decide $ N = k
  pc self S := decide $ S = exit
}

action evtExit_branch2 (self : process) {
  require pc self exit
  num self N := decide $ N = seq.zero
  pc self S := decide $ S = ncs
}

invariant [pc_total] ∀ p, pc p ncs = true ∨ pc p e1 ∨ pc p e2 ∨ pc p e3 ∨ pc p cs ∨ pc p e4 ∨ pc p w1 ∨ pc p w2 ∨ pc p exit
invariant [local_max_unique] max P N ∧ max P M → N = M
invariant [local_num_unique] num P N ∧ num P M → N = M
invariant [local_pc_unique] pc P S ∧ pc P T → S = T
invariant [local_nxt_unique] nxt P N ∧ nxt P M → N = M
invariant [p1_non_zero_num] pc I e4 ∨ pc I w1 ∨ pc I w2 ∨ pc I cs → ¬(num I seq.zero)
invariant [p2_flag_e2_e3] pc I e2 ∨ pc I e3 → flag I
invariant [p3_nxt_not_self] pc I w2 → ¬ (nxt I I)
invariant [p4_unchecked_not_self] pc I w1 ∨ pc I w2 → ¬(unchecked I I)
invariant [p5_critical_section] pc I w1 ∨ pc I w2 → ∀j, (j ≠ I ∧ ¬unchecked I j) → before I j
invariant [p6_nxt_e2_e3]
  pc I w2 ∧
  ((∃ni, nxt I ni ∧ pc ni e2 ∧ ¬unchecked ni I) ∨ (∃ni, nxt I ni ∧ pc ni e3)) →
  (∃numi nxti maxnxti, num I numi ∧ nxt I nxti ∧ max nxti maxnxti ∧ seq.le numi maxnxti)
invariant [p7_cs_precedes_all] pc I cs → ∀j, (j ≠ I) → before I j

/- Ensures no two processes are in critical section simultaneously. -/
safety [mutual_exclusion] pc I cs ∧ pc J cs → I = J
termination true = true
set_option maxHeartbeats 250000
#gen_spec

#model_check { process := Fin 2, seq_t := Fin 3, pc_state := pc_state_IndT } { one_th := 0, one := 1 }


end Bakery
