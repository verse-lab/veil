module

public import Veil

veil module Bakery

param maxProc : Nat
param maxNum : Nat

abbrev TicketNum (maxNum : Nat) := Fin (maxNum + 1)
abbrev ProcTy (maxProc : Nat) := Fin (maxProc + 1)

enum pc_state = { ncs, e1, e2, e3, e4, w1, w2, cs, exit }

-- Changed: unchecked is now a TSet-based ProcessSet instead of a relation
type ProcessSet
instantiate pSet : TSet (ProcTy maxProc) ProcessSet

function num          : ProcTy maxProc → TicketNum maxNum
relation flag         : ProcTy maxProc → Bool
function unchecked    : ProcTy maxProc → ProcessSet
function max          : ProcTy maxProc → TicketNum maxNum
function nxt          : ProcTy maxProc → ProcTy maxProc
function pc           : ProcTy maxProc → pc_state

veil_set_field_representation relation Veil.ArrayAsFinset
veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

ghost relation prec (a b : TicketNum maxNum × ProcTy maxProc) :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

after_init {
  let zeroNum := ⟨0, Nat.zero_lt_succ maxNum⟩
  let firstProc := ⟨0, Nat.zero_lt_succ maxProc⟩
  num P := zeroNum
  flag P := false
  unchecked P := pSet.empty
  max P := zeroNum
  nxt P := firstProc
  pc P := ncs
}

action evtNCS (self : ProcTy maxProc) {
  require pc self = ncs
  pc self := e1
}

action evtE1 (self : ProcTy maxProc) {
  require pc self = e1
  let branch ← pick Bool
  if branch then
    flag self := !flag self
    pc self := e1
  else
    flag self := true
    unchecked self := pSet.remove self (pSet.ofList (Veil.Enumeration.allValues))   -- NOTE: see comment above
    max self := ⟨0, Nat.zero_lt_succ maxNum⟩
    pc self := e2
}

action evtE2 (self : ProcTy maxProc) {
  require pc self = e2
  if ¬ pSet.isEmpty (unchecked self) then
    let i ← pick { i // i ∈ unchecked self }
    let i := i.val
    unchecked self := pSet.remove i (unchecked self)
    let num_i := num i
    let max_self := max self
    if max_self < num_i then
      max self := num_i
    pc self := e2
  else
    pc self := e3
}

action evtE3 (self : ProcTy maxProc) {
  require pc self = e3
  let branch ← pick Bool
  if branch then
    let k ← pick (TicketNum maxNum)
    num self := k
    pc self := e3
  else
    let j :| max self < j
    num self := j
    pc self := e4
}

action evtE4 (self : ProcTy maxProc) {
  require pc self = e4
  let branch ← pick Bool
  if branch then
    flag self := !flag self
    pc self := e4
  else
    flag self := false
    unchecked self := pSet.remove self (pSet.ofList (Veil.Enumeration.allValues))   -- NOTE: see comment above
    pc self := w1
}

action evtW1 (self : ProcTy maxProc) {
  require pc self = w1
  if ¬ pSet.isEmpty (unchecked self) then
    let i ← pick { i // i ∈ unchecked self }
    let i := i.val
    nxt self := i
    assume ¬ flag (nxt self)
    pc self := w2
  else
    pc self := cs
}

action evtW2 (self : ProcTy maxProc) {
  require pc self = w2
  let nxt_self := nxt self
  let num_self := num self
  let num_nxt_self := num nxt_self
  require num_nxt_self.val = 0 ∨ prec (num_self, self) (num_nxt_self, nxt_self)
  unchecked self := pSet.remove nxt_self (unchecked self)
  pc self := w1
}

action evtCS (self : ProcTy maxProc) {
  require pc self = cs
  pc self := exit
}

action evtExit (self : ProcTy maxProc) {
  require pc self = exit
  let branch ← pick Bool
  if branch then
    let k ← pick (TicketNum maxNum)
    num self := k
    pc self := exit
  else
    num self := ⟨0, Nat.zero_lt_succ maxNum⟩
    pc self := ncs
}

ghost relation num_gt_zero (i : ProcTy maxProc) := ⟨0, Nat.zero_lt_succ maxNum⟩ < num i

ghost relation pc_ncs_e1_exit (j : ProcTy maxProc) := pc j ∈ [ncs, e1, exit]

ghost relation pc_ex (i j : ProcTy maxProc) :=
  pc j = e2 ∧ (i ∈ unchecked j ∨ num i ≤ max j)

ghost relation pc_e3 (i j : ProcTy maxProc) :=
  pc j = e3 ∧ num i ≤ max j

ghost relation pc_e4_w1_w2 (i j : ProcTy maxProc) :=
  pc j ∈ [e4, w1, w2] ∧
  prec (num i, i) (num j, j) ∧
  (pc j ∈ [w1, w2] → i ∈ unchecked j)

ghost relation before (i j : ProcTy maxProc) :=
  num_gt_zero i ∧ (pc_ncs_e1_exit j ∨ pc_ex i j ∨ pc_e3 i j ∨ pc_e4_w1_w2 i j)

ghost relation p1_non_zero_num (i : ProcTy maxProc) :=
  pc i ∈ [e4, w1, w2, cs] → (num i).val ≠ 0

ghost relation p2_flag_e2_e3 (i : ProcTy maxProc) :=
  pc i ∈ [e2, e3] → flag i

ghost relation p3_nxt_not_self (i : ProcTy maxProc) :=
  pc i = w2 → nxt i ≠ i

ghost relation p4_unchecked_not_self (i : ProcTy maxProc) :=
  pc i ∈ [w1, w2] → i ∉ unchecked i

ghost relation p5_critical_section (i : ProcTy maxProc) :=
  pc i ∈ [w1, w2] → ∀ j, j ≠ i → j ∉ unchecked i → before i j

ghost relation p6_nxt_e2_e3 (i : ProcTy maxProc) :=
  pc i = w2 ∧
  ((pc (nxt i) = e2 ∧ i ∉ unchecked (nxt i)) ∨ pc (nxt i) = e3) →
    num i ≤ max (nxt i)

ghost relation p7_cs_precedes_all (i : ProcTy maxProc) :=
  pc i = cs → ∀ j, j ≠ i → before i j

invariant [iinv] ∀ i,
  p1_non_zero_num i ∧
  p2_flag_e2_e3 i ∧
  p3_nxt_not_self i ∧
  p4_unchecked_not_self i ∧
  p5_critical_section i ∧
  p6_nxt_e2_e3 i ∧
  p7_cs_precedes_all i

safety [mutual_exclusion] I ≠ J → ¬ (pc I = cs ∧ pc J = cs)

set_option maxHeartbeats 2500000
#gen_spec
#gen_executable

-- #model_check compiled
-- { maxProc := 2,
--   maxNum := 3,
--   ProcessSet := OrdList (ProcTy 2) }
-- {  }

end Bakery
