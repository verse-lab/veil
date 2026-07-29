import Veil

veil module Test

type Proc

type LClockType

instantiate LClock : TotalOrderWithZero LClockType

individual ltime : LClockType

type        MEM_C_LClockType

instantiate MEM_C_LClock : TotalOrderWithZero MEM_C_LClockType
individual  arr_mem_c_max : MEM_C_LClockType

enum OpType = {nop,write}

enum LocType = {init_l,cf_mem_l,mem_c_l,dramc_l}

function evs_p            : LClockType → Proc
function evs_req          : LClockType → OpType
function evs_loc          : LClockType → LocType
function evs_lt_arr_mem_c : LClockType → MEM_C_LClockType

function here : LClockType → Bool

#gen_state

theory ghost relation lt   (x y : LClockType) := (LClock.le x y ∧ x ≠ y)
theory ghost relation next (x y : LClockType) := (lt x y ∧ ∀ z, lt x z → LClock.le y z)

theory ghost relation lt_arr_mem_c   (x y : MEM_C_LClockType) := (MEM_C_LClock.le x y ∧ x ≠ y)
theory ghost relation arr_mem_c_next (x y : MEM_C_LClockType) := (lt_arr_mem_c x y ∧ ∀ z, lt_arr_mem_c x z → MEM_C_LClock.le y z)

ghost relation prevents(t : LClockType) := ∀ T, lt LClock.zero t ∧ (lt T ltime → ¬ (evs_loc T = dramc_l ∧ lt t T))

after_init {
  ltime            := LClock.zero
  arr_mem_c_max    := MEM_C_LClock.zero

  evs_req T          := nop
  evs_loc T          := init_l
  evs_lt_arr_mem_c T := MEM_C_LClock.zero

  here T := false
}

action step_mem_c {
 let min_arr :| (evs_loc min_arr = mem_c_l) ∧ ∀ t, evs_loc t = mem_c_l → (lt_arr_mem_c (evs_lt_arr_mem_c min_arr) (evs_lt_arr_mem_c t) ∨ min_arr = t)

 if evs_loc min_arr = mem_c_l then
   evs_loc min_arr := dramc_l
   if prevents min_arr then
     here min_arr := true
  assert (¬ prevents min_arr)

 }

end Test
