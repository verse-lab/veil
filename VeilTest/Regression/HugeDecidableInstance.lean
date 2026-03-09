import Veil

veil module Test

type Proc
type mem_type
type addr_type

enum mem_loc_type = {mem_loc_init,mem_memc,pio_memc}
enum op_ack_type  = {nGnRnE,nGnRE,nGRE,GRE,normal}

type LClockType

instantiate LClock : TotalOrderWithZero LClockType

individual ltime : LClockType

enum OpType = {nop,write,read}
enum LocType = {init_l,cf_mem_l,mem_c_l,dramc_l}
enum ph_type      = {nop_ph,wr_ph,rd_ph,cpl_ph}

function evs_m            : LClockType → mem_type
function evs_a            : LClockType → addr_type
function evs_req          : LClockType → OpType
function evs_mem_loc      : LClockType → mem_loc_type
function evs_op_ack       : LClockType → op_ack_type

relation wr  : Proc → mem_type → addr_type → LClockType → Bool
relation rd  : Proc → mem_type → addr_type → LClockType → Bool

#gen_state

theory ghost relation lt   (x y : LClockType) := (LClock.le x y ∧ x ≠ y)
theory ghost relation next (x y : LClockType) := (lt x y ∧ ∀ z, lt x z → LClock.le y z)

ghost relation nGR(OP_ACK : op_ack_type)       := (OP_ACK=nGRE    ∨ OP_ACK=GRE)
ghost relation nGnR(OP_ACK : op_ack_type)      := (OP_ACK=nGnRE   ∨ OP_ACK=nGnRnE)

after_init {
  ltime              := LClock.zero
  evs_req T          := nop
  evs_mem_loc T      := mem_loc_init

  wr P M A T := false
  rd P M A T := false
}

procedure succ (n : LClockType) {
   let k :| next n k
   return k
}

-- set_option trace.veil.debug true
set_option maxHeartbeats 90000

action step_north (ph : ph_type)(p : Proc)(m : mem_type)(a : addr_type) (choose_op_ack : op_ack_type) {
  let (next_ltime:LClockType) ← succ ltime
  let t :| evs_req t=write ∧ (evs_m t)=m ∧ (evs_a t)=a
  let op_ack :=
    if (evs_req t=read ∨ evs_req t=write) ∧ evs_m t=m ∧ evs_a t=a then
        if evs_mem_loc t=mem_memc then
          if choose_op_ack=normal ∨ choose_op_ack=GRE ∨ choose_op_ack=nGRE then
            choose_op_ack
          else
            normal
        else
          if choose_op_ack=nGnRnE ∨ choose_op_ack=nGnRE ∨ choose_op_ack=GRE ∨ choose_op_ack=nGRE then
            choose_op_ack
          else
            nGnRnE
    else
      normal
  let pio_new  := false
  let wr_new   := ph=wr_ph
  let devb     := true
  -- NOTE: This is where a huge decidable instance is generated
  let ordser_wr :=  ∃ M A T, wr_new ∧ devb ∧ nGnR op_ack ∧ wr p M A T ∧ (evs_req T=write) ∧ nGnR (evs_op_ack T) ∧ pio_new ∧ ¬(M=m ∧ A=a) ∨
                             wr_new ∧ devb ∧ nGnR op_ack ∧ rd p M A T ∧ (evs_req T=read) ∧ nGnR (evs_op_ack T) ∨
                             wr_new ∧ devb ∧ nGnR op_ack ∧ rd p M A T ∧ (evs_req T=read) ∧ nGR (evs_op_ack T) ∨
                             wr_new ∧ devb ∧ nGR op_ack  ∧ rd p M A T ∧ (evs_req T=read) ∧ nGnR (evs_op_ack T) ∨
                             wr_new ∧ devb ∧ nGR op_ack  ∧ rd p M A T ∧ (evs_req T=read) ∧ nGR (evs_op_ack T)
  if wr_new ∧ ¬ordser_wr then
    pure ()
}

-- #gen_spec

end Test
