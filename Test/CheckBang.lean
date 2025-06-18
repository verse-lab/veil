import Veil.DSL
import Veil.Std

veil module Ring


type node
instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

individual indv : Bool
relation leader : node → Prop
relation pending : node → node → Prop

#gen_state

after_init {
  leader N := False
  pending M N := False
  indv := False
}

action send (n next : node) = {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  pending n next := True
}

action recv (sender n next : node) = {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  require pending sender n
  pending sender n := *
  if (sender = n) then
    leader n := True
  else
    if (le n sender) then
      pending sender next := True
}

action ruin_inv = {
  indv := False
}

safety [single_leader] leader L → le N L
invariant pending S D ∧ btw S N D → le N S
invariant [indv_true] indv

#gen_spec

/--
info: Initialization must establish the invariant:
  single_leader ... ✅
  inv_1 ... ✅
  indv_true ... ❌
The following set of actions must preserve the invariant and successfully terminate:
  send
    single_leader ... ✅
    inv_1 ... ✅
    indv_true ... ✅
  recv
    single_leader ... ❌
    inv_1 ... ✅
    indv_true ... ✅
  ruin_inv
    single_leader ... ✅
    inv_1 ... ✅
    indv_true ... ❌
---
info: @[invProof]
  theorem init_indv_true :
      ∀ (rd : ρ) (st' : σ),
        (@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).assumptions rd st' →
          (@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).init rd st' →
            (@Ring.indv_true node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader) rd st' :=
    by ((unhygienic intros); solve_clause[initSimp, actSimp]Ring.indv_true)
  ⏎
  @[invProof]
  theorem recv_tr_single_leader :
      ∀ (rd : ρ) (st st' : σ),
        (@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).assumptions rd st →
          (@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).inv rd st →
            (@Ring.recv.ext.tr node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader) rd st st' →
              (@Ring.single_leader node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader) rd st' :=
    by solve_tr_clause Ring.recv.ext.tr Ring.single_leader
  ⏎
  @[invProof]
  theorem ruin_inv_tr_indv_true :
      ∀ (rd : ρ) (st st' : σ),
        (@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).assumptions rd st →
          (@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).inv rd st →
            (@Ring.ruin_inv.ext.tr node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader) rd st st' →
              (@Ring.indv_true node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader) rd st' :=
    by solve_tr_clause Ring.ruin_inv.ext.tr Ring.indv_true
  ⏎
  ⏎
---
info: Run with `set_option veil.printCounterexamples true` to print counter-examples.
---
warning: Trusting the SMT solver for 9 theorems.
---
error: The invariant is not inductive: 3 clauses are not preserved!
-/
#guard_msgs(whitespace := lax) in
set_option veil.vc_gen "transition" in #check_invariants!

end Ring
