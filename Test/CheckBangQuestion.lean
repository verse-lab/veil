import Veil.DSL
import Examples.DSL.Std

namespace Ring
open Classical

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
info:
@[invProof]
  theorem init_Ring.indv_true :
      ∀ (st : @State node),
        (@System node node_dec node_ne tot btwn).assumptions st →
          (@System node node_dec node_ne tot btwn).init st →
            (@Ring.indv_true node node_dec node_ne tot btwn) st :=
    by (unhygienic intros); exact sorry

  @[invProof]
  theorem ruin_inv_Ring.indv_true :
      ∀ (st st' : @State node),
        (@System node node_dec node_ne tot btwn).assumptions st →
          (@System node node_dec node_ne tot btwn).inv st →
            (@ruin_inv.tr node node_dec node_ne tot btwn) st st' →
              (@Ring.indv_true node node_dec node_ne tot btwn) st' :=
    by (unhygienic intros); exact sorry

  @[invProof]
  theorem recv_Ring.single_leader :
      ∀ (st st' : @State node),
        (@System node node_dec node_ne tot btwn).assumptions st →
          (@System node node_dec node_ne tot btwn).inv st →
            (@recv.tr node node_dec node_ne tot btwn) st st' →
              (@Ring.single_leader node node_dec node_ne tot btwn) st' :=
    by (unhygienic intros); exact sorry
-/
#guard_msgs(whitespace := lax) in
#check_invariants!


end Ring
