import Veil.DSL
import Veil.Std

veil module Ring


type node
instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

relation leader : node → Prop
relation pending : node → node → Prop

#gen_state

after_init {
  leader N := False
  pending M N := False
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

safety [single_leader] leader L → le N L

#gen_spec

/--
info: @[invProof]
  theorem init_single_leader :
      ∀ (rd : ρ) (st' : σ),
        (@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).assumptions rd st' →
          (@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).init rd st' →
            (@Ring.single_leader node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader) rd st' :=
    by ((unhygienic intros); solve_clause[initSimp, actSimp]Ring.single_leader)
  ⏎
  @[invProof]
  theorem send_tr_single_leader :
      ∀ (rd : ρ) (st st' : σ),
        (@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).assumptions rd st →
          (@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).inv rd st →
            (@Ring.send.ext.tr node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader) rd st st' →
              (@Ring.single_leader node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader) rd st' :=
    by solve_tr_clause Ring.send.ext.tr Ring.single_leader
  ⏎
  @[invProof]
  theorem recv_tr_single_leader :
      ∀ (rd : ρ) (st st' : σ),
        (@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).assumptions rd st →
          (@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).inv rd st →
            (@Ring.recv.ext.tr node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader) rd st st' →
              (@Ring.single_leader node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader) rd st' :=
    by solve_tr_clause Ring.recv.ext.tr Ring.single_leader
-/
#guard_msgs(whitespace := lax) in
set_option veil.vc_gen "transition" in #check_invariants?

end Ring
