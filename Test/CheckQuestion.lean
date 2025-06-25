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
  theorem initializer_tr_single_leader :
      TwoState.meetsSpecificationIfSuccessful
        (@initializer.ext.twoState node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader)
        (fun rd st => (@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).assumptions rd st) fun rd st' =>
        @Ring.single_leader node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader rd st' :=
    by solve_tr_clause initializer.ext.twoState Ring.single_leader
  ⏎
  @[invProof]
  theorem send_doesNotThrow :
      ∀ (ex : Int) (rd : ρ) (st : σ),
        ∀ (n : node) (next : node),
          (@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).assumptions rd st →
            (@Ring.send.ext.wpEx node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader ex n next) (fun _ _ _ => True)
              rd st :=
    by solve_wp_clause Ring.send.ext.wpEx
  ⏎
  @[invProof]
  theorem send_tr_single_leader :
      ∀ (n : node) (next : node),
        TwoState.meetsSpecificationIfSuccessful
          (@Ring.send.ext.twoState node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader n next)
          (fun rd st =>
            And ((@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).assumptions rd st)
              ((@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).inv rd st))
          fun rd st' => @Ring.single_leader node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader rd st' :=
    by solve_tr_clause Ring.send.ext.twoState Ring.single_leader
  ⏎
  @[invProof]
  theorem recv_doesNotThrow :
      ∀ (ex : Int) (rd : ρ) (st : σ),
        ∀ (sender : node) (n : node) (next : node),
          (@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).assumptions rd st →
            (@Ring.recv.ext.wpEx node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader ex sender n next)
              (fun _ _ _ => True) rd st :=
    by solve_wp_clause Ring.recv.ext.wpEx
  ⏎
  @[invProof]
  theorem recv_tr_single_leader :
      ∀ (sender : node) (n : node) (next : node),
        TwoState.meetsSpecificationIfSuccessful
          (@Ring.recv.ext.twoState node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader sender n next)
          (fun rd st =>
            And ((@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).assumptions rd st)
              ((@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).inv rd st))
          fun rd st' => @Ring.single_leader node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader rd st' :=
    by solve_tr_clause Ring.recv.ext.twoState Ring.single_leader
-/
#guard_msgs(whitespace := lax) in
set_option veil.vc_gen "transition" in #check_invariants?

end Ring
