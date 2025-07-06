import Veil

veil module Ring

type node
instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

relation leader : node -> Prop
relation pending : node -> node -> Prop

#gen_state

after_init {
  leader N := False
  pending M N := False
}

action send = {
  let n : node ← pick
  let next : node ← pick
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  pending n next := True
}

action recv = {
  let sender : node ← pick
  let n : node ← pick
  let next : node ← pick
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  require pending sender n
  -- message may or may not be removed
  -- this models that multiple messages might be in flight
  pending sender n := *
  if (sender = n) then
    leader n := True
  else
    -- pass message to next node
    if (le n sender) then
      pending sender next := True
}

action third = { pure () }

safety [single_leader] leader L → le N L
invariant pending S D ∧ btw S N D → le N S
invariant pending L L → le N L

#gen_spec

#guard_msgs(drop info, drop warning) in
set_option veil.vc_gen "transition" in #check_invariants

  @[invProof]
  theorem recv_single_leader' :
      VeilM.meetsSpecificationIfSuccessful
        (@Ring.recv.ext node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader)
        (fun rd st =>
          And ((@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).assumptions rd)
            ((@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).inv rd st))
        fun _ rd st' =>
        @Ring.single_leader node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader rd st' :=
    by solve_wp_clause Ring.recv.ext Ring.single_leader

  @[invProof]
  theorem recv_single_leader :
      VeilM.meetsSpecificationIfSuccessful
        (@Ring.recv.ext node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader)
        (fun rd st =>
          And ((@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).assumptions rd)
            ((@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).inv rd st))
        fun _ rd st' =>
        @Ring.single_leader node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader rd st' :=
    by
    lift_tr_to_wp Ring.recv single_leader

  @[invProof]
  theorem recv_tr_single_leader' :
      TwoState.meetsSpecificationIfSuccessful
        (@Ring.recv.ext.twoState node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader)
        (fun rd st =>
          And ((@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).assumptions rd)
            ((@System node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader).inv rd st))
        fun rd st' =>
        @Ring.single_leader node node_dec node_ne tot btwn σ σ_substate ρ ρ_reader rd st' :=
    by
    lift_wp_to_tr Ring.recv single_leader

end Ring
