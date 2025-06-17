import Veil.DSL

veil module TwoStateTransitionTest

type address
variable (is_byz : address → Prop)

relation initial_msg (originator : address) (dst : address) (r : address) (v : address)

#gen_state

after_init {
  initial_msg O D R V := False
}

#guard_msgs in
internal transition byz = {
  (∀ (src dst : address) (r : address) (v : address),
    (¬ is_byz src ∧ (initial_msg src dst r v ↔ initial_msg' src dst r v)) ∨
    (is_byz src ∧ (initial_msg src dst r v → initial_msg' src dst r v)))
}

#guard_msgs in
internal transition withargs (r : address) = {
  (∀ (src dst : address) (v : address),
    (¬ is_byz src ∧ (initial_msg src dst r v ↔ initial_msg' src dst r v)) ∨
    (is_byz src ∧ (initial_msg src dst r v → initial_msg' src dst r v)))
}

invariant True

#gen_spec

-- The `wp read` should be simplified, but isn't
#print byz.ext.wpGen

  @[invProof]
  theorem byz_inv_0 :
      ∀ (rd : ρ) (st : σ),
        (@System address address_dec address_ne is_byz σ σ_substate ρ ρ_reader).assumptions rd st →
          (@System address address_dec address_ne is_byz σ σ_substate ρ ρ_reader).inv rd st →
            (@TwoStateTransitionTest.byz.ext.wpSucc address address_dec address_ne is_byz σ
                σ_substate ρ ρ_reader)
              (fun _ (rd : ρ) (st' : σ) =>
                @TwoStateTransitionTest.inv_0 address address_dec address_ne is_byz σ σ_substate ρ
                  ρ_reader rd st')
              rd st :=
    by
      ( dsimp only [TwoStateTransitionTest.byz.ext.wpSucc, wpSimp]
        dsimp only [invSimp]
        skip
        intros rd st; sdestruct_hyps
        first
        | intro ass_ inv_; intro (st' : @State address is_byz);
          unhygienic cases st'; revert ass_ inv_; dsimp only
        | try dsimp only
          try simp only [exists_imp, and_imp]
          unhygienic intros
          skip
          try simp only [ifSimp]
          -- even if you try to `simp [wpSimp]` here, it still doesn't work
          simp [wpSimp]
          try sdestruct_hyps
          try dsimp only at *
          try concretize_state)
      ((try split_ifs with exists_imp, and_imp) <;> sauto_all)

end TwoStateTransitionTest
