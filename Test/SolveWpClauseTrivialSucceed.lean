import Veil

veil module Test
type node

individual x : node

#gen_state

after_init {
  pure ()
}

action foo = { pure () }

invariant True

#gen_spec

#guard_msgs in
  theorem foo_inv_0 :
      ∀ (rd : ρ) (st : σ),
        (@System node node_dec node_ne σ σ_substate ρ ρ_reader).assumptions rd st →
          (@System node node_dec node_ne σ σ_substate ρ ρ_reader).inv rd st →
            (@Test.foo.ext.wpSucc node node_dec node_ne σ σ_substate ρ ρ_reader) (fun _ (rd' : ρ) (st' : σ) =>
              @Test.inv_0 node node_dec node_ne σ σ_substate ρ ρ_reader rd' st') rd st :=
    by solve_wp_clause Test.foo.ext.wpSucc Test.inv_0

end Test
