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
      ∀ (st : σ),
        (@System node node_dec node_ne σ σ_substate).assumptions st →
          (@System node node_dec node_ne σ σ_substate).inv st →
            (@Test.foo.ext node node_dec node_ne σ σ_substate) st fun _ (st' : σ) =>
              @Test.inv_0 node node_dec node_ne σ σ_substate st' :=
    by solve_wp_clause Test.foo.ext Test.inv_0

end Test
