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
      ∀ (st : @State node),
        (@System node node_dec node_ne).assumptions st →
            (@System node node_dec node_ne).inv st →
              (@Test.foo.ext node node_dec node_ne) st fun _ (st' : @State node) =>
                @Test.inv_0 node node_dec node_ne st' :=
    by solve_wlp_clause Test.foo.ext Test.inv_0

end Test
