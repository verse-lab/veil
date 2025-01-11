import Veil.DSL

section Test

type node

relation r : node -> node -> Prop

#gen_state Test

action foo = {
  fresh n : node in
  r n N := *
}

/--
info: def foo.fn : (node : Type) →
  [inst : DecidableEq node] → [inst_1 : Nonempty node] → Test.State node → Test.State node × Unit → Prop :=
fun node [DecidableEq node] [Nonempty node] =>
  let t := fun st stret => ∃ t, ∀ (x N : node), t = x ∨ stret.fst.r x N = st.r x N;
  t
-/
#guard_msgs in
#print foo.fn

#guard_msgs in
action double_quant = {
  r N N := *
}

end Test
