import Veil.DSL

section Test

type node

individual x : Prop
relation r : node -> node -> Prop

#gen_state Test

action nondet_individual = {
  x := *
}

/-- info: def nondet_individual.tr : (node : Type) →
  [inst : DecidableEq node] → [inst_1 : Nonempty node] → Test.State node → Test.State node → Prop :=
fun node [DecidableEq node] [Nonempty node] =>
  let t := fun st st' => ∀ (a a_1 : node), st'.r a a_1 = st.r a a_1;
  t
-/
#guard_msgs in
#print nondet_individual.tr

action quantify_fresh = {
  fresh n : node in
  r n N := *
}

/--
info: def quantify_fresh.fn : (node : Type) →
  [inst : DecidableEq node] → [inst_1 : Nonempty node] → Test.State node → Test.State node × Unit → Prop :=
fun node [DecidableEq node] [Nonempty node] =>
  let t := fun st stret => ∃ t, (∀ (x N : node), t = x ∨ stret.fst.r x N = st.r x N) ∧ stret.fst.x = st.x;
  t
-/
#guard_msgs in
#print quantify_fresh.fn

#guard_msgs in
action double_quant = {
  r N N := *
}

/--
info: def double_quant.tr : (node : Type) →
  [inst : DecidableEq node] → [inst_1 : Nonempty node] → Test.State node → Test.State node → Prop :=
fun node [DecidableEq node] [Nonempty node] =>
  let t := fun st st' => st'.x = st.x;
  t
-/
#guard_msgs in
#print double_quant.tr

end Test
