import Veil.DSL

section Test
open Classical

type node

individual x : Prop
relation r : node -> node -> Prop

#gen_state Test

action nondet_individual = {
  x := *
}

/--
info: def nondet_individual : {node : Type} →
  [node_dec : DecidableEq node] → [node_ne : Nonempty node] → Wlp (Test.State node) PUnit :=
fun {node} [DecidableEq node] [Nonempty node] =>
  let t := fun s post => ∀ (t : Prop), post PUnit.unit { x := t, r := s.r };
  t
-/
#guard_msgs in
#print nondet_individual

action quantify_fresh (n : node) = {
  -- let n <- fresh node
  r n N := *
}

/--
info: def quantify_fresh : {node : Type} →
  [node_dec : DecidableEq node] → [node_ne : Nonempty node] → node → Wlp (Test.State node) PUnit :=
fun {node} [DecidableEq node] [Nonempty node] n =>
  let t := fun s post =>
    ∀ (t : node → node → Prop), post PUnit.unit { x := s.x, r := fun x N => if x = n then t n N else s.r x N };
  t
-/
#guard_msgs in
#print quantify_fresh

action double_quant = {
  r N N := *
}

/--
info: def double_quant : {node : Type} →
  [node_dec : DecidableEq node] → [node_ne : Nonempty node] → Wlp (Test.State node) PUnit :=
fun {node} [DecidableEq node] [Nonempty node] =>
  let t := fun s post =>
    ∀ (t : node → node → Prop), post PUnit.unit { x := s.x, r := fun N x => if x = N then t N N else s.r N x };
  t
-/
#guard_msgs in
#print double_quant

end Test
