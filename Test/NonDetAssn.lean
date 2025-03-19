import Veil.DSL

veil module Test


type node

individual x : Prop
relation r : node -> node -> Prop

#gen_state

action nondet_individual = {
  x := *
}

/--
info: def Test.nondet_individual : {node : Type} →
  [node_dec : DecidableEq node] → [node_ne : Nonempty node] → Wp Mode.internal (State node) PUnit :=
fun {node} [DecidableEq node] [Nonempty node] s post => ∀ (t : Prop), post PUnit.unit { x := t, r := s.r }
-/
#guard_msgs in
#print nondet_individual

action quantify_fresh (n : node) = {
  -- let n <- fresh node
  r n N := *
}

/--
info: def Test.quantify_fresh : {node : Type} →
  [node_dec : DecidableEq node] → [node_ne : Nonempty node] → node → Wp Mode.internal (State node) PUnit :=
fun {node} [DecidableEq node] [Nonempty node] n s post =>
  ∀ (t : node → node → Prop), post PUnit.unit { x := s.x, r := fun x N => if x = n then t n N else s.r x N }
-/
#guard_msgs in
#print quantify_fresh

action double_quant = {
  r N N := *
}

/--
info: def Test.double_quant : {node : Type} →
  [node_dec : DecidableEq node] → [node_ne : Nonempty node] → Wp Mode.internal (State node) PUnit :=
fun {node} [DecidableEq node] [Nonempty node] s post =>
  ∀ (t : node → node → Prop), post PUnit.unit { x := s.x, r := fun N x => if x = N then t N N else s.r N x }
-/
#guard_msgs in
#print double_quant

def top_level (n : node) := do' .external in
  require x
  if x then
    r N N := *
  else
    r n n := *
  return r

def top_level' (n : node) := do' .external in
  let freshR <- fresh node -> node -> Prop
  let freshR' <- fresh node -> node -> Prop
  require x
  if x then
    r N N := freshR N N
  else
    r n n := freshR' n n
  return r

example : top_level = top_level' := rfl

end Test
