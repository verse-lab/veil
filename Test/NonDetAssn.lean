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
  [node_dec : DecidableEq node] →
    [node_ne : Nonempty node] → {σ : Type} → [σ_substate : IsSubStateOf (State node) σ] → Wp Mode.internal σ PUnit :=
fun {node} [DecidableEq node] [Nonempty node] {σ} [IsSubStateOf (State node) σ] s post =>
  ∀ (t : Prop), post PUnit.unit (setIn { x := t, r := (getFrom s).r } s)
-/
#guard_msgs in
#print nondet_individual

action quantify_fresh (n : node) = {
  -- let n <- fresh node
  r n N := *
}

/--
info: def Test.quantify_fresh : {node : Type} →
  [node_dec : DecidableEq node] →
    [node_ne : Nonempty node] →
      {σ : Type} → [σ_substate : IsSubStateOf (State node) σ] → node → Wp Mode.internal σ PUnit :=
fun {node} [DecidableEq node] [Nonempty node] {σ} [IsSubStateOf (State node) σ] n s post =>
  ∀ (t : node → node → Prop),
    post PUnit.unit (setIn { x := (getFrom s).x, r := fun x N => if x = n then t n N else (getFrom s).r x N } s)
-/
#guard_msgs in
#print quantify_fresh

action double_quant = {
  r N N := *
}

/--
info: def Test.double_quant : {node : Type} →
  [node_dec : DecidableEq node] →
    [node_ne : Nonempty node] → {σ : Type} → [σ_substate : IsSubStateOf (State node) σ] → Wp Mode.internal σ PUnit :=
fun {node} [DecidableEq node] [Nonempty node] {σ} [IsSubStateOf (State node) σ] s post =>
  ∀ (t : node → node → Prop),
    post PUnit.unit (setIn { x := (getFrom s).x, r := fun N x => if x = N then t N N else (getFrom s).r N x } s)
-/
#guard_msgs in
#print double_quant

def top_level (n : node) := do' .external as [State] in
  require x
  if x then
    r N N := *
  else
    r n n := *
  return r

def top_level' (n : node) := do' .external as [State]in
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
