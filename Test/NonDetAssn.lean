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
info: def Test.nondet_individual.wpGen : {node : Type} →
  [node_dec : DecidableEq node] →
    [node_ne : Nonempty node] →
      {σ : Type} →
        [σ_substate : IsSubStateOf (State node) σ] →
          {ρ : Type} →
            [ρ_reader : IsSubReaderOf (Reader node) ρ] → (ExId → Prop) → (PUnit.{1} → ρ → σ → Prop) → ρ → σ → Prop :=
fun {node} [DecidableEq node] [Nonempty node] {σ} [IsSubStateOf (State node) σ] {ρ} [IsSubReaderOf (Reader node) ρ] hd
    post r s =>
  ∀ (t : Prop), post PUnit.unit r (setIn { x := t, r := (getFrom s).r } s)
-/
#guard_msgs in
#print nondet_individual.wpGen

action quantify_pick (n : node) = {
  -- let n <- pick node
  r n N := *
}

/--
info: def Test.quantify_pick.wpGen : {node : Type} →
  [node_dec : DecidableEq node] →
    [node_ne : Nonempty node] →
      {σ : Type} →
        [σ_substate : IsSubStateOf (State node) σ] →
          {ρ : Type} →
            [ρ_reader : IsSubReaderOf (Reader node) ρ] →
              (ExId → Prop) → node → (PUnit.{1} → ρ → σ → Prop) → ρ → σ → Prop :=
fun {node} [DecidableEq node] [Nonempty node] {σ} [IsSubStateOf (State node) σ] {ρ} [IsSubReaderOf (Reader node) ρ] hd n
    post r s =>
  ∀ (t : node → node → Prop),
    post PUnit.unit r (setIn { x := (getFrom s).x, r := fun x N => if x = n then t n N else (getFrom s).r x N } s)
-/
#guard_msgs in
#print quantify_pick.wpGen

action double_quant = {
  r N N := *
}

/--
info: def Test.double_quant.wpGen : {node : Type} →
  [node_dec : DecidableEq node] →
    [node_ne : Nonempty node] →
      {σ : Type} →
        [σ_substate : IsSubStateOf (State node) σ] →
          {ρ : Type} →
            [ρ_reader : IsSubReaderOf (Reader node) ρ] → (ExId → Prop) → (PUnit.{1} → ρ → σ → Prop) → ρ → σ → Prop :=
fun {node} [DecidableEq node] [Nonempty node] {σ} [IsSubStateOf (State node) σ] {ρ} [IsSubReaderOf (Reader node) ρ] hd
    post r s =>
  ∀ (t : node → node → Prop),
    post PUnit.unit r (setIn { x := (getFrom s).x, r := fun N x => if x = N then t N N else (getFrom s).r N x } s)
-/
#guard_msgs in
#print double_quant.wpGen

noncomputable
def top_level (n : node) := do' .external as [Reader], [State] in
  require x
  if x then
    r N N := *
  else
    r n n := *
  return r

noncomputable
def top_level' (n : node) := do' .external as [Reader],[State]in
  let pickR <- pick node -> node -> Prop
  let pickR' <- pick node -> node -> Prop
  require x
  if x then
    r N N := pickR N N
  else
    r n n := pickR' n n
  return r

example : top_level = top_level' := rfl

end Test
