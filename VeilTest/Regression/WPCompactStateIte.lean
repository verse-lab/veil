import Veil

veil module WPCompactStateIte

individual a : Nat
individual b : Bool

#gen_state

#check State.ite_eta_fields

example {p : Prop} [Decidable p] (s1 s2 : State FieldAbstractType) :
    (if p then s1 else s2) =
      State.mk (if p then s1.a else s2.a) (if p then s1.b else s2.b) := by
  simpa using State.ite_eta_fields (p := p) s1 s2

example {p : Prop} [Decidable p] (s1 s2 : State FieldAbstractType) :
    (if p then s1 else s2) =
      State.mk (if p then s1.a else s2.a) (if p then s1.b else s2.b) := by
  simp only [wpCompactStateSimp]

example {p : Prop} [Decidable p]
    (post : State FieldAbstractType → Prop) (s1 s2 : State FieldAbstractType) :
    (if p then post s1 else post s2) =
      letEq (decide p) fun b =>
        post (State.mk (if b then s1.a else s2.a) (if b then s1.b else s2.b)) := by
  simp only [wpCompactIteSimp]
  simp only [wpCompactStateSimp]

set_option linter.unusedVariables false in
example {p : Prop} [Decidable p] (x : Nat) (post : Nat → Prop) (q : Prop) : True := by
  fail_if_success
    have : (if p then letEq x post else q) = letEq x (fun y => if p then post y else q) := by
      simp only [wpCompactIteSimp]
  trivial

example {p q : Prop} [Decidable p] [Decidable q] (post : Nat → Prop) (x y z : Nat) :
    (if p then (if q then post x else post y) else post z) =
      letEq (decide q) fun qb =>
        letEq (decide p) fun pb =>
          post (if pb then (if qb then x else y) else z) := by
  simp only [wpCompactIteSimp]

example {p q r : Prop} [Decidable p] [Decidable q] [Decidable r]
    (post : Nat → Prop) (w x y z : Nat) :
    (if p then (if q then post w else post x) else (if r then post y else post z)) =
      letEq (decide q) fun qb =>
        letEq (decide r) fun rb =>
          letEq (decide p) fun pb =>
            post (if pb then (if qb then w else x) else (if rb then y else z)) := by
  simp only [wpCompactIteSimp]

action compact_act (n : Nat) {
  if n > 10 then
    a := n
  else if n > 0 then
    a := n + 1
  else
    a := 0
}

example (n : Nat) (handler : Int → Prop)
    (post : Unit → Theory → State FieldAbstractType → Prop)
    (th : Theory) (st : State FieldAbstractType) :
    compact_act.ext.wp_local_eq.pred n handler post th st =
      letEq (@decide (n > 0) (Classical.propDecidable (n > 0))) fun b =>
        letEq (@decide (n > 10) (Classical.propDecidable (n > 10))) fun b_1 =>
          post () th
            {
              a :=
                @ite (FieldAbstractType State.Label.a) (b_1 = true)
                  (Classical.propDecidable (b_1 = true)) n
                  (@ite (FieldAbstractType State.Label.a) (b = true)
                    (Classical.propDecidable (b = true)) (n + 1) 0),
              b :=
                @ite (FieldAbstractType State.Label.b) (b_1 = true)
                  (Classical.propDecidable (b_1 = true)) st.b
                  (@ite (FieldAbstractType State.Label.b) (b = true)
                    (Classical.propDecidable (b = true)) st.b st.b) } := by
  unfold compact_act.ext.wp_local_eq.pred
  rfl

end WPCompactStateIte

veil module WPCompactRelationStateIte

type node

relation r : node -> Bool
function f : node -> node
individual a : Bool

#gen_state

#check State.ite_eta_fields

example {node : Type} {p : Prop} [Decidable p] (s1 s2 : State (FieldAbstractType node)) :
    (if p then s1 else s2) =
      State.mk
        (fun x => if p then s1.r x else s2.r x)
        (fun x => if p then s1.f x else s2.f x)
        (if p then s1.a else s2.a) := by
  simpa using State.ite_eta_fields (node := node) (p := p) s1 s2

example {node : Type} {p : Prop} [Decidable p]
    (post : State (FieldAbstractType node) → Prop) (s1 s2 : State (FieldAbstractType node)) :
    (if p then post s1 else post s2) =
      letEq (decide p) fun b =>
        post
          (State.mk
            (fun x => if b then s1.r x else s2.r x)
            (fun x => if b then s1.f x else s2.f x)
            (if b then s1.a else s2.a)) := by
  simp only [wpCompactIteSimp]
  simp only [wpCompactStateSimp]

after_init {
  r N := false
  f N := N
  a := false
}

action compact_verify (n m : node) {
  if n = m then
    r m := true
  else if r n then
    f n := m
  else
    a := true
}

example {node : Type} [DecidableEq node] [Inhabited node]
    (n m : node) (handler : Int → Prop)
    (post : Unit → Theory node → State (FieldAbstractType node) → Prop)
    (th : Theory node) (st : State (FieldAbstractType node)) :
    compact_verify.ext.wp_local_eq.pred node n m handler post th st =
      letEq (decide (st.r n = true)) fun b =>
        letEq (decide (n = m)) fun b_1 =>
          post () th
            {
              r := fun x =>
                if b_1 = true then
                  if m = x then true else st.r x
                else if b = true then
                  st.r x
                else
                  st.r x,
              f := fun x =>
                if b_1 = true then
                  st.f x
                else if b = true then
                  if n = x then m else st.f x
                else
                  st.f x,
              a :=
                if b_1 = true then
                  st.a
                else if b = true then
                  st.a
                else
                  true } := by
  unfold compact_verify.ext.wp_local_eq.pred
  __veil_neutralize_decidable_inst !
  rfl

invariant [r_refl] r N → r N
invariant [f_refl] f N = f N

#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  r_refl ... ✅
  f_refl ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  compact_verify
    doesNotThrow ... ✅
    r_refl ... ✅
    f_refl ... ✅
-/
#guard_msgs in
#check_invariants

end WPCompactRelationStateIte

set_option veil.experimental.wpCompact false

veil module WPCompactDisabled

type node

relation r : node -> Bool
function f : node -> node
individual a : Bool

#gen_state

action compact_disabled (n m : node) {
  if n = m then
    r m := true
  else if r n then
    f n := m
  else
    a := true
}

set_option linter.unusedVariables false in
example {node : Type} [DecidableEq node] [Inhabited node]
    (n m : node) (handler : Int → Prop)
    (post : Unit → Theory node → State (FieldAbstractType node) → Prop)
    (th : Theory node) (st : State (FieldAbstractType node)) : True := by
  fail_if_success
    have :
        compact_disabled.ext.wp_local_eq.pred node n m handler post th st =
          letEq (decide (st.r n = true)) fun b =>
            letEq (decide (n = m)) fun b_1 =>
              post () th
                {
                  r := fun x =>
                    if b_1 = true then
                      if m = x then true else st.r x
                    else if b = true then
                      st.r x
                    else
                      st.r x,
                  f := fun x =>
                    if b_1 = true then
                      st.f x
                    else if b = true then
                      if n = x then m else st.f x
                    else
                      st.f x,
                  a :=
                    if b_1 = true then
                      st.a
                    else if b = true then
                      st.a
                    else
                      true } := by
      unfold compact_disabled.ext.wp_local_eq.pred
      __veil_neutralize_decidable_inst !
  trivial

end WPCompactDisabled

set_option veil.experimental.wpCompact true
