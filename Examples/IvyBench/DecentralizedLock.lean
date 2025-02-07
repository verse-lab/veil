import Veil
-- https://github.com/aman-goel/ivybench/blob/master/ex/ivy/decentralized-lock.ivy


namespace DecentralizedLock
open Classical

type node
type time

immutable relation le : time -> time -> Prop
relation has_lock : node -> Prop
relation msg : node -> time -> Prop
function epoch : node -> time

immutable individual first : node
immutable individual zero : time
immutable individual max : time

#gen_state

assumption ∀ (x: time), le x X
assumption ∀ (x y z : time), le x y ∧ le y z → le x z
assumption ∀ (x y : time), le x y ∧ le y x → x = y
assumption ∀ (x y : time), le x y ∨ le y x
assumption ∀ (x : time), le zero x
assumption ∀ (x : time), le x max

after_init {
  has_lock X := X = first;
  msg Y T := False;
  epoch X := zero
}

action take_lock (x : node) (y : node) (t : time) = {
    require msg y t;
    require ¬ le t (epoch y);
    has_lock y := True;
    epoch y := t
}

action release_lock (x : node) (y : node) (t : time) = {
    require has_lock x;
    require ¬ le t (epoch x);
    has_lock x := False;
    msg y t := True
}

safety [mutex] ¬ (has_lock X ∧ has_lock Y ∧ X ≠ Y)

invariant [manual_1] ¬ (X ≠ Y ∧ (has_lock X ∨ (msg X T ∧ ¬ le T (epoch X))) ∧ (has_lock Y ∨ (msg Y S ∧ ¬ le S (epoch Y))))
invariant [manual_2] ¬ (has_lock X ∧ (msg X T ∧ ¬ le T (epoch X)))
invariant [manual_3] ¬ (S ≠ T ∧ msg Y S ∧ msg Y T ∧ ¬ le T (epoch Y) ∧ ¬ le S (epoch Y))

#gen_spec

set_option veil.smt.solver "cvc5" in
#check_invariants



end DecentralizedLock
