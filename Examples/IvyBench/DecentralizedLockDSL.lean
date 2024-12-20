import Veil.DSL
import Examples.DSL.PaxosDSL
-- https://github.com/aman-goel/ivybench/blob/master/ex/ivy/decentralized-lock.ivy


section DecentralizedLock
open Classical

type node
type time

relation le : time -> time -> Prop
relation has_lock : node -> Prop
relation msg : node -> time -> Prop
function epoch : node -> time

individual first : node
individual zero : time
individual max : time

#gen_state DecentralizedLock

after_init {
  fresh first' : node in
  fresh zero' : time in
  fresh max' : time in
  first := first';
  zero := zero';
  max := max';
  has_lock X := X = first';
  msg _ _ := False;
  epoch _ := zero';
  require ∀ (X : time), le X X; -- axiom
  require ∀ (X : time), ∀ (Y : time), le X Y ∧ le Y Z → le X Z; -- axiom
  require ∀ (X : time), ∀ (Y : time), le X Y ∧ le Y X → X = Y; -- axiom
  require ∀ (X : time), ∀ (Y : time), le X Y ∨ le Y X; -- axiom
  require ∀ (X : time), le zero' X; -- axiom
  require ∀ (X : time), le X max' -- axiom
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

#gen_spec DecentralizedLock

safety [mutex] ¬ (has_lock X ∧ has_lock Y ∧ X ≠ Y)

invariant [manual_1] ¬ (X ≠ Y ∧ (has_lock X ∨ (msg X T ∧ ¬ le T (epoch X))) ∧ (has_lock Y ∨ (msg Y S ∧ ¬ le S (epoch Y))))
invariant [manual_2] ¬ (has_lock X ∧ (msg X T ∧ ¬ le T (epoch X)))
invariant [manual_3] ¬ (S ≠ T ∧ msg Y S ∧ msg Y T ∧ ¬ le T (epoch Y) ∧ ¬ le S (epoch Y))

#check_invariants


end DecentralizedLock
