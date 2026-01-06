import Veil

-- https://github.com/tlaplus/Examples/blob/c2641e69204ed241cdf548d9645ac82df55bfcd8/specifications/ewd840/EWD840.tla

veil module EWD840

type seq_t
enum Color = {white, black}

relation active: seq_t → Bool
relation colormap: seq_t → Color → Bool
individual tpos: seq_t
individual tcolor : Color

instantiate seq : TotalOrderWithZero seq_t
immutable individual one : seq_t
immutable individual max_seq_t : seq_t

#gen_state

theory ghost relation lt (x y : seq_t) := (seq.le x y ∧ x ≠ y)
theory ghost relation next (x y : seq_t) := (lt x y ∧ ∀ z, lt x z → seq.le y z)

assumption [zero_one] next seq.zero one
assumption [max_seq_prop] ∀n, (n ≠ max_seq_t → lt n max_seq_t) ∧ (lt seq.zero max_seq_t)

procedure pred (n : seq_t) {
  let k ← pick seq_t
  assume next k n
  return k
}

after_init {
  -- let b ← pick Bool
  active N := *
  -- Each node independently picks a color (matching TLA+ color \in [Node -> Color])
  colormap N C := *
  assume ∀n, ∃c, colormap n c
  assume ∀n c1 c2, colormap n c1 ∧ colormap n c2 → c1 = c2
  tpos := *
  tcolor := black
}

action InitStateProbe {
  require tpos = seq.zero
  require tcolor = black ∨ colormap seq.zero black
  tpos := max_seq_t
  tcolor := white
  active N := active N
  colormap seq.zero C := C == white
}

action PassToken(i : seq_t) {
  require i ≠ seq.zero
  require tpos = i;
  require ¬active i ∨ colormap i black ∨ tcolor = black
  -- let numx :| tpos = numx
  -- let num' ← pred
  let num' ← pred i
  tpos := num'
  tcolor := if colormap i black then black else tcolor
  colormap i C := C == white
}

action SendMsg(i : seq_t) {
  require active i
  -- require ∀ j, j ≠ i → active j
  let j :| j ≠ i
  active j := true
  colormap i C := if lt i j then C == black else colormap i C
}

action Deactivate(i : seq_t) {
  require active i
  active i := false
}

ghost relation terminated := ∀i, ¬ active i

termination [allDeactive] ∀i, ¬ active i
ghost relation terminationDetected :=
  tpos = seq.zero ∧ tcolor = white ∧ colormap seq.zero white ∧ ¬ active seq.zero

invariant [TerminationDetection] (terminationDetected → terminated)

-- ghost relation P0 := ∀i, lt tpos i → ¬ active i
ghost relation P1 := ∃j, (seq.le seq.zero j) ∧ (seq.le j tpos) ∧ colormap j black
ghost relation P2 := tcolor = black
invariant [aux_unique_color] ∀n, colormap n C1 ∧ colormap n C2 → C1 = C2
invariant [Inv] (∀i, lt tpos i → ¬ active i) ∨ (∃j, (seq.le seq.zero j) ∧ (seq.le j tpos) ∧ colormap j black) ∨ (tcolor = black)

#time #gen_spec

#model_check
{ seq_t := Fin 4, Color := Color_IndT }
{ one := 1, max_seq_t := 3  }

end EWD840
