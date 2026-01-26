import Veil

-- https://github.com/tlaplus/Examples/blob/c2641e69204ed241cdf548d9645ac82df55bfcd8/specifications/ewd840/EWD840.tla

veil module EWD840

type node
type nodesSet
enum Color = {white, black}

relation active: node → Bool
function colormap: node → Color
individual tpos: node
individual tcolor : Color

instantiate seq : TotalOrderWithZero node
instantiate nSet : TSet node nodesSet
immutable individual one : node
immutable individual max_node : node

#gen_state

theory ghost relation lt (x y : node) := (seq.le x y ∧ x ≠ y)
theory ghost relation next (x y : node) := (lt x y ∧ ∀ z, lt x z → seq.le y z)

assumption [zero_one] next seq.zero one
assumption [max_seq_prop] ∀n, seq.le n max_node


-- Init ==
--   /\ active \in [Node -> BOOLEAN]
--   /\ color \in [Node -> Color]
--   /\ tpos \in Node
--   /\ tcolor = "black"
/- Has the same num of states as TLA+ version. -/
after_init {
  let S1 ← pick nodesSet
  let S2 ← pick nodesSet
  active N := if nSet.contains N S1 then true else false
  colormap N := if nSet.contains N S2 then white else black
  tpos := *
  tcolor := black
}


-- InitiateProbe ==
--   /\ tpos = 0
--   /\ tcolor = "black" \/ color[0] = "black"
--   /\ tpos' = N-1
--   /\ tcolor' = "white"
--   /\ active' = active
--   /\ color' = [color EXCEPT ![0] = "white"]
action InitStateProbe {
  require tpos = seq.zero
  require tcolor = black ∨ colormap seq.zero = black
  tpos := max_node
  tcolor := white
  colormap seq.zero := white
}


procedure pred (n : node) {
  let k ← pick node
  assume next k n
  return k
}

-- System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)
-- PassToken(i) ==
--   /\ tpos = i
--   /\ ~ active[i] \/ color[i] = "black" \/ tcolor = "black"
--   /\ tpos' = i-1
--   /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
--   /\ active' = active
--   /\ color' = [color EXCEPT ![i] = "white"]
action PassToken(i : node) {
  require i ≠ seq.zero
  require tpos = i;
  require ¬active i ∨ colormap i = black ∨ tcolor = black
  tpos := ← pred i
  tcolor := if colormap i = black then black else tcolor
  colormap i := white
}


-- Environment == \E i \in Node : SendMsg(i) \/ Deactivate(i)

-- SendMsg(i) ==
--   /\ active[i]
--   /\ \E j \in Node \ {i} :
--         /\ active' = [active EXCEPT ![j] = TRUE]
--         /\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE @]
--   /\ UNCHANGED <<tpos, tcolor>>
action SendMsg (i : node) (j : node) {
  require active i
  require j ≠ i
  active j := true
  colormap i := if lt i j then black else colormap i
}

-- Deactivate(i) ==
--   /\ active[i]
--   /\ active' = [active EXCEPT ![i] = FALSE]
--   /\ UNCHANGED <<color, tpos, tcolor>>
action Deactivate (i : node) {
  require active i
  active i := false
}


termination [allDeactive] ∀i, ¬ active i
ghost relation terminated := ∀i, ¬ active i
ghost relation terminationDetected :=
  tpos = seq.zero ∧ tcolor = white ∧ colormap seq.zero = white ∧ ¬ active seq.zero

invariant [TerminationDetection] (terminationDetected → terminated)

-- ghost relation P0 := ∀i, lt tpos i → ¬ active i
ghost relation P1 := ∃j, (seq.le seq.zero j) ∧ (seq.le j tpos) ∧ colormap j = black
ghost relation P2 := tcolor = black
invariant [Inv] (∀i, lt tpos i → ¬ active i)
∨ (∃j, (seq.le seq.zero j) ∧ (seq.le j tpos) ∧ colormap j = black)
∨ (tcolor = black)

#time #gen_spec

#model_check compiled
{ node := Fin 9,
  nodesSet := Std.ExtTreeSet (Fin 9),
  Color := Color_IndT }
{ one := 1, max_node := 8  }

end EWD840
