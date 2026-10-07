module

public import Veil

-- https://github.com/tlaplus/Examples/blob/c2641e69204ed241cdf548d9645ac82df55bfcd8/specifications/ewd840/EWD840.tla

veil module EWD840

param n : Nat
enum Color = {white, black}

relation active: (Fin n.succ) → Bool
function colormap: (Fin n.succ) → Color
individual tpos: (Fin n.succ)
individual tcolor : Color

veil_set_field_representation relation Veil.ArrayAsFinset
veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

-- Init ==
--   /\ active \in [Node -> BOOLEAN]
--   /\ color \in [Node -> Color]
--   /\ tpos \in Node
--   /\ tcolor = "black"
/- Has the same num of states as TLA+ version. -/
after_init {
  active := *
  colormap := *
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
  let zero := ⟨0, Nat.zero_lt_succ n⟩
  require tpos = zero
  require tcolor = black ∨ colormap zero = black
  tpos := Fin.last n
  tcolor := white
  colormap zero := white
}

-- System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)
-- PassToken(i) ==
--   /\ tpos = i
--   /\ ~ active[i] \/ color[i] = "black" \/ tcolor = "black"
--   /\ tpos' = i-1
--   /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
--   /\ active' = active
--   /\ color' = [color EXCEPT ![i] = "white"]
action PassToken {
  let zero := ⟨0, Nat.zero_lt_succ n⟩
  let i := tpos
  require i ≠ zero
  require ¬active i ∨ colormap i = black ∨ tcolor = black
  tpos := i - 1     -- FIXME: If the first `require` can introduce a hypothesis, then we can use `Fin.pred`
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
action SendMsg (i : Fin n.succ) {
  require active i
  let j :| j ≠ i
  active j := true
  if j > i then
    colormap i := black
}

-- Deactivate(i) ==
--   /\ active[i]
--   /\ active' = [active EXCEPT ![i] = FALSE]
--   /\ UNCHANGED <<color, tpos, tcolor>>
action Deactivate (i : Fin n.succ) {
  require active i
  active i := false
}


ghost relation terminated := ∀i, ¬ active i
termination [allDeactive] terminated
ghost relation terminationDetected :=
  let zero := ⟨0, Nat.zero_lt_succ n⟩
  tpos = zero ∧ tcolor = white ∧ colormap zero = white ∧ ¬ active zero

invariant [TerminationDetection] (terminationDetected → terminated)

ghost relation P0 := ∀ i > tpos, ¬ active i
ghost relation P1 := ∃ j ≤ tpos, colormap j = black
ghost relation P2 := tcolor = black
invariant [Inv] P0 ∨ P1 ∨ P2

#gen_spec

#model_check compiled
{ n := 3 }

end EWD840
