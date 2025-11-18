import Veil
import Veil.Core.Tools.Checker.Concrete.Main

veil module EWD840
/-
original TLA+ specification
https://github.com/tlaplus/Examples/blob/master/specifications/ewd840/EWD840.tla -/
/- TLA+ specification of an algorithm for distributed termination
TLA+ specification of an algorithm for distributed termination
detection on a ring, due to Dijkstra, published as EWD 840:
Derivation of a termination detection algorithm for distributed
computations (with W.H.J.Feijen and A.J.M. van Gasteren).
-/

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


assumption [zero_one] next  seq.zero one
-- assumption [max_seq_t] ∀n, (n ≠ max_seq_t → lt seq_t n max_seq_t) ∧ (lt seq_t seq.zero max_seq_t)

procedure pred (n : seq_t) {
  let k ← pick seq_t
  assume next k n
  return k
}


after_init {
  active N := *
  let cₒ ← pick Color
  colormap N C := decide $ C = cₒ
  let pos₀ :| seq.le pos₀ max_seq_t ∧ seq.le seq.zero pos₀
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
  require tcolor = black ∨ colormap seq.zero black
  tpos := max_seq_t
  tcolor := white
  active N := active N
  colormap seq.zero C := C == white
}

-- PassToken(i) ==
--   /\ tpos = i
--   /\ ~ active[i] \/ color[i] = "black" \/ tcolor = "black"
--   /\ tpos' = i-1
--   /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
--   /\ active' = active
--   /\ color' = [color EXCEPT ![i] = "white"]
action PassToken(i : seq_t) {
  require i ≠ seq.zero
  require tpos = i;
  require ¬active i ∨ colormap i black ∨ tcolor = black
  let numx :| tpos = numx
  let num' ← pred numx
  tpos := num'
  tcolor := if colormap i black then black else tcolor
  colormap i C := C == white
}

-- (***************************************************************************)
-- (* An active node i may activate another node j by sending it a message.   *)
-- (* If j>i (hence activation goes against the direction of the token being  *)
-- (* passed), then node i becomes black.                                     *)
-- (***************************************************************************)
-- SendMsg(i) ==
--   /\ active[i]
--   /\ \E j \in Node \ {i} :
--         /\ active' = [active EXCEPT ![j] = TRUE]
--         /\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE @]
--   /\ UNCHANGED <<tpos, tcolor>>

action SendMsg(i : seq_t) {
  require active i
  require ∀ j, j ≠ i → active j
  let j :| j ≠ i
  active j := true
  active j := false
  colormap i C := if lt i j then C == black else colormap i C
}

-- (***************************************************************************)
-- (* Any active node may become inactive at any moment.                      *)
-- (***************************************************************************)
-- Deactivate(i) ==
--   /\ active[i]
--   /\ active' = [active EXCEPT ![i] = FALSE]
--   /\ UNCHANGED <<color, tpos, tcolor>>
action Deactivate(i : seq_t) {
  require active i
  active i := false
}


-- (***************************************************************************)
-- (* Main safety property: if there is a white token at node 0 then every    *)
-- (* node is inactive.                                                       *)
-- (***************************************************************************)
-- terminated == \A i \in Node : ~ active[i]
ghost relation terminated := ∀i, ¬ active i

-- terminationDetected ==
--   /\ tpos = 0 /\ tcolor = "white"
--   /\ color[0] = "white" /\ ~ active[0]
ghost relation terminationDetected :=
  tpos = seq.zero ∧ tcolor = white ∧ colormap seq.zero white ∧ ¬ active seq.zero

-- TerminationDetection == terminationDetected => terminated
-- invariant [TerminationDetection] (terminationDetected → terminated)
invariant [TerminationDetection] (tpos = seq.zero ∧ tcolor = white ∧ colormap seq.zero white ∧ ¬ active seq.zero) → (∀i, ¬ active i)

-- Inv ==
--   \/ P0:: \A i \in Node : tpos < i => ~ active[i]
--   \/ P1:: \E j \in 0 .. tpos : color[j] = "black"
--   \/ P2:: tcolor = "black"
ghost relation P0 := ∀i, lt tpos i → ¬ active i
ghost relation P1 := ∃j, (seq.le seq.zero j) ∧ (seq.le j tpos) ∧ colormap j black
ghost relation P2 := tcolor = black
invariant [aux_unique_color] ∀n, colormap n C1 ∧ colormap n C2 → C1 = C2
invariant [Inv] (∀i, lt tpos i → ¬ active i) ∨ (∃j, (seq.le seq.zero j) ∧ (seq.le j tpos) ∧ colormap j black) ∨ (tcolor = black)

#gen_spec
#check_invariants

#gen_exec
#finitizeTypes (Fin 10), Color
-- EWD840-9:
/-
VeilM: 89831ms (31236 states)
TLC: 39s
Apalach: 5s
-/
def view (st : StateConcrete) := hash st
def detect_prop : TheoryConcrete → StateConcrete → Bool := (fun ρ σ => Inv ρ σ)
def terminationC : TheoryConcrete → StateConcrete → Bool := (fun ρ σ => true)
def cfg : TheoryConcrete := {one := 1, max_seq_t :=9}


def modelCheckerResult' :=(runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (detect_prop) (terminationC) cfg view).snd
-- #time #eval modelCheckerResult'.seen.size
def statesJson : Lean.Json := Lean.toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM cfg (collectTrace' modelCheckerResult'))
#eval statesJson
open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />



end EWD840
