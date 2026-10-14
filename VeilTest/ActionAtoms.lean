module

public import Veil
public import Veil.Core.Tools.LivenessMC.LivenessMC
public meta import Veil.Core.Tools.LivenessMC.LivenessMC

/-! Edge and enabled atoms: `E(a)` is a state atom (some instantiation of `a` can fire here) and `T(a)` is
an edge atom (the step taken here is an instantiation of `a`). Both are decided against the action *label*,
so they need no ghost state. -/

veil module ActionAtoms

individual n : Nat

#gen_state

after_init { n := 0 }

-- `up` is enabled only below 2, `reset` only at 2, so the system cycles 0 → 1 → 2 → 0.
action up {
  require n < 2
  n := n + 1
}

action reset {
  require n = 2
  n := 0
}

-- `up` can always eventually fire, and does.
temporal (only := check) [upRecurs] □ ◇ E(up)
temporal (only := check) [upTaken] □ ◇ T(up)
-- `reset` is not always enabled, so this one must fail.
temporal (only := check) [resetAlways] □ E(reset)
-- Per-action strong fairness, the motivating shape: whenever `reset` is enabled it is eventually taken.
-- Its negation puts the edge atom `¬T(reset)` inside a `◇□`, which is what the step regions exist for.
temporal (only := check) [resetFair] □ (E(reset) → ◇ T(reset))
-- A step cannot be two different actions at once.
temporal (only := check) [notBoth] □ ¬(T(up) ∧ T(reset))

#gen_spec
#gen_executable

open Veil.LivenessMC in
#eval do
  let sys := enumerableTransitionSystem {}
  let expect (nm : String) (want : Bool)
      (r : LTLLib.EmptinessResult (State FieldConcreteType × LTLLib.TBAState)) : IO Unit := do
    let got := match r with | .empty _ => true | .nonEmpty _ _ => false
    if got == want then IO.println s!"  ok    {nm}"
    else IO.println s!"  FAIL  {nm}: expected {if want then "holds" else "fails"}"
  IO.println "action atoms (labelled NDFS route):"
  expect "□◇E(up)"                true
    (checkNDFS sys (upRecurs.ast Theory (State FieldConcreteType) FieldConcreteType) (by native_decide) (by native_decide))
  expect "□◇T(up)"                true
    (checkNDFS sys (upTaken.ast Theory (State FieldConcreteType) FieldConcreteType) (by native_decide) (by native_decide))
  expect "□E(reset)"              false
    (checkNDFS sys (resetAlways.ast Theory (State FieldConcreteType) FieldConcreteType) (by native_decide) (by native_decide))
  expect "□(E(reset) → ◇T(reset))" true
    (checkNDFS sys (resetFair.ast Theory (State FieldConcreteType) FieldConcreteType) (by native_decide) (by native_decide))
  expect "□¬(T(up) ∧ T(reset))"   true
    (checkNDFS sys (notBoth.ast Theory (State FieldConcreteType) FieldConcreteType) (by native_decide) (by native_decide))

open Veil.LivenessMC in
#eval do
  let sys := enumerableTransitionSystem {}
  let expect (nm : String) (want : Bool)
      (r : LTLLib.EmptinessResult ((State FieldConcreteType × Nat) × Bool)) : IO Unit := do
    let got := match r with | .empty _ => true | .nonEmpty _ _ => false
    if got == want then IO.println s!"  ok    {nm}"
    else IO.println s!"  FAIL  {nm}: expected {if want then "holds" else "fails"}"
  -- The same properties on the *fairness* route, which hoists and must agree. Before the entry points
  -- were lifted this route took an unlabelled successor function, so every `T(…)` would have read false.
  IO.println "action atoms (fairness route agrees):"
  expect "□◇T(up)"                true
    (checkUnderFairness sys (upTaken.ast Theory (State FieldConcreteType) FieldConcreteType))
  expect "□(E(reset) → ◇T(reset))" true
    (checkUnderFairness sys (resetFair.ast Theory (State FieldConcreteType) FieldConcreteType))
  expect "□¬(T(up) ∧ T(reset))"   true
    (checkUnderFairness sys (notBoth.ast Theory (State FieldConcreteType) FieldConcreteType))

end ActionAtoms

/-! ## Parallel edges

`toggle1` and `toggle2` have the same effect and are both always enabled, so every endpoint pair `(s, t)`
is realized by two steps reading *different* letters.
It is what separates an edge atom from any encoding that attaches atoms to states or to endpoint pairs:
under such an encoding `T(toggle1)` and `T(toggle2)` would be indistinguishable on `(0, 1)`, and
`□◇T(toggle1)` would wrongly come out true. -/

veil module ParallelEdges

individual bit : Nat

#gen_state

after_init { bit := 0 }

-- Nat subtraction: 1 - 0 = 1 and 1 - 1 = 0, so both actions toggle, and both are always enabled.
action toggle1 { bit := 1 - bit }
action toggle2 { bit := 1 - bit }

-- FAILS: the run that always takes `toggle2` never takes `toggle1`.
temporal (only := check) [t1Recurs] □ ◇ T(toggle1)
-- FAILS, for the same reason.
temporal (only := check) [t1Forever] ◇ □ T(toggle1)
-- HOLDS: every step is one of the two.
temporal (only := check) [eitherStep] □ (T(toggle1) ∨ T(toggle2))
-- HOLDS: a step is exactly one action.
temporal (only := check) [notBothPar] □ ¬(T(toggle1) ∧ T(toggle2))

#gen_spec
#gen_executable

open Veil.LivenessMC in
#eval do
  let sys := enumerableTransitionSystem {}
  let expect (nm : String) (want : Bool)
      (r : LTLLib.EmptinessResult (State FieldConcreteType × LTLLib.TBAState)) : IO Unit := do
    let got := match r with | .empty _ => true | .nonEmpty _ _ => false
    if got == want then IO.println s!"  ok    {nm}"
    else IO.println s!"  FAIL  {nm}: expected {if want then "holds" else "fails"}"
  IO.println "parallel edges (the §6.3 discriminator):"
  expect "□◇T(toggle1)"                false
    (checkNDFS sys (t1Recurs.ast Theory (State FieldConcreteType) FieldConcreteType)
      (by native_decide) (by native_decide))
  expect "◇□T(toggle1)"                false
    (checkNDFS sys (t1Forever.ast Theory (State FieldConcreteType) FieldConcreteType)
      (by native_decide) (by native_decide))
  expect "□(T(toggle1) ∨ T(toggle2))"  true
    (checkNDFS sys (eitherStep.ast Theory (State FieldConcreteType) FieldConcreteType)
      (by native_decide) (by native_decide))
  expect "□¬(T(toggle1) ∧ T(toggle2))" true
    (checkNDFS sys (notBothPar.ast Theory (State FieldConcreteType) FieldConcreteType)
      (by native_decide) (by native_decide))

open Veil.LivenessMC in
#eval do
  let sys := enumerableTransitionSystem {}
  let expect (nm : String) (want : Bool)
      (r : LTLLib.EmptinessResult ((State FieldConcreteType × Nat) × Bool)) : IO Unit := do
    let got := match r with | .empty _ => true | .nonEmpty _ _ => false
    if got == want then IO.println s!"  ok    {nm}"
    else IO.println s!"  FAIL  {nm}: expected {if want then "holds" else "fails"}"
  -- `◇□T(toggle1)` is the region case: negated it is `□◇¬T(toggle1)`, and the fairness route decides the
  -- region on the letter each *step* reads. On this module every endpoint pair carries both letters, so
  -- an encoding that read the region off the pair would answer differently.
  IO.println "parallel edges (fairness route agrees):"
  expect "□◇T(toggle1)"                false
    (checkUnderFairness sys (t1Recurs.ast Theory (State FieldConcreteType) FieldConcreteType))
  expect "◇□T(toggle1)"                false
    (checkUnderFairness sys (t1Forever.ast Theory (State FieldConcreteType) FieldConcreteType))
  expect "□(T(toggle1) ∨ T(toggle2))"  true
    (checkUnderFairness sys (eitherStep.ast Theory (State FieldConcreteType) FieldConcreteType))
  expect "□¬(T(toggle1) ∧ T(toggle2))" true
    (checkUnderFairness sys (notBothPar.ast Theory (State FieldConcreteType) FieldConcreteType))

end ParallelEdges

/-! ## An edge atom inside a hoisted fairness

`work` and `idle` are both always enabled and `idle` is a no-op, so the run that always idles never sets the flag.
The property only holds once `work` is assumed to be taken.
Writing that assumption needs `T(work)`, and hoisting it needs the fairness routes to read letters off
steps. `sfWork` is per-action strong fairness written as a property, whose negation is
`□◇E(work) ∧ ◇□¬T(work)` (an edge atom inside a `◇□` region). -/

veil module FairnessEdgeAtoms

individual flag : Nat

#gen_state

after_init { flag := 0 }

action work { flag := 1 }
action idle { flag := flag }

-- FAILS: the always-idle run never sets the flag.
temporal [reaches] ◇ ⌜ flag = 1 ⌝
-- HOLDS: `T(work)` taken infinitely often forces it. The assumption is a hoisted `□◇` over an edge atom.
temporal (only := check) [reachesFair] (□ ◇ T(work)) → ◇ ⌜ flag = 1 ⌝
-- FAILS: `work` is always enabled and the always-idle run never takes it.
temporal (only := check) [sfWork] (□ ◇ E(work)) → (□ ◇ T(work))
-- HOLDS: the same strong fairness as an assumption. It is a disjunction of two fair disjuncts, so it is
-- hoisted whole and crossed, one with the edge atom in a `◇□` region.
temporal (only := check) [sfForces] ((□ ◇ E(work)) → (□ ◇ T(work))) → ◇ ⌜ flag = 1 ⌝
-- The two cases that *discriminate*. Every property above has an edge atom only in its assumption, so an
-- implementation that never contributed `T(…)` would make the assumption unsatisfiable and the implication
-- vacuously true — the same answer, for the wrong reason. These two assume something the idle run does
-- satisfy, so they must FAIL, and a broken `T(…)` would report them as holding.
-- FAILS: the always-idle run takes `idle` infinitely often and never sets the flag. (`□◇`, a mark.)
temporal (only := check) [idleRecurs] (□ ◇ T(idle)) → ◇ ⌜ flag = 1 ⌝
-- FAILS: the same run takes `idle` forever. (`◇□`, a step region — the §6.5 case.)
temporal (only := check) [idleForever] (◇ □ T(idle)) → ◇ ⌜ flag = 1 ⌝

#gen_spec
#gen_executable

open Veil.LivenessMC in
#eval do
  let sys := enumerableTransitionSystem {}
  let expect (nm : String) (want : Bool)
      (r : LTLLib.EmptinessResult ((State FieldConcreteType × Nat) × Bool)) : IO Unit := do
    let got := match r with | .empty _ => true | .nonEmpty _ _ => false
    if got == want then IO.println s!"  ok    {nm}"
    else IO.println s!"  FAIL  {nm}: expected {if want then "holds" else "fails"}"
  IO.println "edge atoms inside a hoisted fairness:"
  expect "◇flag=1"                          false
    (checkUnderFairness sys (reaches.ast Theory (State FieldConcreteType) FieldConcreteType))
  expect "□◇T(work) → ◇flag=1"              true
    (checkUnderFairness sys (reachesFair.ast Theory (State FieldConcreteType) FieldConcreteType))
  expect "□◇E(work) → □◇T(work)"            false
    (checkUnderFairness sys (sfWork.ast Theory (State FieldConcreteType) FieldConcreteType))
  expect "SF(work) → ◇flag=1"               true
    (checkUnderFairness sys (sfForces.ast Theory (State FieldConcreteType) FieldConcreteType))
  expect "□◇T(idle) → ◇flag=1"              false
    (checkUnderFairness sys (idleRecurs.ast Theory (State FieldConcreteType) FieldConcreteType))
  expect "◇□T(idle) → ◇flag=1"              false
    (checkUnderFairness sys (idleForever.ast Theory (State FieldConcreteType) FieldConcreteType))

/-! ### Which properties get the prune's free path

The prune is the default and fastest route and it takes **no side condition**:
it routes a property whose hoisted regions mention an edge atom to the crossing, so `checkFair` is
unconditional in the property and an edge atom under `◇□` is handled.
-/

open Veil.LivenessMC in
#eval do
  let route (nm : String) (want : Bool) (got : Bool) : IO Unit := do
    if got == want then IO.println s!"  ok    {nm}  →  {if got then "free" else "one prune level"}"
    else IO.println s!"  FAIL  {nm}: expected {if want then "free" else "one prune level"}"
  IO.println "prune cost (§12.3: `□◇T(a)` is free, `◇□T(a)` commits a region first):"
  route "◇flag=1                  (no fairness)        " true
    (pruneRegionsAvoidEdgeAtoms (reaches.ast Theory (State FieldConcreteType) FieldConcreteType))
  route "□◇T(work) → ◇flag=1      (edge atom assumed)  " true
    (pruneRegionsAvoidEdgeAtoms (reachesFair.ast Theory (State FieldConcreteType) FieldConcreteType))
  route "SF(work) → ◇flag=1       (SF assumed)         " true
    (pruneRegionsAvoidEdgeAtoms (sfForces.ast Theory (State FieldConcreteType) FieldConcreteType))
  route "□◇T(idle) → ◇flag=1      (edge atom assumed)  " true
    (pruneRegionsAvoidEdgeAtoms (idleRecurs.ast Theory (State FieldConcreteType) FieldConcreteType))
  route "□◇E(work) → □◇T(work)    (SF verified)        " false
    (pruneRegionsAvoidEdgeAtoms (sfWork.ast Theory (State FieldConcreteType) FieldConcreteType))
  route "◇□T(idle) → ◇flag=1      (◇□ over an edge atom)" false
    (pruneRegionsAvoidEdgeAtoms (idleForever.ast Theory (State FieldConcreteType) FieldConcreteType))

open Veil.LivenessMC in
#eval do
  let sys := enumerableTransitionSystem {}
  let expect (nm : String) (want : Bool) (r : LTLLib.EmptinessResult (State FieldConcreteType × Nat)) :
      IO Unit := do
    let got := match r with | .empty _ => true | .nonEmpty _ _ => false
    if got == want then IO.println s!"  ok    {nm}"
    else IO.println s!"  FAIL  {nm}: expected {if want then "holds" else "fails"}"
  -- the prune route, which takes no side condition: it decides the jointness of its hoisted regions
  -- rather than assuming it (`EdgeLabels.md` §14), so an edge atom in a `◇□` is its business, not the
  -- caller's. These agree with the crossing above.
  IO.println "the prune route, on every property, with no side condition:"
  expect "◇flag=1"                          false
    (checkFair sys (reaches.ast Theory (State FieldConcreteType) FieldConcreteType))
  expect "□◇T(work) → ◇flag=1"              true
    (checkFair sys (reachesFair.ast Theory (State FieldConcreteType) FieldConcreteType))
  expect "SF(work) → ◇flag=1"               true
    (checkFair sys (sfForces.ast Theory (State FieldConcreteType) FieldConcreteType))
  expect "□◇T(idle) → ◇flag=1"              false
    (checkFair sys (idleRecurs.ast Theory (State FieldConcreteType) FieldConcreteType))

end FairnessEdgeAtoms
