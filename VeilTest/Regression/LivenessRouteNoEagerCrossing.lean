module

public import Veil

/-! # A non-crossing route must not build the crossing

Regression test for a bug measured on 2026-10-10. `checkRoute` bound the crossing in a `let`
*before* its `match`:

```
let crossing := projectStates (fun q => q.1.1) (modelCheckFairFNFCrossOfStep p.φ init step)
match route, cert.cert with
  ...
  | .fair, _ => projectStates Prod.fst (checkFair sys p)
```

Three branches use `crossing` -- `.crossing`, and the fallbacks of `.patOnly`/`.prune` -- but the
compiler evaluated it on **every** route, so each route silently paid a full `2^n` crossing on top
of its own search. It was not benchmark-only: `checkRoute` is what `#liveness_check (route := …)`
dispatches through, so every non-default route paid it.

Measured on `ltl-bench`'s `sfHub` family, where size `n` contributes `n` strong-fairness pairs and
hence `2^n` crossed disjuncts:

| row | expected | with the bug |
|---|---|---|
| n=12 `Goal` `fair` | 0.54 ms | 2342 ms (= the crossing's 2326 ms + 0.54 ms) |
| n=22 `Goal` `fair` | 1.27 ms | **timeout, >600 s** -- the crossing times out there |

Confirmed before the fix by the prediction `new = old(crossing) + old(route)`, which held on 208 of
241 measured rows within 25%.

## How this test detects it

The assertion is **relative, never absolute**: a formula is built whose crossing is exponentially
larger than its prune, and the test requires the prune routes to be at least an order of magnitude
faster than `.crossing` on the very same query. With the bug, every route costs
`crossing + itself`, so the ratio collapses to ~1 and the test fails. Without it the ratio is in
the hundreds.

Relative rather than absolute because an absolute millisecond bound is a machine-specific
tripwire -- `ltl-bench`'s own notes record several measurements that had to be discarded for having
been taken on a loaded machine. A ratio needs no such assumption: both numbers come from the same
machine, moments apart.
-/

open Veil Veil.LivenessMC Lean

/-- One state that loops forever. The state space is deliberately trivial: the crossing's cost here
comes from the **formula** (`2^pairs` disjuncts, each checked on a tiny product), not from the
search, which is what makes the two routes differ by orders of magnitude on identical input. -/
private def loopingSystem :
    EnumerableTransitionSystem Unit (List Unit) Nat (List Nat) Int Unit
      (Transitions Unit Int Nat) () := {
  initStates := [0]
  tr := fun _ n => { successes := [((), n)], failures := [] }
}

/-- Strong-fairness pairs in the assumption. The crossing is `2^pairs` emptiness checks, so this
is the knob that separates the routes; 16 keeps the crossing well under a second while leaving a
ratio of hundreds. -/
private def pairs : Nat := 16

/-- `□◇(atom i)`. -/
private def gf (i : Nat) : LTLLib.Formula Nat := .always (.eventually (.atom i))

/-- `(⋀ i < pairs, □◇a_2i → □◇a_2i+1) → □◇a_0`.

Every atom is the same predicate, but they are **distinct atom indices**, so the fair normal form
cannot collapse them and the crossing really does enumerate `2^pairs` disjuncts. That is the point:
the cost under test is the crossing's, not the model's. -/
private def manyStrongPairs : LivenessProperty Unit Nat Unit := {
  name := `manyStrongPairs
  atoms := (List.range (2 * pairs)).map fun i =>
    .state { name := Name.mkSimple s!"a{i}", property := fun _ _ => True }
  φ := .implies
    ((List.range pairs).foldl
      (fun acc i => .and acc (.implies (gf (2 * i)) (gf (2 * i + 1)))) .tt)
    (gf 0)
}

/-- Wall-clock of one `checkRoute`, forced to completion by matching on the result. `checkRoute` is
a pure function, so the clock has to straddle something that demands it. -/
private def timeRoute (route : Route) [RouteCertificate route loopingSystem] :
    IO (Nat × String) := do
  let t0 ← IO.monoNanosNow
  -- Matching on the call directly, with the second clock read inside each branch, is how
  -- `LivenessMC/Runtime.lean` times the search itself. A `let` would not do: `checkRoute` is pure,
  -- so only a pattern match that drives control flow is guaranteed to demand it -- and relying on
  -- a `let` being evaluated when expected is precisely the mistake this test exists to catch.
  match checkRoute route loopingSystem manyStrongPairs with
  | .empty _ => return ((← IO.monoNanosNow) - t0, "empty")
  | .nonEmpty _ _ => return ((← IO.monoNanosNow) - t0, "nonEmpty")

-- `.fair` and `.prune` must each be far cheaper than `.crossing` on the same query. With the eager
-- `let` they are all `crossing + route` and the ratios collapse to ~1.
#eval show IO Unit from do
  let (crossNs, crossVerdict) ← timeRoute .crossing
  let (fairNs, fairVerdict) ← timeRoute .fair
  let (pruneNs, pruneVerdict) ← timeRoute .prune

  -- Same question, so the same answer, whichever route decides it.
  unless fairVerdict == crossVerdict && pruneVerdict == crossVerdict do
    throw <| IO.userError s!"routes disagree: crossing {crossVerdict}, fair {fairVerdict}, \
      prune {pruneVerdict}"

  -- A margin of 10x against a real ratio in the hundreds: large enough that scheduler noise or a
  -- busy machine cannot trip it, small enough that re-introducing the eager crossing cannot pass.
  unless fairNs * 10 < crossNs do
    throw <| IO.userError s!"`.fair` cost {fairNs}ns against `.crossing`'s {crossNs}ns -- \
      under 10x apart, so `.fair` is paying for a crossing it never uses. See the module docstring: \
      `checkRoute` must not evaluate the crossing outside the branches that return it."
  unless pruneNs * 10 < crossNs do
    throw <| IO.userError s!"`.prune` cost {pruneNs}ns against `.crossing`'s {crossNs}ns -- \
      under 10x apart, so `.prune` is paying for a crossing it never uses."
