module

public import Veil

/-! # Non-crossing routes do not run the crossing

`.fair` and `.prune` must be at least 10x faster than `.crossing` on a formula with `2^16`
crossed disjuncts.
-/

open Veil Veil.LivenessMC Lean

/-- One state with a self-loop. -/
private def loopingSystem :
    EnumerableTransitionSystem Unit (List Unit) Nat (List Nat) Int Unit
      (Transitions Unit Int Nat) () := {
  initStates := [0]
  tr := fun _ n => { successes := [((), n)], failures := [] }
}

/-- Strong-fairness pairs in the assumption. -/
private def pairs : Nat := 16

/-- `□◇(atom i)`. -/
private def gf (i : Nat) : LTLLib.Formula Nat := .always (.eventually (.atom i))

/-- `(⋀ i < pairs, □◇a_2i → □◇a_2i+1) → □◇a_0`. -/
private def manyStrongPairs : LivenessProperty Unit Nat Unit := {
  name := `manyStrongPairs
  atoms := (List.range (2 * pairs)).map fun i =>
    .state { name := Name.mkSimple s!"a{i}", property := fun _ _ => True }
  φ := .implies
    ((List.range pairs).foldl
      (fun acc i => .and acc (.implies (gf (2 * i)) (gf (2 * i + 1)))) .tt)
    (gf 0)
}

/-- Wall clock of `checkRoute route` in nanoseconds, and its verdict. -/
private def timeRoute (route : Route) [RouteCertificate route loopingSystem] :
    IO (Nat × String) := do
  let t0 ← IO.monoNanosNow
  match checkRoute route loopingSystem manyStrongPairs with
  | .empty _ => return ((← IO.monoNanosNow) - t0, "empty")
  | .nonEmpty _ _ => return ((← IO.monoNanosNow) - t0, "nonEmpty")

#eval show IO Unit from do
  let (crossNs, crossVerdict) ← timeRoute .crossing
  let (fairNs, fairVerdict) ← timeRoute .fair
  let (pruneNs, pruneVerdict) ← timeRoute .prune

  unless fairVerdict == crossVerdict && pruneVerdict == crossVerdict do
    throw <| IO.userError s!"routes disagree: crossing {crossVerdict}, fair {fairVerdict}, \
      prune {pruneVerdict}"

  unless fairNs * 10 < crossNs do
    throw <| IO.userError s!"`.fair` took {fairNs}ns, `.crossing` {crossNs}ns"
  unless pruneNs * 10 < crossNs do
    throw <| IO.userError s!"`.prune` took {pruneNs}ns, `.crossing` {crossNs}ns"
