import Veil.Core.Tools.Checker.Concrete.DataStructure
import Lean


partial def buildSteps [BEq σₕ] [Hashable σₕ]
  (edges : Std.HashMap σₕ (σₕ × κ)) (cur : σₕ)
  (acc : List (Step σₕ κ) := []) : σₕ × List (Step σₕ κ) :=
  match edges.get? cur with
  | none => (cur, acc)
  | some (prev, label) =>
    buildSteps edges prev ({ label := label, next := cur } :: acc)


-- def collectTrace' [BEq σₕ] [Hashable σₕ] (res : SearchContext σ κ σₕ )
def collectTrace' [BEq σₕ] [Hashable σₕ]
  (res : SearchContext σ κ σₕ init_states adj view)
: List (Trace σₕ κ) := Id.run do
  let unsafeV := res.counterexample
  let edges := res.log
  let mut traces : List (Trace σₕ κ) := []
  for badState in unsafeV do
    let (st₀, trace) := buildSteps edges badState
    let trace := { start := st₀, steps := trace }
    traces := traces ++ [trace]
  return traces


def collectTrace [BEq σₕ] [Hashable σₕ]
  (res : Option σₕ × Option (SearchContext σ κ σₕ init_states adj view))
: List (Trace σₕ κ) := Id.run do
  match res with
  | (none, some ctx) =>
    return collectTrace' ctx
  | (some st, none) =>
    return [{ start := st, steps := [] }]
  | _ => return []


def spaceSize [BEq σₕ] [Hashable σₕ]
  (res : Option σₕ × Option (SearchContext σ κ σₕ init_states adj view))
: Nat := Id.run do
  match res with
  | (none, some ctx) =>
    return ctx.seen.size
  | _ => return 0
