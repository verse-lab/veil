-- import ProofWidgets.Component.GraphDisplay
import ProofWidgets.Component.HtmlDisplay
import Veil.Core.Tools.Checker.Concrete.DataStructure

import Lean

open Lean Elab Command Tactic Meta Term
open ProofWidgets Jsx

partial def buildSteps [BEq β] [Hashable β]
  (edges : Std.HashMap β (β × κ)) (cur : β)
  (acc : List (Step β κ) := []) : β × List (Step β κ) :=
  match edges.get? cur with
  | none => (cur, acc)
  | some (prev, label) =>
    buildSteps edges prev ({ label := label, next := cur } :: acc)


def collectTrace' [BEq β] [Repr β] [Hashable β] [Repr κ] (res : SearchContext α β κ)
: List (Trace β κ) := Id.run do
  let unsafeV := res.counterexample
  let edges := res.log
  let mut traces : List (Trace β κ) := []
  for badState in unsafeV do
    let (st₀, trace) := buildSteps edges badState
    let trace := { start := st₀, steps := trace }
    traces := traces ++ [trace]
  return traces
