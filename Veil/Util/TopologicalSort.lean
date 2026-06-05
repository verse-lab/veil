import Lean

open Lean Std

namespace Veil

/-- Topologically sort `nodes` using `dependencies`, preserving the input order
among currently-ready nodes. Dependencies not present in `nodes` are ignored.
If the selected graph contains a cycle, append the remaining nodes in input
order instead of looping forever. -/
def topologicalSort [BEq α] [Hashable α] (nodes : List α)
    (dependencies : α → List α) : Array α := Id.run do
  let nodeSet := nodes.foldl (fun acc node => acc.insert node) (HashSet.emptyWithCapacity nodes.length)
  let hasPendingDependency (remaining : HashSet α) (node : α) : Bool := Id.run do
    let mut found := false
    for dependency in dependencies node do
      if nodeSet.contains dependency && remaining.contains dependency then
        found := true
    return found
  let mut remaining := nodeSet
  let mut order := #[]
  while !remaining.isEmpty do
    let ready := nodes.filter fun node =>
      remaining.contains node && !hasPendingDependency remaining node
    match ready with
    | [] =>
      for node in nodes do
        if remaining.contains node then
          order := order.push node
      remaining := {}
    | node :: _ =>
      remaining := remaining.erase node
      order := order.push node
  order

end Veil
