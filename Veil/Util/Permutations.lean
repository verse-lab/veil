module

/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Adapted from Mathlib.Data.List.Defs (authors: Parikshit Khanna, Jeremy Avigad,
Leonardo de Moura, Floris van Doorn, Mario Carneiro).
-/
public import Lean
public meta import Lean

@[expose] public section

namespace Veil.List

private def permutationsAux2 (t : α) (ts : List α) (r : List β) :
    List α → (List α → β) → List α × List β
  | [], _ => (ts, r)
  | y :: ys, f =>
    let (us, zs) := permutationsAux2 t ts r ys (fun x => f (y :: x))
    (y :: us, f (t :: y :: us) :: zs)

private def permutationsAux : (ts is : List α) → List (List α)
  | [], _ => []
  | t :: ts, is =>
    List.foldr (fun y r => (permutationsAux2 t ts r y id).2)
      (permutationsAux ts (t :: is)) (is :: permutationsAux is [])
termination_by ts is => (ts.length + is.length, ts.length)
decreasing_by all_goals (simp_wf; omega)

/-- All permutations, retaining the previous mathlib candidate order and duplicates. -/
@[no_expose] def permutations (l : List α) : List (List α) := l :: permutationsAux l []

end Veil.List
