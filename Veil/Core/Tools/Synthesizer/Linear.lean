module

public meta import Veil.Core.Tools.Synthesizer.Structure

/-!
# Linear templates

Generalizing a counterexample by dropping literals of its negated diagram yields clauses about the
values the counterexample happened to have, never a relation between counters such as
`buffered + consumed = produced`. This file proposes such relations as candidate clauses.

## Main definitions

* `Veil.Synthesizer.Linear.templateAtoms`: the template atoms over a set of numeric terms.
* `Veil.Synthesizer.Linear.candidates`: the ground clauses a counterexample violates and every
  known reachable state satisfies, unguarded or guarded by one fact of the counterexample.

## Implementation notes

The search checks every candidate for initiation and consecution like any other clause, so a
candidate can cost time but not soundness.
-/

public meta section

namespace Veil.Synthesizer.Linear
open Lean

/-- The numeric terms of a structure without arguments, with their values. -/
def groundTerms (m : FinStructure) : Array (NumTerm × Int) :=
  m.nums.filterMap fun (sym, table) ↦
    if sym.argSorts.size == 1 then (table.find? (·.1.isEmpty)).map fun (_, v) ↦ (⟨sym, #[]⟩, v)
    else none

/-- The facts of `m` about the 0-ary components of the module that are not numeric: whether each
`Bool` individual holds, and the value of each enum-valued individual. -/
def guardLiterals (m : FinStructure) : Array Literal :=
  m.rels.flatMap fun (sym, table) ↦
    if sym.origin != .component || sym.arity != 0 then #[]
    else if !sym.isFunction then #[{ positive := m.holds sym #[], atom := .rel sym #[] }]
    else
      match table[0]?.bind (·[0]?) |>.bind fun i ↦ (m.enumCtor? sym.argSorts[0]! i).map (·, i) with
      | some (ctor, i) => #[{ positive := true, atom := .rel sym #[.enumConst ctor i] }]
      | none => #[]

/-- The template atoms over `terms`, all of one sort, with the constants `cs`, in the order to try
them: the equalities `x + y = z`, `x = y` and `x = y + c`, then `x ≤ y`, the bounds `c ≤ x` and
`x ≤ c`, `x ≤ y + c`, `x + y ≤ z` and `z ≤ x + y`. Smaller constants come first. -/
def templateAtoms (terms : Array NumTerm) (cs : Array Int) : Array Atom := Id.run do
  let cs := cs.qsort (fun a b ↦ a.natAbs < b.natAbs)
  let nonzero := cs.filter (· != 0)
  let n := terms.size
  let mut out : Array Atom := #[]
  for i in [:n] do
    for j in [i+1:n] do
      for k in [:n] do
        if k != i && k != j then out := out.push (.numSumEq terms[i]! terms[j]! terms[k]!)
  for i in [:n] do
    for j in [i+1:n] do
      out := out.push (.numEqOffset terms[i]! terms[j]! 0)
  for c in nonzero do
    for i in [:n] do
      for j in [:n] do
        if i != j then out := out.push (.numEqOffset terms[i]! terms[j]! c)
  for i in [:n] do
    for j in [:n] do
      if i != j then out := out.push (.numLeOffset terms[i]! terms[j]! 0)
  for c in cs do
    for t in terms do
      out := out.push (.numGe t c)
      out := out.push (.numLe t c)
  for c in nonzero do
    for i in [:n] do
      for j in [:n] do
        if i != j then out := out.push (.numLeOffset terms[i]! terms[j]! c)
  for i in [:n] do
    for j in [i+1:n] do
      for k in [:n] do
        if k != i && k != j then
          out := out.push (.numSumLe terms[i]! terms[j]! terms[k]!)
          out := out.push (.numLeSum terms[k]! terms[i]! terms[j]!)
  return out

/-- The candidate clauses for blocking `m`: ground template clauses over the numeric individuals
of `m` that `m` violates and every structure of `samples` satisfies, first unguarded, then
guarded by one fact of `guardLiterals m`. The constants are `numerals`, `0` and `1`. -/
def candidates (m : FinStructure) (numerals : Array Int) (samples : Array FinStructure := #[]) :
    Array Clause := Id.run do
  let cs := (#[0, 1] ++ numerals).toList.eraseDups.toArray
  let ground := groundTerms m
  let atoms := (ground.map (·.1.sort)).toList.eraseDups.toArray.flatMap fun s ↦
    templateAtoms ((ground.filter (·.1.sort == s)).map (·.1)) cs
  let guards := guardLiterals m
  let positive (a : Atom) : Literal := { positive := true, atom := a }
  let unguarded := atoms.map fun a ↦ ({ vars := #[], lits := #[positive a] } : Clause)
  let guarded := atoms.flatMap fun a ↦
    guards.map fun g ↦ ({ vars := #[], lits := #[g.negate, positive a] } : Clause)
  let mut out := #[]
  for c in unguarded ++ guarded do
    if !m.models c && samples.all (·.models c) && !out.contains c then out := out.push c
  return out

end Veil.Synthesizer.Linear
