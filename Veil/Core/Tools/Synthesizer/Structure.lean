module

public meta import Veil.Core.Tools.Synthesizer.Clause

/-!
# Finite structures

This file defines the finite first-order structures UPDR reads out of solver models, evaluates
clauses in them, and computes their diagrams.

## Main definitions

* `Veil.Synthesizer.FinStructure`: a finite domain per sort and a table per symbol.
* `Veil.Synthesizer.FinStructure.models`: `m ⊨ c` for a universal clause `c`.
* `Veil.Synthesizer.FinStructure.diagramLiterals`: the diagram of a structure
  [Karbyshev et al., Def. 4.1].
* `Veil.Synthesizer.FinStructure.negatedDiagram`: the universal clause that excludes every
  structure containing a copy of `m` [Karbyshev et al., Lemma 4.3].

## Implementation notes

* The table of a function symbol is its graph, one row `args ++ [value]` per argument tuple.
  Its diagram therefore states one positive literal per row: `f ā ≠ b'` follows from `f ā = b`
  and `b ≠ b'`, a diagram literal for an uninterpreted result sort and an axiom of the enum class
  for an enum sort. A 0-ary function keeps one literal per element, positive or negative, so that
  generalization can keep `c = x` instead of `c ≠ y ∨ x = y`.
* An enum sort has a fixed carrier, its constructors. Diagrams name enum elements as constants and
  quantify over the uninterpreted sorts only.
* Numeric terms have values but no elements. The diagram states the value of every numeric term
  and the order between the terms of one sort.

## References

* A. Karbyshev, N. Bjørner, S. Itzhaky, N. Rinetzky, S. Shoham, *Property-Directed Inference of
  Universal Invariants or Proving Their Absence*, Journal of the ACM 64(1), 2017.
-/

public meta section

namespace Veil.Synthesizer
open Lean

/-- The element an argument denotes under an assignment of variables to elements. -/
def Arg.eval (asg : Array Nat) : Arg → Nat
  | .var v => asg[v]!
  | .enumConst _ i => i

/-- A finite first-order structure. The elements of sort `s` are `0, …, size s - 1`; element `i`
of an enum sort is its `i`-th constructor. -/
structure FinStructure where
  /-- The size of each sort. -/
  sorts : Array (SortName × Nat)
  /-- The enum sorts among `sorts`, each with its constructor names in order. -/
  enums : Array (SortName × Array Name) := #[]
  /-- The tuples on which each relation holds; for a function, the rows of its graph. -/
  rels : Array (Symbol × Array (Array Nat))
  /-- The value of each numeric symbol on each argument tuple. -/
  nums : Array (Symbol × Array (Array Nat × Int)) := #[]
deriving Repr, BEq, Inhabited

namespace FinStructure

variable (m : FinStructure)

/-- The number of elements of sort `s`. -/
def sortSize (s : SortName) : Nat := ((m.sorts.find? (·.1 == s)).map (·.2)).getD 0

/-- Whether `s` is an enum sort. -/
def isEnum (s : SortName) : Bool := m.enums.any (·.1 == s)

/-- The constructor that is element `i` of the enum sort `s`. -/
def enumCtor? (s : SortName) (i : Nat) : Option Name :=
  (m.enums.find? (·.1 == s)).bind fun (_, ctors) ↦ ctors[i]?

/-- The table of `sym`, if the structure interprets it. -/
def table? (sym : Symbol) : Option (Array (Array Nat)) := (m.rels.find? (·.1 == sym)).map (·.2)

/-- Whether `sym` holds on `tuple`. -/
def holds (sym : Symbol) (tuple : Array Nat) : Bool :=
  ((m.table? sym).map (·.contains tuple)).getD false

/-- All tuples of elements of the given sorts, in lexicographic order. -/
def tuples (argSorts : Array SortName) : Array (Array Nat) :=
  argSorts.foldl (init := #[#[]]) fun acc s ↦
    acc.flatMap fun t ↦ (Array.range (m.sortSize s)).map (t.push ·)

/-- The elements of the uninterpreted sorts, in a fixed order: the variables of the diagram. -/
def elements : Array (SortName × Nat) :=
  (m.sorts.filter fun (s, _) ↦ !m.isEnum s).flatMap fun (s, n) ↦ (Array.range n).map (s, ·)

/-- The numeric terms of the structure with their values: each numeric symbol applied to each
argument tuple of its table, the elements written through `argOf`. -/
def numTerms (argOf : SortName → Nat → Arg) : Array (NumTerm × Int) :=
  m.nums.flatMap fun (sym, table) ↦
    table.map fun (row, v) ↦ (⟨sym, (sym.argSorts.pop.zip row).map fun (s, i) ↦ argOf s i⟩, v)

/-- The value of a numeric term under an assignment. -/
def numValue (asg : Array Nat) (t : NumTerm) : Option Int := do
  let (_, table) ← m.nums.find? (·.1 == t.sym)
  let row := t.args.map (·.eval asg)
  (table.find? (·.1 == row)).map (·.2)

/-! ### Diagrams -/

/-- The argument naming element `i` of sort `s` in the diagram: a constructor, or the variable of
the element. -/
def diagramArg (s : SortName) (i : Nat) : Arg :=
  match m.enumCtor? s i with
  | some ctor => .enumConst ctor i
  | none =>
    match m.elements.findIdx? (· == (s, i)) with
    | some v => .var v
    | none => panic! s!"IC3: element {i} of sort {s} is not an element of the structure"

/-- The literals of the diagram that describe the tables of the relations and functions. -/
def tableLiterals : Array Literal :=
  m.rels.flatMap fun (sym, table) ↦
    let atom (t : Array Nat) : Atom :=
      .rel sym ((sym.argSorts.zip t).map fun (s, i) ↦ m.diagramArg s i)
    if sym.isFunction && sym.argSorts.size > 1 then table.map ({ positive := true, atom := atom · })
    else (m.tuples sym.argSorts).map fun t ↦ { positive := m.holds sym t, atom := atom t }

/-- The literals `xᵢ ≠ xⱼ` for distinct elements of one uninterpreted sort. -/
def distinctLiterals : Array Literal := Id.run do
  let els := m.elements
  let mut lits := #[]
  for i in [:els.size] do
    for j in [i+1:els.size] do
      if els[i]!.1 == els[j]!.1 then lits := lits.push { positive := false, atom := .eq i j }
  return lits

/-- The literals of the diagram about numeric terms: the value of each term, and the order between
consecutive terms of one sort sorted by value, `<` or, for equal values, `=`. -/
def numericLiterals : Array Literal := Id.run do
  let terms := m.numTerms m.diagramArg
  let mut lits := terms.map fun (t, v) ↦ { positive := true, atom := .numEq t v }
  for s in (terms.map (·.1.sort)).toList.eraseDups do
    let ts := (terms.filter (·.1.sort == s)).qsort fun a b ↦ a.2 < b.2
    for i in [1:ts.size] do
      let (t₁, v₁) := ts[i-1]!
      let (t₂, v₂) := ts[i]!
      let a := if v₁ == v₂ then Atom.numEqOffset t₁ t₂ 0 else Atom.numLt t₁ t₂
      lits := lits.push { positive := true, atom := a }
  return lits

/-- The diagram of `m` [Karbyshev et al., Def. 4.1], as the body of an existential sentence over
the variables `0, …, |elements| - 1`, one per element of an uninterpreted sort. -/
def diagramLiterals : Array Literal := m.tableLiterals ++ m.distinctLiterals ++ m.numericLiterals

/-- The universal clause `¬ Diag(m)`, false exactly in the structures containing a copy of `m`. -/
def negatedDiagram : Clause :=
  { vars := m.elements.map (·.1), lits := m.diagramLiterals.map Literal.negate }

/-! ### Evaluation -/

/-- The truth value of a literal under an assignment, or `none` when the structure lacks a symbol
or a table row the literal needs. -/
def evalLiteral (asg : Array Nat) (l : Literal) : Option Bool := do
  let v ← match l.atom with
    | .rel sym args => (m.table? sym).map (·.contains (args.map (·.eval asg)))
    | .eq a b => some (asg[a]! == asg[b]!)
    | .lin terms c isEq =>
      (terms.foldlM (init := c) fun acc (k, t) ↦ (m.numValue asg t).map (acc + k * ·)).map
        fun sum ↦ if isEq then sum == 0 else sum ≤ 0
  return if l.positive then v else !v

/-- Search the assignments of elements to `vars`, one variable at a time. After `i` variables
are assigned, `settle` sees the literals of width `i` and may decide the subtree; a complete
assignment that nothing decided answers `atLeaf`. The search asks whether every subtree answers
`true` when `universal`, and whether some subtree does otherwise. -/
def searchAssignments (vars : Array SortName) (lits : Array Literal)
    (settle : Array Nat → Array Literal → Option Bool) (atLeaf universal : Bool) : Bool :=
  let byWidth := lits.foldl (init := Array.replicate (vars.size + 1) #[]) fun acc l ↦
    acc.modify (min l.width vars.size) (·.push l)
  go byWidth 0 #[]
where
  /-- The answer for the assignments extending `asg`, which assigns the first `i` variables. -/
  go (byWidth : Array (Array Literal)) (i : Nat) (asg : Array Nat) : Bool :=
    match settle asg byWidth[i]! with
    | some b => b
    | none =>
      if h : i < vars.size then
        let els := Array.range (m.sortSize vars[i])
        if universal then els.all (go byWidth (i + 1) <| asg.push ·)
        else els.any (go byWidth (i + 1) <| asg.push ·)
      else atLeaf
  termination_by vars.size - i

/-- `m ⊨ c`: every assignment satisfies some literal of `c`. A literal the structure does not
determine counts as satisfied, so that a structure lacking a value rejects no clause. -/
def models (c : Clause) : Bool :=
  m.searchAssignments c.vars c.lits (atLeaf := false) (universal := true) fun asg ls ↦
    if ls.any fun l ↦ (m.evalLiteral asg l).getD true then some true else none

/-- `m ⊨ ∃ vars, ⋀ lits`. A literal the structure does not determine counts as unsatisfied. -/
def modelsExistential (vars : Array SortName) (lits : Array Literal) : Bool :=
  m.searchAssignments vars lits (atLeaf := true) (universal := false) fun asg ls ↦
    if ls.any fun l ↦ !(m.evalLiteral asg l).getD false then some false else none

end FinStructure

end Veil.Synthesizer
