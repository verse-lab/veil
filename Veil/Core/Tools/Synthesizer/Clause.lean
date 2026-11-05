module

public meta import Lean

/-!
# Universal clauses

This file defines the formulas UPDR builds invariants from: universal clauses over a first-order
vocabulary, and the operations the search needs on them.

## Main definitions

* `Veil.Synthesizer.Symbol`: a relation or function symbol of the vocabulary.
* `Veil.Synthesizer.Atom`, `Veil.Synthesizer.Literal`: atomic formulas and their negations.
* `Veil.Synthesizer.Clause`: a universal clause `∀ x̄, l₁ ∨ … ∨ lₙ`.
* `Veil.Synthesizer.Clause.subsumes`: subsumption up to a renaming of variables.
* `Veil.Synthesizer.Clause.restrict`: the clause on a subset of its literals.

## Implementation notes

* A function symbol `f : s₁ → … → sₙ → t` is read through its graph: a symbol with argument
  sorts `s₁ … sₙ t` whose atom `f a₁ … aₙ b` means `f a₁ … aₙ = b`. An individual of a sort is
  the 0-ary case.
* A clause names no element of an uninterpreted sort, only bound variables, so that the negation
  of a diagram is a universal statement about every state. The constructors of an enum sort are
  constants of the vocabulary and may be named (`Arg.enumConst`).
* `Int` and `Nat` have no clause variables. Atoms over them are linear constraints between
  numeric terms (`Atom.lin`), as in Ivy.
-/

public meta section

namespace Veil.Synthesizer
open Lean

/-- A sort parameter of the module, by name. -/
abbrev SortName := Name

/-- Whether `s` is one of the numeric sorts `Int` and `Nat`. -/
def isNumericSort (s : SortName) : Bool := s == `Int || s == `Nat

/-- Where a symbol of the vocabulary is declared. -/
inductive Origin where
  /-- A relation, individual or function of the module. -/
  | component
  /-- A field of the typeclass instance `inst`. -/
  | field (inst : Name)
deriving Repr, BEq, Hashable, Inhabited

/-- A relation or function symbol with its argument sorts. The last argument sort of a function
symbol is its result sort. -/
structure Symbol where
  /-- The declared name: a component name, or the field name of a class. -/
  name : Name
  /-- Where the symbol is declared. -/
  origin : Origin := .component
  /-- Whether the symbol is a function read through its graph. -/
  isFunction : Bool := false
  /-- The argument sorts, followed by the result sort for a function. -/
  argSorts : Array SortName
deriving Repr, BEq, Hashable, Inhabited

namespace Symbol

/-- The name the symbol is written with: `leader`, or `tot.le` for a class field. -/
def key (f : Symbol) : Name :=
  match f.origin with
  | .component => f.name
  | .field inst => inst ++ f.name

/-- The instance a class field belongs to. -/
def inst? (f : Symbol) : Option Name :=
  match f.origin with
  | .component => none
  | .field inst => some inst

/-- The number of arguments, not counting the result of a function. -/
def arity (f : Symbol) : Nat := if f.isFunction then f.argSorts.size - 1 else f.argSorts.size

/-- Whether the symbol is a function into `Int` or `Nat`. -/
def isNumeric (f : Symbol) : Bool := f.isFunction && (f.argSorts.back?.map isNumericSort).getD false

end Symbol

/-- A bound variable of a clause, by index into `Clause.vars`. -/
abbrev Var := Nat

/-- An argument of an atom: a variable, or the constructor of an enum sort at position `idx` of
its declaration, which is its element index in every structure. -/
inductive Arg where
  | var (v : Var)
  | enumConst (ctor : Name) (idx : Nat)
deriving Repr, BEq, Hashable, Inhabited

/-- The numeral `n` denotes the variable `n`. -/
instance : OfNat Arg n := ⟨.var n⟩

/-- The constructor's own name, without the enum class a clause may write it through. -/
def ctorBaseName (ctor : Name) : String := (ctor.updatePrefix .anonymous).toString

namespace Arg

/-- The variable an argument is, if it is one. -/
def var? : Arg → Option Var
  | .var v => some v
  | .enumConst .. => none

/-- Rename the variable of an argument. -/
def rename (ρ : Var → Var) : Arg → Arg
  | .var v => .var (ρ v)
  | a => a

end Arg

/-- A term of a numeric sort: a numeric symbol applied to arguments. -/
structure NumTerm where
  /-- A numeric symbol. -/
  sym : Symbol
  /-- Its arguments. -/
  args : Array Arg
deriving Repr, BEq, Hashable, Inhabited

/-- The sort of a numeric term: the result sort of its symbol. -/
def NumTerm.sort (t : NumTerm) : SortName := t.sym.argSorts.back!

/-- An atomic formula: a symbol applied to arguments, the equality of two variables, or the
linear constraint `Σ kᵢ * tᵢ + c = 0` (when `isEq`) or `Σ kᵢ * tᵢ + c ≤ 0`. -/
inductive Atom where
  | rel (sym : Symbol) (args : Array Arg)
  | eq (a b : Var)
  | lin (terms : Array (Int × NumTerm)) (const : Int) (isEq : Bool)
deriving Repr, BEq, Hashable, Inhabited

namespace Atom

/-- `t = n`. -/
def numEq (t : NumTerm) (n : Int) : Atom := .lin #[(1, t)] (-n) true
/-- `t ≤ n`. -/
def numLe (t : NumTerm) (n : Int) : Atom := .lin #[(1, t)] (-n) false
/-- `n ≤ t`. -/
def numGe (t : NumTerm) (n : Int) : Atom := .lin #[(-1, t)] n false
/-- `s < t`, as `s + 1 ≤ t`. -/
def numLt (s t : NumTerm) : Atom := .lin #[(1, s), (-1, t)] 1 false
/-- `s = t + c`. -/
def numEqOffset (s t : NumTerm) (c : Int) : Atom := .lin #[(1, s), (-1, t)] (-c) true
/-- `s ≤ t + c`. -/
def numLeOffset (s t : NumTerm) (c : Int) : Atom := .lin #[(1, s), (-1, t)] (-c) false
/-- `s + t = u`. -/
def numSumEq (s t u : NumTerm) : Atom := .lin #[(1, s), (1, t), (-1, u)] 0 true
/-- `s + t ≤ u`. -/
def numSumLe (s t u : NumTerm) : Atom := .lin #[(1, s), (1, t), (-1, u)] 0 false
/-- `u ≤ s + t`. -/
def numLeSum (u s t : NumTerm) : Atom := .lin #[(1, u), (-1, s), (-1, t)] 0 false

/-- Whether the atom compares a single term with a numeral. -/
def isNumeral : Atom → Bool
  | .lin terms _ _ => terms.size == 1
  | _ => false

/-- The arguments of an atom, in order. -/
def args : Atom → Array Arg
  | .rel _ args => args
  | .eq a b => #[.var a, .var b]
  | .lin terms _ _ => terms.flatMap (·.2.args)

/-- The variables of an atom, in order of occurrence. -/
def vars (a : Atom) : Array Var := a.args.filterMap Arg.var?

/-- Rename the variables of an atom. -/
def rename (ρ : Var → Var) : Atom → Atom
  | .rel s args => .rel s (args.map (·.rename ρ))
  | .eq a b => .eq (ρ a) (ρ b)
  | .lin terms c isEq =>
    .lin (terms.map fun (k, t) ↦ (k, { t with args := t.args.map (·.rename ρ) })) c isEq

/-- The pairs of corresponding arguments of two atoms of the same shape: the same symbol, or
linear constraints with the same coefficients, symbols and constant. `none` otherwise. -/
def argPairs? : Atom → Atom → Option (Array (Arg × Arg))
  | .rel s args, .rel s' args' =>
    if s == s' && args.size == args'.size then some (args.zip args') else none
  | .eq a b, .eq a' b' => some #[(.var a, .var a'), (.var b, .var b')]
  | .lin ts c e, .lin ts' c' e' =>
    let sameShape (p : (Int × NumTerm) × (Int × NumTerm)) : Bool :=
      p.1.1 == p.2.1 && p.1.2.sym == p.2.2.sym && p.1.2.args.size == p.2.2.args.size
    if c == c' && e == e' && ts.size == ts'.size && (ts.zip ts').all sameShape then
      some ((ts.zip ts').flatMap fun ((_, t), (_, t')) ↦ t.args.zip t'.args)
    else none
  | _, _ => none

end Atom

/-- An atom or its negation. -/
structure Literal where
  /-- Whether the literal is the atom rather than its negation. -/
  positive : Bool
  atom : Atom
deriving Repr, BEq, Hashable, Inhabited

namespace Literal

/-- The negation of a literal. -/
def negate (l : Literal) : Literal := { l with positive := !l.positive }

/-- Rename the variables of a literal. -/
def rename (ρ : Var → Var) (l : Literal) : Literal := { l with atom := l.atom.rename ρ }

/-- One more than the largest variable of the literal, `0` when it has none: the number of
leading variables to assign before the literal can be evaluated. -/
def width (l : Literal) : Nat := l.atom.vars.foldl (fun w v ↦ max w (v + 1)) 0

end Literal

/-- The universal clause `∀ vars, ⋁ lits`. The empty disjunction is `False`. -/
structure Clause where
  /-- The sorts of the bound variables `x0, x1, …`. -/
  vars : Array SortName
  /-- The disjuncts. -/
  lits : Array Literal
deriving Repr, BEq, Hashable, Inhabited

namespace Clause

/-- Which variables occur in some literal. -/
def usedVars (c : Clause) : Array Bool :=
  c.lits.foldl (init := Array.replicate c.vars.size false) fun used l ↦
    l.atom.vars.foldl (init := used) fun used v ↦ if v < used.size then used.set! v true else used

/-- Remove the variables no literal uses, renumbering the others in order. -/
def pruneVars (c : Clause) : Clause :=
  let used := c.usedVars
  let kept := (Array.range c.vars.size).filter (used[·]!)
  let ρ (v : Var) : Var := (kept.idxOf? v).getD 0
  { vars := kept.map (c.vars[·]!), lits := c.lits.map (·.rename ρ) }

/-- The clause made of the literals whose index satisfies `p`, with unused variables pruned. -/
def restrict (c : Clause) (p : Nat → Bool) : Clause :=
  pruneVars { c with lits := c.lits.zipIdx.filterMap fun (l, i) ↦ if p i then some l else none }

/-! ### Subsumption -/

/-- A partial renaming of the variables of one clause into those of another: entry `v` is the
image of variable `v`, once chosen. -/
abbrev Renaming := Array (Option Var)

/-- Extend `ρ`, a renaming of variables of sorts `cs` into variables of sorts `ds`, so that `v`
maps to `w`. -/
def bindVar (cs ds : Array SortName) (ρ : Renaming) (v w : Var) : Option Renaming :=
  match ρ[v]? with
  | some (some w') => if w' == w then some ρ else none
  | some none => if cs[v]? == ds[w]? && w < ds.size then some (ρ.set! v (some w)) else none
  | none => none

/-- Extend `ρ` so that argument `a` renames to argument `b`. -/
def bindArg (cs ds : Array SortName) (ρ : Renaming) : Arg × Arg → Option Renaming
  | (.var v, .var w) => bindVar cs ds ρ v w
  | (a, b) => if a == b then some ρ else none

/-- Extend `ρ` so that literal `l` renames to literal `m`. -/
def bindLiteral (cs ds : Array SortName) (ρ : Renaming) (l m : Literal) : Option Renaming :=
  if l.positive != m.positive then none
  else (l.atom.argPairs? m.atom).bind (·.foldlM (bindArg cs ds) ρ)

/-- `c` subsumes `d` when some sort-respecting renaming of the variables of `c` into those of
`d` maps every literal of `c` to a literal of `d`. Then `c` implies `d`.

The renaming is built one literal of `c` at a time, always the literal with the fewest possible
images, so that a literal without one ends the branch at once. -/
def subsumes (c d : Clause) : Bool :=
  c.vars.all d.vars.contains &&
    go c.lits.size (Array.range c.lits.size) (Array.replicate c.vars.size none)
where
  /-- Match the literals of `c` at indices `todo` under `ρ`; `fuel` is the number left. -/
  go : Nat → Array Nat → Renaming → Bool
    | 0, todo, _ => todo.isEmpty
    | fuel + 1, todo, ρ => Id.run do
      if todo.isEmpty then return true
      let mut best : Option (Nat × Array Renaming) := none
      for k in [:todo.size] do
        let exts := d.lits.filterMap (bindLiteral c.vars d.vars ρ c.lits[todo[k]!]! ·)
        if exts.isEmpty then return false
        if best.all (exts.size < ·.2.size) then best := some (k, exts)
        if exts.size == 1 then break
      let some (k, exts) := best | return false
      return exts.any (go fuel (todo.eraseIdx! k) ·)

/-- Insert `a` into `xs` unless the clause of an element subsumes its clause, dropping the
elements whose clause the clause of `a` subsumes. -/
def insertSubsuming (clause : α → Clause) (xs : Array α) (a : α) : Array α :=
  if xs.any fun x ↦ (clause x).subsumes (clause a) then xs
  else (xs.filter fun x ↦ !(clause a).subsumes (clause x)).push a

/-- The elements of `xs` whose clause the clause of no other element subsumes, keeping the first
of equivalent ones. -/
def removeSubsumed (clause : α → Clause) (xs : Array α) : Array α :=
  let cs := xs.map clause
  let redundant (i : Nat) : Bool := (Array.range cs.size).any fun j ↦
    j != i && cs[j]!.subsumes cs[i]! && (!cs[i]!.subsumes cs[j]! || j < i)
  (xs.zipIdx.filter fun (_, i) ↦ !redundant i).map (·.1)

end Clause

end Veil.Synthesizer
