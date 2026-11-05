module

public meta import Lean
public meta import Veil.Core.Tools.Synthesizer.Structure

/-!
# Rendering clauses and structures

This file writes clauses as Veil terms, for the solver queries and the certificates, and as text,
for the messages a user pastes into a module. It also writes finite structures as text.

## Main definitions

* `Veil.Synthesizer.Written`: an expression in the surface syntax of a Veil module.
* `Veil.Synthesizer.Clause.written`: a clause as written in a module:
  `∀ (x0 x1 : node), ¬ leader x0 ∨ tot.le x1 x0`.
* `Veil.Synthesizer.Clause.toTerm`, `Veil.Synthesizer.Clause.toString`: its two renderings.
* `Veil.Synthesizer.FinStructure.render`: a structure as one line per symbol.

## Implementation notes

A function atom is written as the equation `f x0 = x1`, a linear constraint with its negative
coefficients moved to the right-hand side so that no subtraction is written, and an enum
constructor by its name. Class symbols are written through the instance binder (`tot.le`), which
is in scope both in a module and in the binders of a query.
-/

public meta section

namespace Veil.Synthesizer
open Lean Lean.Parser.Term

/-- An expression in the surface syntax of a Veil module, as UPDR writes it. -/
inductive Written where
  | ident (n : Name)
  | app (f : Name) (args : Array Written)
  /-- A numeral of a numeric sort; the term ascribes the sort. -/
  | numeral (sort : SortName) (n : Int)
  /-- `k * t`. -/
  | scale (k : Nat) (t : Written)
  /-- A sum of at least one term. -/
  | sum (parts : Array Written)
  | eq (a b : Written)
  | le (a b : Written)
  | not (a : Written)
  /-- A disjunction of at least one formula. -/
  | or (parts : Array Written)
  | false
  | forall (binders : Array (Name × SortName)) (body : Written)
deriving Inhabited

/-- The name of the `i`-th bound variable of a clause. -/
def varName (i : Nat) : Name := .mkSimple s!"x{i}"

/-- The identifier of the `i`-th bound variable of a clause. -/
def varIdent (i : Nat) : Ident := mkIdent (varName i)

namespace Written

/-- The Lean term of a written expression. -/
partial def toTerm [Monad m] [MonadQuotation m] : Written → m Term
  | .ident n => pure (mkIdent n)
  | .app f args => do `($(mkIdent f) $(← args.mapM toTerm)*)
  | .numeral s n => do
    let lit : Term := Syntax.mkNumLit (toString n.natAbs)
    if n < 0 then `((-$lit : $(mkIdent s))) else `(($lit : $(mkIdent s)))
  | .scale k t => do `($(Syntax.mkNumLit (toString k)) * $(← t.toTerm))
  | .sum ps => fold (fun a b ↦ `($a + $b)) ps
  | .eq a b => do `($(← a.toTerm) = $(← b.toTerm))
  | .le a b => do `($(← a.toTerm) ≤ $(← b.toTerm))
  | .not a => do `(¬ $(← a.toTerm))
  | .or ps => fold (fun a b ↦ `($a ∨ $b)) ps
  | .false => `(False)
  | .forall bs body => do
    let binders ← bs.mapM fun (x, s) ↦ `(bracketedBinder| ($(mkIdent x) : $(mkIdent s)))
    `(∀ $binders*, $(← body.toTerm))
where
  /-- Combine the terms of `ps` from the left with `op`. -/
  fold (op : Term → Term → m Term) (ps : Array Written) : m Term := do
    let ts ← ps.mapM toTerm
    ts[1:].foldlM op ts[0]!

/-- The text of a written expression. -/
partial def toString : Written → String
  | .ident n => n.toString
  | .app f args => " ".intercalate (f.toString :: (args.map toString).toList)
  | .numeral _ n => ToString.toString n
  | .scale k t => s!"{k} * {t.toString}"
  | .sum ps => " + ".intercalate (ps.map toString).toList
  | .eq a b => s!"{a.toString} = {b.toString}"
  | .le a b => s!"{a.toString} ≤ {b.toString}"
  | .not a => s!"¬ {a.toString}"
  | .or ps => " ∨ ".intercalate (ps.map toString).toList
  | .false => "False"
  | .forall bs body =>
    s!"∀ {" ".intercalate (bs.map fun (x, s) ↦ s!"({x} : {s})").toList}, {body.toString}"

end Written

/-- An argument as written: a variable `xᵢ` or a constructor. -/
def Arg.written : Arg → Written
  | .var v => .ident (varName v)
  | .enumConst ctor _ => .ident ctor

/-- A symbol applied to arguments, as written. -/
def Symbol.apply (f : Symbol) (args : Array Written) : Written :=
  if args.isEmpty then .ident f.key else .app f.key args

/-- One side of a linear constraint: the sum of `k * t` and a positive constant `c`, or the
numeral `0` of `sort` when it is empty. -/
def linearSide (sort : SortName) (terms : Array (Int × NumTerm)) (c : Int) : Written :=
  let parts := terms.map fun (k, t) ↦
    let t := t.sym.apply (t.args.map Arg.written)
    if k == 1 then t else .scale k.natAbs t
  let parts := if c > 0 then parts.push (.numeral sort c) else parts
  if parts.isEmpty then .numeral sort 0 else .sum parts

/-- An atom as written. -/
def Atom.written : Atom → Written
  | .rel sym args =>
    let args := args.map Arg.written
    if sym.isFunction && !args.isEmpty then .eq (sym.apply args.pop) args.back! else sym.apply args
  | .eq a b => .eq (.ident (varName a)) (.ident (varName b))
  | .lin terms c isEq =>
    let sort := (terms[0]?.map (·.2.sort)).getD `Int
    let lhs := linearSide sort (terms.filter (·.1 > 0)) c
    let rhs := linearSide sort ((terms.filter (·.1 < 0)).map fun (k, t) ↦ (-k, t)) (-c)
    if isEq then .eq lhs rhs else .le lhs rhs

/-- A literal as written. -/
def Literal.written (l : Literal) : Written :=
  if l.positive then l.atom.written else .not l.atom.written

/-- A clause as written. -/
def Clause.written (c : Clause) : Written :=
  let body := if c.lits.isEmpty then .false else .or (c.lits.map Literal.written)
  if c.vars.isEmpty then body else .forall (c.vars.mapIdx fun i s ↦ (varName i, s)) body

/-- A literal as a Lean term. -/
def Literal.toTerm [Monad m] [MonadQuotation m] (l : Literal) : m Term := l.written.toTerm

/-- A clause as a Lean term. -/
def Clause.toTerm [Monad m] [MonadQuotation m] (c : Clause) : m Term := c.written.toTerm

/-- A clause as text, ready to paste into a module. -/
def Clause.toString (c : Clause) : String := c.written.toString

instance : ToString Clause := ⟨Clause.toString⟩

/-- A numeral of a numeric sort as a term, `(3 : Int)`. -/
def numeralTerm [Monad m] [MonadQuotation m] (sort : SortName) (n : Int) : m Term :=
  (Written.numeral sort n).toTerm

namespace FinStructure

/-- Element `i` of sort `s` as text: its constructor for an enum sort, its index otherwise. -/
def elementName (m : FinStructure) (s : SortName) (i : Nat) : String :=
  match m.enumCtor? s i with
  | some c => c.toString
  | none => ToString.toString i

/-- A structure as text: its sorts, then one line per symbol. A relation is the set of its tuples,
a 0-ary relation `true` or `false`, and a function the rows `(args)↦value`. -/
def render (m : FinStructure) : String :=
  let names (sorts : Array SortName) (t : Array Nat) : List String :=
    ((sorts.zip t).map fun (s, i) ↦ m.elementName s i).toList
  let row (args : List String) (value : String) : String :=
    if args.isEmpty then value else "(" ++ ",".intercalate args ++ ")↦" ++ value
  let sorts := ", ".intercalate <| m.sorts.toList.map fun (s, n) ↦
    match m.enums.find? (·.1 == s) with
    | some (_, ctors) => s!"{s} = \{{", ".intercalate (ctors.toList.map (·.toString))}}"
    | none => s!"{s} = Fin {n}"
  let rels := m.rels.toList.map fun (sym, tuples) ↦
    let table :=
      if sym.isFunction then
        " ".intercalate <| tuples.toList.map fun t ↦
          let ns := names sym.argSorts t
          row ns.dropLast (ns.getLast?.getD "?")
      else if sym.argSorts.isEmpty then if tuples.isEmpty then "false" else "true"
      else if tuples.isEmpty then "∅"
      else " ".intercalate <| tuples.toList.map fun t ↦
        "(" ++ ",".intercalate (names sym.argSorts t) ++ ")"
    s!"    {sym.key}: {table}"
  let nums := m.nums.toList.map fun (sym, table) ↦
    let rows := table.toList.map fun (t, v) ↦ row (names sym.argSorts.pop t) (ToString.toString v)
    s!"    {sym.key}: {" ".intercalate rows}"
  s!"    sorts: {sorts}\n" ++ "\n".intercalate (rels ++ nums)

end FinStructure

end Veil.Synthesizer
