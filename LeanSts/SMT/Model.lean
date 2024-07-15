import LeanSts.SMT.Main
import Lean

abbrev Name := Lean.Name
abbrev UninterpretedValue := Name

structure FiniteUinterpretedSort where
  name : Name
  size : Nat
  /-- The elements are assumed to be distinct. -/
  elements : Array UninterpretedValue

structure InterpretedSort where
  name : Name
  interpretation : Type

def boolSortI : InterpretedSort := { name := `Bool, interpretation := Bool }
def intSortI : InterpretedSort := { name := `Int, interpretation := Int }

inductive FirstOrderSort
  | Interpreted (s : InterpretedSort)
  | Uninterpreted (s : FiniteUinterpretedSort)

def FirstOrderSort.valueType : FirstOrderSort → Type
  | FirstOrderSort.Interpreted s => s.interpretation
  | FirstOrderSort.Uninterpreted _ => UninterpretedValue

def FirstOrderSort.valueTypeArray : Array FirstOrderSort → Array Type
  | xs => xs.map (λ s => s.valueType)

def boolSort : FirstOrderSort := FirstOrderSort.Interpreted boolSortI
def intSort : FirstOrderSort := FirstOrderSort.Interpreted intSortI

structure ConstantDecl where
  name : Name
  sort : FirstOrderSort

structure RelationDecl where
  name : Name
  domain : Array FirstOrderSort

structure FunctionDecl where
  name : Name
  domain : Array FirstOrderSort
  range : FirstOrderSort

inductive Declaration where
  | Constant (c : ConstantDecl)
  | Relation (r : RelationDecl)
  | Function (f : FunctionDecl)

def Declaration.name : Declaration → Name
  | Declaration.Constant c => c.name
  | Declaration.Relation r => r.name
  | Declaration.Function f => f.name

def Declaration.arity : Declaration → Nat
  | Declaration.Constant _ => 0
  | Declaration.Relation r => r.domain.size
  | Declaration.Function f => f.domain.size

def Declaration.domain : Declaration → Array FirstOrderSort
  | Declaration.Constant _ => #[]
  | Declaration.Relation r => r.domain
  | Declaration.Function f => f.domain

def Declaration.range : Declaration → FirstOrderSort
  | Declaration.Constant c => c.sort
  | Declaration.Relation _ => boolSort
  | Declaration.Function f => f.range

structure Signature where
  constants : Array ConstantDecl
  relations : Array RelationDecl
  functions : Array FunctionDecl

structure ExplicitInterpretation (sig : Signature) where
  interp :
    (d : Declaration) → -- TODO: `d` should be in `sig`
    {dom : Array Type // dom = FirstOrderSort.valueTypeArray d.domain} →
    {val : Type // val = FirstOrderSort.valueType d.range}

structure FirstOrderStructure where
  /-- Also called universes. -/
  domains : Array FirstOrderSort
  signature : Signature
  interp : ExplicitInterpretation signature


set_option trace.smt true
set_option trace.smt.solve true
set_option trace.smt.reconstruct.proof true

set_option trace.sauto true
set_option sauto.smt.solver "z3"

theorem model1 {a : Type} (rel : a → a → Prop) (f : a → Int) (s1 s2 : a) :
  rel s1 s2 → rel s2 s1 ∨ f s1 = f s2 := by
  sauto

-- TRY:
-- (check-sat-using (then macro-finder smt))

/-
    (
    (sort Bool (true false))
    (sort Int ())
    (sort a (a0 a1))
    (function f (a) Int)
    (interpret f (a0) -1)
    (interpret f (a1) 0)
    (relation rel (a a))
    (interpret rel (a0 a0) false)
    (interpret rel (a0 a1) false)
    (interpret rel (a1 a0) true)
    (interpret rel (a1 a1) false)
    (constant s1 a)
    (interpret s1 () a1)
    (constant s2 a)
    (interpret s2 () a0)
    )
-/
