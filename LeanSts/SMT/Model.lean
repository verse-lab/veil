import Lean
import Auto
import LeanSts.MetaUtil
import Batteries.Data.Array.Basic

abbrev SortName := Lean.Name
abbrev UninterpretedValue := Lean.Name

instance : Ord SortName where
  compare a b := a.cmp b
instance : Ord UninterpretedValue where
  compare a b := a.cmp b

instance [Ord α] : Ord (Array α) where
  compare a b :=
    a.zip b |>.foldl (init := Ordering.eq) fun c (a, b) => match c with
      | Ordering.eq => compare a b
      | c => c

instance [Ord α] [Ord β] : Ord (α × β) where
  compare x y := match x, y with
    | (a, b), (a', b') => compare a a' |>.then (compare b b')

structure FiniteUninterpretedSort where
  name : SortName
  size : Nat
  /-- The elements are assumed to be distinct. -/
  elements : Array UninterpretedValue
deriving BEq, Hashable, Inhabited, Ord

instance : ToString FiniteUninterpretedSort where
  toString s := s!"sort {s.name} = {s.elements}"

structure InterpretedSort where
  name : SortName
  -- interpretation : Type
deriving BEq, Hashable, Inhabited, Ord

instance : ToString InterpretedSort where
  toString s := s!"interpreted sort {s.name}"

def boolSortI : InterpretedSort := { name := `Bool }
def intSortI : InterpretedSort := { name := `Int }

def builtinInterpretedSorts : Lean.HashMap SortName InterpretedSort :=
  Lean.HashMap.ofList [(`Bool, boolSortI), (`Int, intSortI)]

def InterpretedSort.interpretation (s : InterpretedSort) : Type :=
  match s.name with
  | `Bool => Bool
  | `Int => Int
  | _ => Unit

/- FIXME: I don't know how to write this without tactics. -/
def InterpretedSort.valToString {s : InterpretedSort} (val : s.interpretation) : String := by
  unfold interpretation at val
  split at val <;> exact (toString val)

instance : BEq InterpretedSort where
  beq s₁ s₂ := s₁.name == s₂.name

instance : Hashable InterpretedSort where
  hash s := (`InterpretedSort ++ s.name).hash

inductive FirstOrderSort
  | Interpreted (s : InterpretedSort)
  | Uninterpreted (s : FiniteUninterpretedSort)
deriving BEq, Hashable, Inhabited, Ord

instance : ToString FirstOrderSort where
  toString
    | FirstOrderSort.Interpreted s => toString s
    | FirstOrderSort.Uninterpreted s => toString s

def FirstOrderSort.name : FirstOrderSort → SortName
  | FirstOrderSort.Interpreted s => s.name
  | FirstOrderSort.Uninterpreted s => s.name

def FirstOrderSort.size : FirstOrderSort → Nat
  | FirstOrderSort.Interpreted _ => 1
  | FirstOrderSort.Uninterpreted s => s.size

open Lean Elab Term Meta in
/-- Create an SMT constraint that the given sort has cardinality *at most* `n`.-/
def FirstOrderSort.cardinalityConstraint (n : Nat) : FirstOrderSort → MetaM (Option Expr)
  | FirstOrderSort.Interpreted _ => return none
  | FirstOrderSort.Uninterpreted s => do
    -- We construct a ∃∀ formula of the form ∃a, b, c. ∀x. (x = a) ∨ (x = b) ∨ (x = c)
    -- If we want an *exact* constraint, we need to assert `distinct(a, b, c)` as well.
    let mut existentials := #[]
    let varN := mkIdent (Name.mkSimple s!"x_{s.name}")
    let mut disjs := #[]
    for i in [:n] do
      let varI := mkIdent (Name.mkSimple s!"card_{s.name}_{i}")
      let disj ← `(term|($varN = $varI))
      existentials := existentials.push (varI, .some s.name)
      disjs := disjs.push disj
    let body ← `(term|forall $varN, $(← repeatedOr disjs))
    let stx ← repeatedExists existentials body
    let (expr, _) ← TermElabM.run <| elabTerm stx .none
    return expr

inductive FirstOrderValue where
  | Interpreted (s : InterpretedSort) (val : s.interpretation)
  | Uninterpreted (s : FiniteUninterpretedSort) (val : UninterpretedValue)

instance : Ord FirstOrderValue where
  compare x y := match x, y with
    | .Uninterpreted s₁ v₁, .Uninterpreted s₂ v₂ =>
      match compare s₁ s₂ with
      | Ordering.eq => compare v₁ v₂
      | o => o
    | .Interpreted s₁ _v₁, .Interpreted s₂ _v₂ =>
      match compare s₁ s₂ with
      | Ordering.eq =>
        -- FIXME: we need to use the `Ord` instance for the interpretation type
        Ordering.eq
      | o => o
    | .Interpreted .., .Uninterpreted .. => Ordering.lt
    | .Uninterpreted .., .Interpreted .. => Ordering.gt

def FirstOrderValue.isTrue (val : FirstOrderValue) : Bool :=
  match val with
  | FirstOrderValue.Interpreted { name := `Bool } b => b
  | _ => false

instance : ToString FirstOrderValue where
  toString
    | FirstOrderValue.Interpreted s val => s.valToString val
    | FirstOrderValue.Uninterpreted _ val => toString val

def Array.funcArgsString (vals : Array FirstOrderValue) : String :=
  "(" ++ (String.intercalate ", " (vals.map toString).toList) ++ ")"

def boolSort : FirstOrderSort := FirstOrderSort.Interpreted boolSortI
def intSort : FirstOrderSort := FirstOrderSort.Interpreted intSortI

structure ConstantDecl where
  name : SortName
  sort : FirstOrderSort
deriving BEq, Hashable, Ord

instance : ToString ConstantDecl where
  toString c := s!"constant {c.name} : {c.sort}"

structure RelationDecl where
  name : SortName
  domain : Array FirstOrderSort
deriving BEq, Hashable, Ord

instance : ToString RelationDecl where
  toString r := s!"relation {r.name} : {r.domain}"

structure FunctionDecl where
  name : SortName
  domain : Array FirstOrderSort
  range : FirstOrderSort
deriving BEq, Hashable, Ord

instance : ToString FunctionDecl where
  toString f := s!"function {f.name} : {f.domain} → {f.range}"

inductive Declaration where
  | Constant (c : ConstantDecl)
  | Relation (r : RelationDecl)
  | Function (f : FunctionDecl)
deriving BEq, Hashable, Ord

instance : ToString Declaration where
  toString
    | Declaration.Constant c => toString c
    | Declaration.Relation r => toString r
    | Declaration.Function f => toString f

def Declaration.name : Declaration → SortName
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

/-- We want to sort declarations by name, even if they are of different types. -/
instance (priority := high) : Ord Declaration where
  compare x y := compare x.name y.name |>.then (compare x y)

/-- Create a SMT constraint that the number of elements in the relation to be *at most* n. -/
def Declaration.cardinalityConstraint (decl : Declaration) (n : Nat) :  Lean.MetaM (Option Lean.Expr) :=
  match decl with
  | Declaration.Constant _ => return none
  | Declaration.Function _ => return none
  | Declaration.Relation _ => do
    -- We create a formula of the form:
    -- ∃ c11, c21, c31, c12, c22, c32.
    --  ∀ x1, x2, x3. rel x1 x2 x3 → (
    --     (x1 = c11 ∧ x2 = c21 ∧ x3 = c31) ∨
    --     (x1 = c12 ∧ x2 = c22 ∧ x3 = c32)
    --   )
    -- there are `arity * n` existentials, `arity` univeralsand `n` disjunctions
    -- e.g. #[c11, c21, c31, c12, c22, c32] (with respective sorts)
    let mut existentials : Array (Lean.Ident × Option SortName) := #[]
    -- stores each argument instance, e.g. #[[c11, c21, c31], [c12, c22, c32]]
    let mut relInstances : Array (Array Lean.Ident) := #[]
    -- e.g. #[x1, x2, x3] (with respective sorts)
    let mut universals : Array (Lean.Ident × Option SortName) := #[]
    -- generate `arity` universal variables
    for j in [0 : decl.arity] do
      let sortName := (decl.domain[j]!).name
      let varJ := Lean.mkIdent (Lean.Name.mkSimple s!"x_{decl.name}_{j}")
      -- NOTE: `Nat` gets represented as `Int` in the model, so we let
      -- type inference figure out the correct type in this case
      if sortName == `Int then
        universals := universals.push (varJ, none)
      else
        universals := universals.push (varJ, sortName)
    -- generate `n` instances of the relation
    for i in [0 : n] do
      let mut relInstanceArgs := #[]
      for j in [0 : decl.arity] do
        let sortName := (decl.domain[j]!).name
        let varI := Lean.mkIdent (Lean.Name.mkSimple s!"card_{decl.name}_{i}_{j}")
        -- NOTE: `Nat` gets represented as `Int` in the model, so we let
        -- type inference figure out the correct type in this case
        if sortName == `Int then
          existentials := existentials.push (varI, none)
        else
          existentials := existentials.push (varI, sortName)
        relInstanceArgs := relInstanceArgs.push varI
      relInstances := relInstances.push relInstanceArgs
    let universalVars := universals.map Prod.fst
    -- build the expression bottom-up
    let mut disjs := #[]
    for i in [0 : n] do
      let mut eqs := #[]
      for (x, c) in Array.zip universalVars relInstances[i]! do
        eqs := eqs.push <| ← `(term|($x = $c))
      disjs := disjs.push <| ← `(term|$(← repeatedAnd eqs))
    let disj ← repeatedOr disjs
    let relApp ← `(term|$(Lean.mkIdent decl.name) $universalVars*)
    let forallBody ← `(term|($relApp → $disj))
    let existsBody ← repeatedForall universals forallBody
    let stx ← repeatedExists existentials existsBody
    let (expr, _) ← Lean.Elab.Term.TermElabM.run <| Lean.Elab.Term.elabTerm stx .none
    -- dbg_trace s!"cardinality constraint for {decl.name} (size = {n}): {← Lean.Meta.ppExpr expr}"
    return (some expr)

structure Signature where
  constants : Array ConstantDecl
  relations : Array RelationDecl
  functions : Array FunctionDecl
deriving BEq, Hashable, Ord

instance : Inhabited Signature := ⟨{ constants := #[], relations := #[], functions := #[] }⟩

def Signature.declarations (sig : Signature) : Array Declaration :=
  sig.constants.map Declaration.Constant ++
  sig.relations.map Declaration.Relation ++
  sig.functions.map Declaration.Function

abbrev InputOutputPair := (Array FirstOrderValue) × FirstOrderValue

inductive Interpretation
  | Enumeration (iopairs : Array InputOutputPair)
  | Symbolic    (expr : String)
deriving Ord, Inhabited

def Interpretation.toString (interp : Interpretation) (decl : Declaration) : Id String := do
  let mut out := ""
  match interp with
  | .Enumeration iopairs =>
    for (args, val) in iopairs.qsortOrd do
      match decl with
      | Declaration.Constant c => out := out ++ s!"{c.name} = {val}\n"
      | Declaration.Relation r =>
          -- out := out ++ s!"{r.name}{args.funcArgsString} = {val}\n"
          if val.isTrue then out := out ++ s!"{r.name}{args.funcArgsString} = true\n"
      | Declaration.Function f => out := out ++ s!"{f.name}{args.funcArgsString} = {val}\n"
  | .Symbolic str => out := out ++ s!"{decl.name} = {str}\n"
  return out

def Interpretation.push (i : Interpretation) (iop : InputOutputPair) : Interpretation :=
  match i with
  | Interpretation.Enumeration iopairs => Interpretation.Enumeration (iopairs.push iop)
  | _ => panic! s!"tried to push an input-output pair to symbolic interpretation"

abbrev ExplicitInterpretation := Lean.HashMap Declaration Interpretation

instance : Ord ExplicitInterpretation where
  compare x y := compare x.toArray y.toArray

structure FirstOrderStructure where
  /-- Also called universes. -/
  domains : Array FirstOrderSort
  signature : Signature
  interp : ExplicitInterpretation
deriving Ord

open Lean hiding Declaration

/- FIXME: make this match mypyvy output to a greater extent -/
instance : ToString FirstOrderStructure where
  toString s := Id.run (do
    let mut out := s!"\n"
    for dom in s.domains do
      out := out ++ s!"{dom}\n"
    for (decl, interp) in s.interp.toArray.qsortOrd do
      out := out ++ (← interp.toString decl)
    return out)

def FirstOrderStructure.findSort (s : FirstOrderStructure) (name : Lean.Name) : MetaM FirstOrderSort :=
  match s.domains.find? (fun s => s.name == name) with
  | some sort => return sort
  | none => throwError s!"sort {name} used but not previously declared!"

def FirstOrderStructure.findDecl (s : FirstOrderStructure) (name : Lean.Name) : MetaM Declaration :=
  match s.signature.constants.find? (fun c => c.name == name) with
  | some c => return Declaration.Constant c
  | none => match s.signature.relations.find? (fun r => r.name == name) with
    | some r => return Declaration.Relation r
    | none => match s.signature.functions.find? (fun f => f.name == name) with
      | some f => return Declaration.Function f
      | none => throwError s!"{name} provided an interpretation for, but not previously declared!"

def FirstOrderStructure.isInterpretedByFiniteEnumeration (s : FirstOrderStructure) (decl : Declaration) : Bool :=
  match s.interp.find? decl with
  | some (Interpretation.Enumeration _) => true
  | _ => false

/-- On how many argument vectors is this constant/relation/function `True`? -/
def FirstOrderStructure.numTrueInstances (s : FirstOrderStructure) (decl : Declaration) : MetaM Nat := do
  match s.interp.find? decl with
  | none => return 0
  | some (.Enumeration iopairs) =>
      return iopairs.foldl (init := 0) fun c (_, res) => if res.isTrue then c + 1 else c
  | _ => throwError s!"cannot call `FirstOrderStructure.numTrueInstances` on a symbolic interpretation!"

instance : Inhabited FirstOrderStructure := ⟨{ domains := #[], signature := default, interp := default }⟩

open Auto.Parser.SMTSexp
abbrev Sexpr := Auto.Parser.SMTSexp.Sexp

partial def extractInstructions (e : Sexpr) (depth : Int := 0): MetaM (List Sexpr) := do
  match e with
  | .atom _ => throwError s!"malformed model: unexpected atom at depth {depth}"
  | .app xs =>
      let mut instructions : List Sexpr:= if depth == 1 then [e] else []
      if depth == 0 then
        for x in xs do
          instructions := instructions ++ (← extractInstructions x (depth + 1))
      return instructions

def findSortWithName (name : Lean.Name) (struct : FirstOrderStructure) : MetaM FirstOrderSort :=
  match struct.domains.find? (fun s => s.name == name) with
  | some sort => return sort
  | none => throwError s!"sort {name} used but not previously declared!"

def findSortsArray (names : Array Sexp) (struct : FirstOrderStructure) : MetaM (Array FirstOrderSort) := do
  let mut sorts : Array FirstOrderSort := #[]
  for dom in names do
    match dom with
    | .atom (.symb domName) => sorts := sorts.push (← findSortWithName domName.toName struct)
    | _ => throwError s!"malformed domain: {dom}"
  return sorts

def getValueOfSort (val : Sexp) (sort : FirstOrderSort) : MetaM FirstOrderValue := do
  match sort with
  | FirstOrderSort.Interpreted s => do
    match s.name with
    | `Bool => match val with
      | .atom (.symb "true") => return FirstOrderValue.Interpreted boolSortI true
      | .atom (.symb "false") => return FirstOrderValue.Interpreted boolSortI false
      | _ => throwError s!"expected a boolean value, but got {val}"
    | `Int => match val with
      | .atom (.nat n) => return FirstOrderValue.Interpreted intSortI (Int.ofNat n)
      | .atom (.symb i) => return FirstOrderValue.Interpreted intSortI i.toInt!
      | _ => throwError s!"expected an integer value, but got {val}"
    | _ => throwError s!"unsupported interpreted sort: {s}"
  | FirstOrderSort.Uninterpreted s => do
    match val with
    | .atom (.symb valName) => return FirstOrderValue.Uninterpreted s valName.toName
    | _ => throwError s!"expected an uninterpreted value, but got {val}"

def getValueArray (vals : Array Sexp) (sorts : Array FirstOrderSort) : MetaM (Array FirstOrderValue) := do
  let mut values : Array FirstOrderValue := #[]
  for (val, sort) in Array.zip vals sorts do
    values := values.push (← getValueOfSort val sort)
  return values

def parseInstruction (inst : Sexpr) (struct : FirstOrderStructure): MetaM (FirstOrderStructure) := do
  let mut struct := struct
  match inst with
  -- (|sort| |Bool| (|true| |false|)),
  -- (|sort| |a| (|a0| |a1|)),
  | .app #[(.atom (.symb "sort")), (.atom (.symb sortName)), (.app els)] => do
    let sortName := sortName.toName
    let sort: FirstOrderSort ← (match builtinInterpretedSorts.find? sortName with
    | some sortI => return .Interpreted sortI
    | none => do
      let mut elems : Array UninterpretedValue := #[]
      for elem in els do
        match elem with
        | .atom (.symb elemName) => elems := elems.push elemName.toName
        | _ => throwError s!"malformed element: {elem}"
      return .Uninterpreted { name := sortName, size := elems.size, elements := elems }
    )
    trace[sauto.debug] s!"{sort}"
    struct := { struct with domains := struct.domains.push sort }

  -- (|constant| |s1| |a|),
  | .app #[(.atom (.symb "constant")), (.atom (.symb constName)), (.atom (.symb sortName))] => do
    let constName := constName.toName
    let sortName := sortName.toName
    let sort ← findSortWithName sortName struct
    let decl: ConstantDecl := { name := constName, sort := sort }
    trace[sauto.debug] s!"{decl}"
    struct := { struct with signature := { struct.signature with constants := struct.signature.constants.push decl } }

  -- (|relation| |rel| (|a| |a|)),
  | .app #[(.atom (.symb "relation")), (.atom (.symb relName)), (.app doms)] => do
    let relName := relName.toName
    let doms ← findSortsArray doms struct
    let decl: RelationDecl := { name := relName, domain := doms }
    trace[sauto.debug] s!"{decl}"
    struct := { struct with signature := { struct.signature with relations := struct.signature.relations.push decl } }

  -- (|function| |f| (|a|) |Int|),
  | .app #[(.atom (.symb "function")), (.atom (.symb funName)), (.app doms), (.atom (.symb range))] => do
    let funName := funName.toName
    let doms ← findSortsArray doms struct
    let range ← findSortWithName range.toName struct
    let decl: FunctionDecl := { name := funName, domain := doms, range := range }
    trace[sauto.debug] s!"{decl}"
    struct := { struct with signature := { struct.signature with functions := struct.signature.functions.push decl } }

  -- (|interpret| |rel| (|a0| |a0|) |false|)
  -- (|interpret| |f| (|a0|) |-1|)
  -- (|interpret| |f| (|a1|) 0)
  | .app #[(.atom (.symb "interpret")), (.atom (.symb declName)), (.app args), val] => do
    let declName := declName.toName
    let decl ← struct.findDecl declName
    let args ← getValueArray args decl.domain
    let val ← getValueOfSort val decl.range
    trace[sauto.debug] s!"interpret {declName} {args} {val}"
    let interp := struct.interp.findD decl (Interpretation.Enumeration #[])
    let interp' := interp.push (args, val)
    struct := { struct with interp := struct.interp.insert decl interp' }

  -- (|symbolic| |st.delivered| |Lambda([arg0, arg1, arg2], ...)|)
  | .app #[(.atom (.symb "symbolic")), (.atom (.symb declName)), (.atom (.symb interp))] => do
    let declName := declName.toName
    let decl ← struct.findDecl declName
    trace[sauto.debug] s!"symbolic {declName} {interp}"
    let interp := struct.interp.findD decl (Interpretation.Symbolic interp)
    struct := { struct with interp := struct.interp.insert decl interp }

  | _ => throwError s!"(parseInstruction) malformed instruction: {inst}"
  return struct

def extractStructure (model : Sexpr) : MetaM FirstOrderStructure := do
  let mut struct : FirstOrderStructure := default
  let instructions ← extractInstructions model
  trace[sauto.debug] "instructions: {instructions}"
  for inst in instructions do
    struct := (← parseInstruction inst struct)
  return struct
