import Lean
import Auto

abbrev Name := Lean.Name
abbrev UninterpretedValue := Name

structure FiniteUinterpretedSort where
  name : Name
  size : Nat
  /-- The elements are assumed to be distinct. -/
  elements : Array UninterpretedValue
deriving BEq, Hashable

instance : ToString FiniteUinterpretedSort where
  toString s := s!"sort {s.name} = {s.elements}"

structure InterpretedSort where
  name : Name
  -- interpretation : Type
deriving BEq, Hashable

instance : ToString InterpretedSort where
  toString s := s!"interpreted sort {s.name}"

def boolSortI : InterpretedSort := { name := `Bool }
def intSortI : InterpretedSort := { name := `Int }

def builtinInterpretedSorts : Lean.HashMap Name InterpretedSort :=
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
  | Uninterpreted (s : FiniteUinterpretedSort)
deriving BEq, Hashable

instance : ToString FirstOrderSort where
  toString
    | FirstOrderSort.Interpreted s => toString s
    | FirstOrderSort.Uninterpreted s => toString s

def FirstOrderSort.name : FirstOrderSort → Name
  | FirstOrderSort.Interpreted s => s.name
  | FirstOrderSort.Uninterpreted s => s.name

inductive FirstOrderValue where
  | Interpreted (s : InterpretedSort) (val : s.interpretation)
  | Uninterpreted (s : FiniteUinterpretedSort) (val : UninterpretedValue)

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
  name : Name
  sort : FirstOrderSort
deriving BEq, Hashable

instance : ToString ConstantDecl where
  toString c := s!"constant {c.name} : {c.sort}"

structure RelationDecl where
  name : Name
  domain : Array FirstOrderSort
deriving BEq, Hashable

instance : ToString RelationDecl where
  toString r := s!"relation {r.name} : {r.domain}"

structure FunctionDecl where
  name : Name
  domain : Array FirstOrderSort
  range : FirstOrderSort
deriving BEq, Hashable

instance : ToString FunctionDecl where
  toString f := s!"function {f.name} : {f.domain} → {f.range}"

inductive Declaration where
  | Constant (c : ConstantDecl)
  | Relation (r : RelationDecl)
  | Function (f : FunctionDecl)
deriving BEq, Hashable

instance : ToString Declaration where
  toString
    | Declaration.Constant c => toString c
    | Declaration.Relation r => toString r
    | Declaration.Function f => toString f

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

instance : Inhabited Signature := ⟨{ constants := #[], relations := #[], functions := #[] }⟩

abbrev ExplicitInterpretation := Lean.HashMap Declaration (Array FirstOrderValue × FirstOrderValue)

structure FirstOrderStructure where
  /-- Also called universes. -/
  domains : Array FirstOrderSort
  signature : Signature
  interp : ExplicitInterpretation

open Lean hiding Declaration

/- FIXME: make this match mypyvy output to a greater extent -/
instance : ToString FirstOrderStructure where
  toString s := Id.run (do
    let mut out := s!"\n"
    for dom in s.domains do
      out := out ++ s!"  {dom}\n"
    for (decl, (args, val)) in s.interp.toList do
      match decl with
      | Declaration.Constant c => out := out ++ s!"  {c.name} = {val}\n"
      | Declaration.Relation r => if val.isTrue then out := out ++ s!"  {r.name}{args.funcArgsString} = true\n"
      | Declaration.Function f => out := out ++ s!"  {f.name}{args.funcArgsString} = {val}\n"
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
    | .atom (.symb domName) => sorts := sorts.push (← findSortWithName (Name.mkSimple domName) struct)
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
    | .atom (.symb valName) => return FirstOrderValue.Uninterpreted s (Name.mkSimple valName)
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
    let sortName := Name.mkSimple sortName
    let sort: FirstOrderSort ← (match builtinInterpretedSorts.find? sortName with
    | some sortI => return .Interpreted sortI
    | none => do
      let mut elems : Array UninterpretedValue := #[]
      for elem in els do
        match elem with
        | .atom (.symb elemName) => elems := elems.push (Name.mkSimple elemName)
        | _ => throwError s!"malformed element: {elem}"
      return .Uninterpreted { name := sortName, size := elems.size, elements := elems }
    )
    trace[sauto.debug] s!"{sort}"
    struct := { struct with domains := struct.domains.push sort }

  -- (|constant| |s1| |a|),
  | .app #[(.atom (.symb "constant")), (.atom (.symb constName)), (.atom (.symb sortName))] => do
    let constName := Name.mkSimple constName
    let sortName := Name.mkSimple sortName
    let sort ← findSortWithName sortName struct
    let decl: ConstantDecl := { name := constName, sort := sort }
    trace[sauto.debug] s!"{decl}"
    struct := { struct with signature := { struct.signature with constants := struct.signature.constants.push decl } }

  -- (|relation| |rel| (|a| |a|)),
  | .app #[(.atom (.symb "relation")), (.atom (.symb relName)), (.app doms)] => do
    let relName := Name.mkSimple relName
    let doms ← findSortsArray doms struct
    let decl: RelationDecl := { name := relName, domain := doms }
    trace[sauto.debug] s!"{decl}"
    struct := { struct with signature := { struct.signature with relations := struct.signature.relations.push decl } }

  -- (|function| |f| (|a|) |Int|),
  | .app #[(.atom (.symb "function")), (.atom (.symb funName)), (.app doms), (.atom (.symb range))] => do
    let funName := Name.mkSimple funName
    let doms ← findSortsArray doms struct
    let range ← findSortWithName (Name.mkSimple range) struct
    let decl: FunctionDecl := { name := funName, domain := doms, range := range }
    trace[sauto.debug] s!"{decl}"
    struct := { struct with signature := { struct.signature with functions := struct.signature.functions.push decl } }

  -- (|interpret| |rel| (|a0| |a0|) |false|)
  -- (|interpret| |f| (|a0|) |-1|)
  -- (|interpret| |f| (|a1|) 0)
  | .app #[(.atom (.symb "interpret")), (.atom (.symb declName)), (.app args), val] => do
    let declName := Name.mkSimple declName
    let decl ← struct.findDecl declName
    let args ← getValueArray args decl.domain
    let val ← getValueOfSort val decl.range
    trace[sauto.debug] s!"interpret {declName} {args} {val}"
    struct := { struct with interp := struct.interp.insert decl (args, val) }

  | _ => throwError s!"(parseInstruction) malformed instruction: {inst}"
  return struct

def extractStructure (model : Sexpr) : MetaM FirstOrderStructure := do
  let mut struct : FirstOrderStructure := default
  let instructions ← extractInstructions model
  trace[sauto.debug] "instructions: {instructions}"
  for inst in instructions do
    struct ← parseInstruction inst struct
  return struct
