module

public meta import Veil
public meta import Veil.Core.Tools.Synthesizer.Clause

/-!
# The vocabulary of a module

This file reads the symbols an invariant may mention off a Veil module: its relations,
individuals and functions, the constructors of its enum sorts, and the relations, constants and
functions of its typeclass instances.

## Main definitions

* `Veil.Synthesizer.Signature`: the vocabulary of a module.
* `Veil.Synthesizer.Signature.ofModule`: the vocabulary of a module, or an error naming the
  component outside the supported fragment.
* `Veil.Synthesizer.Signature.classFieldSpecs`: what each field of a typeclass is.

## Implementation notes

* The no-universal-invariant verdict is relative to the vocabulary, so a component the vocabulary
  cannot represent is an error rather than left out. The exceptions are class fields whose type
  lies outside the module's sorts, `Prop` and `Bool`, which are recorded in
  `Signature.excludedClassFields`, and ghost definitions, whose bodies the queries see.
* An enum sort is, to Veil, a sort parameter with a class of constants (its constructors) and
  axioms (they are distinct and exhaustive). The constructors are `Arg.enumConst` arguments; the
  class contributes no symbols, and its axioms reach every query through its instance binder.
-/

public meta section

initialize Lean.registerTraceClass `veil.synthesizer.debug

namespace Veil.Synthesizer
open Lean Elab Meta Veil

/-- The vocabulary of a module. -/
structure Signature where
  /-- The sort parameters, enum sorts included, in declaration order. -/
  sorts : Array SortName
  /-- The enum sorts, each with its constructors as a clause writes them. -/
  enums : Array (SortName × Array Name) := #[]
  /-- The mutable components: the fields of the state. -/
  stateSymbols : Array Symbol
  /-- The immutable components: the fields of the theory. -/
  theorySymbols : Array Symbol
  /-- The relations, constants and functions of the typeclass instances. -/
  classSymbols : Array Symbol
  /-- The typeclass instances: instance name, class name and sort arguments. -/
  instances : Array (Name × Name × Array SortName) := #[]
  /-- The keys of the class symbols that no axiom of their class mentions. -/
  freeClassSymbols : Array Name := #[]
  /-- The ghost definitions of the module, which are not symbols of the vocabulary. -/
  ghosts : Array Name := #[]
  /-- The class fields outside the vocabulary, as `inst.field`. -/
  excludedClassFields : Array Name := #[]
  /-- The numeric sorts that are the result of some component. -/
  numericSorts : Array SortName := #[]
  /-- The integer literals of the module's actions and assertions, with `0` and `1`. -/
  numerals : Array Int := #[]
deriving Repr, Inhabited

/-- What a field of a typeclass is. -/
inductive FieldSpec where
  /-- A predicate over the class's sort parameters, `Bool`-valued when `isBool`. -/
  | relation (argSorts : Array SortName) (isBool : Bool)
  /-- A constant of one of the sort parameters. -/
  | constant (sort : SortName)
  /-- A function between the sort parameters. -/
  | function (argSorts : Array SortName) (result : SortName)
  /-- A proposition about the fields it `mentions`. -/
  | axiom (mentions : Array Name)
  /-- A field whose type lies outside the sort parameters. -/
  | other
deriving Repr, BEq, Inhabited

/-- The symbol a field of instance `inst` contributes to the vocabulary, if any. -/
def FieldSpec.symbol? (inst field : Name) : FieldSpec → Option Symbol
  | .relation argSorts _ => some { name := field, origin := .field inst, argSorts }
  | .constant s =>
    some { name := field, origin := .field inst, isFunction := true, argSorts := #[s] }
  | .function argSorts s =>
    some { name := field, origin := .field inst, isFunction := true, argSorts := argSorts.push s }
  | .axiom _ | .other => none

namespace Signature

/-- The identifier a term is, if it is one. -/
def identName? (t : Term) : Option Name :=
  match t.raw with
  | .ident _ _ n _ => some n
  | _ => none

/-- All identifiers of a piece of syntax, in order. -/
partial def collectIdents : Syntax → Array Name
  | .ident _ _ n _ => #[n]
  | .node _ _ args => args.flatMap collectIdents
  | _ => #[]

/-- The natural-number literals of a piece of syntax. -/
partial def collectNumerals : Syntax → Array Int
  | .atom _ v => (v.toNat?.map fun n ↦ #[(n : Int)]).getD #[]
  | .node _ _ args => args.flatMap collectNumerals
  | _ => #[]

/-- The symbol of a component of the module, or an error for a component with an argument or
result type outside the module's sorts, `Bool` and the numeric sorts. -/
def componentSymbol (sorts : Array SortName) (sc : StateComponent) : MetaM Symbol := do
  let argSorts ← sc.domainTerms.mapM fun t ↦ match identName? t with
    | some n =>
      if sorts.contains n then pure n
      else if isNumericSort n then
        throwError "IC3: {sc.kind} {sc.name} takes an integer argument; model the index as an \
          ordered sort"
      else throwError "IC3: {sc.kind} {sc.name} has a non-sort argument type {t}"
    | none => throwError "IC3: {sc.kind} {sc.name} has a non-sort argument type {t}"
  let valueSort? : Option SortName := match identName? sc.codomainTerm with
    | some s => if sorts.contains s || isNumericSort s then some s else none
    | none => none
  match sc.kind, identName? sc.codomainTerm with
  | .relation, _ => return { name := sc.name, argSorts }
  | .individual, some `Bool => return { name := sc.name, argSorts := #[] }
  | .individual, _ =>
    let some s := valueSort?
      | throwError "IC3: individual {sc.name} has unsupported type {sc.codomainTerm}"
    return { name := sc.name, isFunction := true, argSorts := #[s] }
  | .function, some `Bool => return { name := sc.name, argSorts }
  | .function, _ =>
    let some s := valueSort?
      | throwError "IC3: function {sc.name} has unsupported result type {sc.codomainTerm}"
    return { name := sc.name, isFunction := true, argSorts := argSorts.push s }
  | .module, _ => throwError "IC3: child modules ({sc.name}) are not supported yet"

/-- The number of parameters of class `className`, after checking that it is a structure-based
class without parents whose fields have default binders, instantiated at `sortArgs`. -/
def checkClass (inst className : Name) (sortArgs : Array SortName) : MetaM Nat := do
  let env ← getEnv
  let some (.inductInfo info) := env.find? className
    | throwError "IC3: cannot resolve the class of instance {inst} ({className})"
  if info.numParams != sortArgs.size then
    throwError "IC3: instance {inst} : {className} has {sortArgs.size} sort argument(s) but the \
      class has {info.numParams} parameter(s)"
  let some structInfo := getStructureInfo? env className
    | throwError "IC3: {className} (instance {inst}) is not a structure-based class"
  if structInfo.fieldNames.any (isSubobjectField? env className · |>.isSome) then
    throwError "IC3: class {className} (instance {inst}) extends another class; not supported yet"
  forallTelescopeReducing (getStructureCtor env className).type fun xs _ ↦ do
    for x in xs.extract info.numParams xs.size do
      let decl ← x.fvarId!.getDecl
      unless decl.binderInfo == .default do
        throwError "IC3: field {decl.userName} of class {className} (instance {inst}) has a \
          non-default binder; not supported yet"
  return info.numParams

/-- What field `field` of class `className`, instantiated at `sortArgs`, is. A field over the
sort parameters into `Prop` or `Bool` is a relation, into a sort parameter a constant or a
function, and a field whose type is a proposition is an axiom. A relation or function with an
argument outside the sort parameters, or with an implicit argument, is an error: it is a symbol a
universal clause could use. -/
def fieldSpec (inst className : Name) (sortArgs : Array SortName) (numParams : Nat)
    (field : Name) : MetaM (Option FieldSpec) := do
  let env ← getEnv
  let some projFn := getProjFnForField? env className field | return none
  let some info := env.find? projFn | return none
  let fieldNames := (getStructureInfo? env className).map (·.fieldNames) |>.getD #[]
  forallTelescopeReducing info.type fun xs body ↦ do
    -- The binders are the class parameters, `self`, then the field's own arguments.
    if xs.size < numParams + 1 then return some .other
    let params := xs.extract 0 numParams
    let sortOf (e : Expr) : Option SortName := (params.idxOf? e).bind (sortArgs[·]?)
    let args ← (xs.extract (numParams + 1) xs.size).mapM (·.fvarId!.getDecl)
    let argSorts := args.filterMap (sortOf ·.type)
    let overSorts := argSorts.size == args.size
    let explicit := args.all (·.binderInfo.isExplicit)
    let check (what : String) : MetaM Unit := do
      unless overSorts do
        throwError "IC3: field {field} of {className} (instance {inst}) is a {what} over a \
          non-sort type; not supported"
      unless explicit do
        throwError "IC3: field {field} of {className} (instance {inst}) has an implicit \
          argument; not supported"
    if body.isProp || body == mkConst ``Bool then
      check "relation"
      return some (.relation argSorts (body == mkConst ``Bool))
    if let some s := sortOf body then
      if args.isEmpty then return some (.constant s)
      check "function"
      return some (.function argSorts s)
    if ← isProp body then
      -- An axiom names the fields it constrains through their projection functions.
      let mentions := fieldNames.filter fun f ↦
        (getProjFnForField? env className f).any fun pf ↦ (info.type.find? (·.isConstOf pf)).isSome
      return some (.axiom mentions)
    return some .other

/-- What each field of class `className`, instantiated at `sortArgs` for instance `inst`, is. -/
def classFieldSpecs (inst className : Name) (sortArgs : Array SortName) :
    MetaM (Array (Name × FieldSpec)) := do
  let numParams ← checkClass inst className sortArgs
  let some structInfo := getStructureInfo? (← getEnv) className | return #[]
  structInfo.fieldNames.filterMapM fun field ↦ do
    return (← fieldSpec inst className sortArgs numParams field).map (field, ·)

/-- The constructors of the enum sort `sort`, in declaration order, as a clause writes them: by
their own name, or through the enum's class when the module declares the same name. -/
def enumConstructors (mod : Veil.Module) (sort : SortName) : MetaM (Array Name) := do
  let typeName := mod.name ++ Name.toEnumConcreteTypeName sort
  let env ← getEnv
  let some (.inductInfo info) := env.find? typeName
    | throwError "IC3: cannot find the constructors of enum sort {sort} ({typeName})"
  return info.ctors.toArray.map fun c ↦
    let ctor := c.updatePrefix .anonymous
    if env.contains (mod.name ++ ctor) then Name.toEnumClass sort ++ ctor else ctor

/-- The ghost definitions of a module, by name. -/
def ghostDefinitions (mod : Veil.Module) : Array Name :=
  let names := mod._derivedDefinitions.toList.filterMap fun (n, dd) ↦
    match dd.kind with
    | .ghost _ | .theoryGhost _ => some (n.replacePrefix mod.name .anonymous)
    | _ => none
  names.toArray.qsort fun a b ↦ a.toString < b.toString

/-- The symbols of a typeclass parameter of the module, with the keys of those no axiom mentions
and the fields outside the vocabulary; `none` for a parameter that contributes nothing. -/
def instanceSymbols (sorts : Array SortName) (p : Veil.Parameter) :
    MetaM (Option ((Name × Name × Array SortName) × Array Symbol × Array Name × Array Name)) := do
  -- The class is the first identifier of the binder type; the module sorts after it are its
  -- arguments, in order.
  let idents := collectIdents p.type.raw
  let some classIdent := idents[0]? | throwError "IC3: cannot read the class of instance {p.name}"
  let className ← try resolveGlobalConstNoOverload (mkIdent classIdent)
    catch _ => throwError "IC3: cannot resolve the class of instance {p.name} ({classIdent})"
  if [``Inhabited, ``Nonempty, ``DecidableEq].contains className then return none
  unless isStructure (← getEnv) className do
    throwError "IC3: {className} (instance {p.name}) is not a structure-based class; not supported"
  let sortArgs := (idents.extract 1 idents.size).filter sorts.contains
  let specs ← classFieldSpecs p.name className sortArgs
  let constrained := specs.flatMap fun (_, spec) ↦ match spec with
    | .axiom mentions => mentions
    | _ => #[]
  let syms := specs.filterMap fun (field, spec) ↦ (spec.symbol? p.name field).map (field, ·)
  let outside := specs.filterMap fun (field, spec) ↦
    if spec matches .other then some field else none
  for field in outside do
    trace[veil.synthesizer.debug] "IC3: field {field} of {className} (instance {p.name}) is \
      outside the vocabulary: neither a relation, a sort constant nor a function between sorts"
  let free := syms.filterMap fun (field, sym) ↦ if constrained.contains field then none else sym.key
  return some ((p.name, className, sortArgs), syms.map (·.2), free, outside.map (p.name ++ ·))

/-- Whether `n` has the shape of a clause variable, `x0`, `x1`, …. -/
def isVarName (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "x" && s.length > 1 && (s.drop 1).all Char.isDigit

/-- The vocabulary of a module. Child modules, module parameters and classes outside
`classFieldSpecs`' shape are errors. -/
def ofModule (mod : Veil.Module) : MetaM Signature := do
  let sorts := mod.sortParams.map (·.1.name)
  let enums ← (mod.sortParams.filter (·.2 == .enumSort)).mapM fun (p, _) ↦
    return (p.name, ← enumConstructors mod p.name)
  let mut stateSymbols := #[]
  let mut theorySymbols := #[]
  for sc in mod.signature do
    match sc.mutability with
    | .mutable => stateSymbols := stateSymbols.push (← componentSymbol sorts sc)
    | .immutable => theorySymbols := theorySymbols.push (← componentSymbol sorts sc)
    | .inherit => throwError "IC3: child modules ({sc.name}) are not supported yet"
  -- The instance of an enum's class contributes nothing: its constants are the constructors.
  let enumInsts := enums.map (Name.toEnumInst ·.1)
  let mut sig : Signature := { sorts, enums, stateSymbols, theorySymbols, classSymbols := #[] }
  for p in mod.parameters do
    match p.kind with
    | .moduleTypeclass .sortAssumption | .moduleTypeclass .userDefined =>
      if enumInsts.contains p.name then continue
      let some (inst, syms, free, excluded) ← instanceSymbols sorts p | continue
      sig := { sig with
        classSymbols := sig.classSymbols ++ syms, instances := sig.instances.push inst
        freeClassSymbols := sig.freeClassSymbols ++ free
        excludedClassFields := sig.excludedClassFields ++ excluded }
    | .userParameter => throwError "IC3: module parameter {p.name} is not supported yet"
    -- Veil's own parameters and assumptions declare no symbol over the module's sorts.
    | .mode | .sort _ | .fieldConcreteType | .environmentState | .backgroundTheory
    | .definitionParameter .. | .theoryArg | .stateArg
    | .moduleTypeclass .backgroundTheory | .moduleTypeclass .environmentState
    | .moduleTypeclass .fieldRepresentation | .moduleTypeclass .lawfulFieldRepresentation => pure ()
  -- A module name of the shape `x0` would be captured by the variables of a rendered clause.
  let names := sorts ++ (stateSymbols ++ theorySymbols).map (·.name) ++
    mod.parameters.map (·.name) ++ enums.flatMap (·.2)
  if let some n := names.find? isVarName then
    throwError "IC3: the name {n} clashes with clause variable names (x0, x1, …); rename it"
  let numericSorts := ((stateSymbols ++ theorySymbols).filter (·.isNumeric)).map (·.argSorts.back!)
    |>.toList.eraseDups.toArray
  let numerals := if numericSorts.isEmpty then #[] else
    let raw := mod.procedures.flatMap (collectNumerals ·.code.raw) ++
      mod.assertions.flatMap (collectNumerals ·.term.raw)
    (#[0, 1] ++ raw).toList.eraseDups.toArray.qsort (· < ·)
  return { sig with ghosts := ghostDefinitions mod, numericSorts, numerals }

/-- Whether the vocabulary has a function symbol with arguments or an enum sort, beyond the
constants and relations Proposition 5.6 of [Karbyshev et al.] is stated for. -/
def extendsPaper (sig : Signature) : Bool :=
  !sig.enums.isEmpty ||
    (sig.stateSymbols ++ sig.theorySymbols ++ sig.classSymbols).any fun f ↦
      f.isFunction && f.arity > 0

/-- The heads of the assignments `f a b := e` and `f a b := *` of a `do` block, nested blocks
included. -/
partial def assignmentHeads : Syntax → Array Name
  | stx@(.node _ kind args) =>
    if kind == ``Lean.Parser.Term.doReassign || kind == ``Veil.havocAssignment then
      (collectIdents stx)[0]?.toArray
    else args.flatMap assignmentHeads
  | _ => #[]

/-- The mutable components that `after_init` never assigns, read syntactically. -/
def unassignedByInit (mod : Veil.Module) : Array Name :=
  match mod.procedures.find? (·.info matches .initializer) with
  | none => #[]
  | some p =>
    let heads := assignmentHeads p.code.raw
    (mod.signature.filter fun sc ↦ sc.mutability matches .mutable && !heads.contains sc.name).map
      (·.name)

end Signature

end Veil.Synthesizer
