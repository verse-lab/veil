import Lean
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Util
import Mathlib.Data.FinEnum
import Veil.Util.Meta

import Veil.Core.Tools.Checker.Concrete.modelCheckerView
import ProofWidgets.Component.HtmlDisplay

import Lean.Parser.Term
open Lean Elab Command Veil
open Lean Elab Command

/-- Concatenate an array of arrays into a single array. -/
def concatArrays {α} (xs : Array (Array α)) : Array α :=
  xs.foldl (init := #[]) fun acc arr => acc ++ arr

/-- Collect all Veil variable binders from a module. -/
def Module.collectVeilVarsBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module)
  : m (Std.HashMap Name (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  mod.parameters.foldlM (init := {}) fun acc p => do
    let b ← p.binder
    pure <| acc.insert p.name b

structure BinderConfig where
  suffix : Option String := none

  instName : Option Name := none
  /-- Error message prefix if binder not found -/
  errPrefix : String := "No binder found"

/-- Collect binders from a module based on configuration. -/
def collectBinders [Monad m] [MonadQuotation m] [MonadError m]
    (mod : Veil.Module)
    (config : BinderConfig)
    : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  match config.instName with
  | some instName =>
    -- Collect instance binders (e.g., Ord, Enumeration)
    let instNamePostfix := instNameToPostfix instName
    let ids : Array Ident ← mod.sortIdents
    ids.mapM (fun t : Ident => do
      let name' := t.getId.appendAfter instNamePostfix
      `(bracketedBinder| [$(mkIdent name') : $(mkIdent instName) $t]))
  | none =>
    -- Collect explicit type binders with optional suffix
    let typeIdents : Array (TSyntax `ident) ← mod.sortIdents
    let varsBinders ← Module.collectVeilVarsBinders mod
    typeIdents.mapM fun t : (TSyntax `ident) => do
      let base := t.getId
      let key := match config.suffix with
                 | none => base
                 | some suf => base.appendAfter suf
      match varsBinders[key]? with
      | some b => pure b
      | none => throwError m!"{config.errPrefix} for type {t}"
where
  instNameToPostfix (instName : Name) : String :=
    match instName with
    | ``Ord       => "_ord"
    | ``Enumeration   => "_fin_enum"
    | ``Hashable  => "_hash"
    | ``ToJson    => "_to_json"
    | ``Repr      => "_repr"
    | _           => "_anonymous_inst"

/-- Given name of instance like `Ord`, return all the instance binders for all the types. -/
def Veil.Module.instBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module) (instName : Name)
  : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) :=
  collectBinders mod { instName := some instName }

/-- Structure containing all relevant terms for field representation. -/
structure FieldTerms where
  sortIdents : Array (TSyntax `ident)
  domainTerm : TSyntax `term
  codomainTerm : TSyntax `term
  fieldConcreteTerm : TSyntax `term

/-- Generate field representation terms for a given field identifier. -/
def mkFieldTerms [Monad m] [MonadQuotation m]
    (mod : Veil.Module)
    (fIdent : TSyntax `ident)
    : m FieldTerms := do
  let sortIdents ← mod.sortIdents
  let domainTerm : TSyntax `term ←
    `(term| ($(mkIdent `State.Label.toDomain):ident $sortIdents*) $fIdent:ident)
  let codomainTerm : TSyntax `term ←
    `(term| ($(mkIdent `State.Label.toCodomain):ident $sortIdents*) $fIdent:ident)
  let fieldConcreteTerm : TSyntax `term ←
    `(term| ($(mkIdent `FieldConcreteType):ident $sortIdents*) $fIdent:ident)
  pure { sortIdents, domainTerm, codomainTerm, fieldConcreteTerm }

/-- Generate propCmp (e.g., `TransCmp`, `LawfulEqCmp`) binder for a given type. -/
def propCmpBinder [Monad m] [MonadQuotation m] [MonadError m]
    (propName : Name)
    (sortIdent : Ident)
    : m (TSyntax `Lean.Parser.Term.bracketedBinder) := do
  let instNamePostfix := propNameToPostfix propName
  let name' := sortIdent.getId.appendAfter instNamePostfix
  `(bracketedBinder| [$(mkIdent name') : $(mkIdent propName) ($(mkIdent ``Ord.compare) ($(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $sortIdent)))])

where
  propNameToPostfix (propName : Name) : String :=
    match propName with
    | ``Std.TransCmp    => "_trans_cmp"
    | ``Std.LawfulEqCmp => "_lawful_cmp"
    | ``Std.OrientedCmp => "_oriented_cmp"
    | _                 => "_anonymous_prop_cmp"

/-- Common dsimp terms used across multiple instance derivations. -/
def commonDSimpTerms : Array Ident := #[
  mkIdent `FieldConcreteType,
  mkIdent `State.Label.toDomain,
  mkIdent `State.Label.toCodomain,
  mkIdent ``Veil.IteratedProd'
]

/-- Extended dsimp terms including additional common identifiers. -/
def extendedDSimpTerms : Array Ident :=
  commonDSimpTerms ++ #[
    mkIdent `instRepForFieldRepresentation,
    mkIdent `id
  ]

/-- Tactic generation strategy for instance derivation. -/
inductive TacticStrategy where
  | /-- Simple: dsimp + repeat infer_instance -/
    simple
  | /-- Cases with alternatives: cases f <;> first | tac1 | tac2 | ... -/
    casesWithAlternatives (alternatives : Array (TSyntax `tactic))
  | /-- Custom tactic syntax -/
    custom (tactic : TSyntax `tactic)

/-- Specification for which binders to collect for an instance. -/
inductive BinderSpec where
  | /-- Collect type explicit binders -/
    typeExplicit
  | /-- Collect DecidableEq binders -/
    decEq
  | /-- Collect Inhabited binders -/
    inhabited
  | /-- Collect instance binders for a specific typeclass -/
    inst (className : Name)

/-- Standard pattern for BEq: typeExplicit + decEq + Ord -/
def BinderSpec.forBEq : Array BinderSpec := #[.typeExplicit, .decEq, .inst ``Ord]

/-- Standard pattern for Hashable: typeExplicit + decEq + Ord + Hashable -/
def BinderSpec.forHashable : Array BinderSpec := #[.typeExplicit, .decEq, .inst ``Ord, .inst ``Hashable]

/-- Standard pattern for Repr: Ord + Repr -/
def BinderSpec.forRepr : Array BinderSpec := #[.inst ``Ord, .inst ``Repr]

/-- Standard pattern for LawfulFieldRepresentation: Enumeration + Ord -/
def BinderSpec.forLawful : Array BinderSpec := #[.inst ``Enumeration, .inst ``Ord]

/-- Standard pattern for Inhabited State: typeExplicit + Ord + Inhabited + DecEq + Enumeration -/
def BinderSpec.forInhabitedState : Array BinderSpec :=
  #[.typeExplicit, .inst ``Ord, .inhabited, .decEq, .inst ``Enumeration]

/-- Configuration for generic instance generation (simplified version). -/
structure SimpleInstanceConfig where
  /-- Name of the instance to generate -/
  instName : Name
  /-- Type class being instantiated (e.g., `BEq`, `Hashable`) -/
  className : Name
  /-- All binders for the instance -/
  binders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)
  /-- Terms to use in dsimp only [...] -/
  dsimpTerms : Array Ident := commonDSimpTerms
  /-- Sort identifiers for FieldConcreteType -/
  sortIdents : Array (TSyntax `ident)
  /-- Field label name -/
  fieldLabelName : Name

/-- Generate simple instance with dsimp + repeat infer_instance pattern. -/
def mkSimpleFieldConcreteTypeInstance (config : SimpleInstanceConfig) : CommandElabM (TSyntax `command) := do
  let classIdent := mkIdent config.className
  let instIdent := mkIdent config.instName
  let fieldLabelIdent := mkIdent config.fieldLabelName
  let binders := config.binders
  let sortIdents := config.sortIdents
  let dsimpTerms := config.dsimpTerms

  `(command |
    instance $instIdent:ident
      $[$binders]* : ($classIdent ($(mkIdent `FieldConcreteType):ident $sortIdents* $fieldLabelIdent)) := by
        dsimp only [$[$dsimpTerms:ident],*]
        repeat' (first | infer_instance | constructor)
  )

/-- Collect comprehensive binders for NextAct and executable list generation.
    Includes: Enumeration, Hashable, Ord, LawfulEqCmp, and TransCmp instances. -/
def Veil.Module.collectNextActBinders (mod : Veil.Module) : CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let sortIdents ← mod.sortIdents
  let finEnumInsts ← mod.instBinders ``Enumeration
  let hashInsts ← mod.instBinders ``Hashable
  let ordInsts ← mod.instBinders ``Ord
  let lawfulInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.LawfulEqCmp id)
  let transInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.TransCmp id)
  return finEnumInsts ++ hashInsts ++ ordInsts ++ lawfulInsts ++ transInsts


namespace Lean
/-- `t_Enum` is a type class. -/
def Name.toEnumClass (name : Name) : Name := name.appendAfter "_Enum"

/-- `t_isEnum` is an instance, where `t` is declared as an `enum` type. -/
def Name.toEnumInst (name : Name) : Name := name.appendAfter "_isEnum"

/-- Given a name `t`, return the name of its instance like `instPrefix_t`. -/
def Name.toInstName (name : Name) (instPrefix : String) : Name := name.appendBefore instPrefix
end Lean


/- TODO: Go through `import Veil.Frontend.DSL.Module.Util`, I believe there are more utility functions that can be used here -/
/- Collect all the mutable state fields. Without this step, may lead to `none` field name from `immutable` field. -/
def Veil.Module.stateFieldNames [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module)
  : m (Array Name) := do
  let sc := mod.mutableComponents
  return sc.map (·.name)


/- Collect all the mutable state fields of the given kind. -/
def Veil.Module.fieldNames [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module) (kind : StateComponentKind)
  : m (Array Name) := do
  let sc := mod.mutableComponents |>.filter (·.kind == kind)
  return sc.map (·.name)


/-- When a type is declared using `enum`, it will first elaborated to a typeclass,
then elaborated to syntax `instantiate _isEnum` and added into the `parameters`
field of `Veil.Module` with name postfix `_isEnum`.
Refer `Module.declareUninterpretedSort` for details.

The function collects all the type idents that are either enum types or non-enum
types based on the `isEnum` flag.
-/
def Veil.Module.typeIdents [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module) (isEnum : Bool)
  : m (Array (TSyntax `ident)) := do
  let paramNames : Array Name := mod.parameters.map (·.name)
  let isEnumType :=
    fun t => paramNames.contains (t.getId.toEnumInst) -- to a function
  let pred := if isEnum then isEnumType else fun t => not (isEnumType t)
  let ids ← mod.sortIdents
  return ids.filter pred


/-- Different from `Module.getStateBinders`, which used to collect Codomain and Domain.
* `res` is the `Domain`, while `base` is the `Codomain`/type of return value.
* For individual, base is always `#[]`.
* For relation, base is always `Bool`.
-/
def Veil.Module.getStateDomains [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module) : m (Array (Name × Array Term)) := do
  mod.signature.filterMapM fun sc => do
    match sc.mutability with
    | .mutable =>
      let (res, base) ← splitForallArgsCodomain (← sc.typeStx)
      match sc.kind with
      | .function   =>  return .some (sc.name, res)
      | _           =>  return .none
    | _ => return .none


def Veil.Module.collectVeilVarsBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module)
  : m (Std.HashMap Name (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  mod.parameters.foldlM (init := {}) fun acc p => do
    let b ← p.binder
    pure <| acc.insert p.name b

def Veil.Module.typeExplicitBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module)
  : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) :=
  collectBinders mod { errPrefix := "No type binder found" }

def Veil.Module.typeDecEqBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module)
  : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) :=
  collectBinders mod { suffix := some "_dec_eq", errPrefix := "No DecidableEq binder found" }

def Veil.Module.typeInhabitedBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module)
  : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) :=
  collectBinders mod { suffix := some "_inhabited", errPrefix := "No Inhabited binder found" }

/-- Collect binders according to BinderSpec specifications. -/
def Veil.Module.collectBindersFromSpecs (mod : Veil.Module) (specs : Array BinderSpec)
    : CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let binderGroups ← specs.mapM fun (spec : BinderSpec) =>
    match spec with
    | .typeExplicit => mod.typeExplicitBinders
    | .decEq => mod.typeDecEqBinders
    | .inhabited => mod.typeInhabitedBinders
    | .inst className => mod.instBinders className
  pure $ concatArrays binderGroups

/-- Collect propCmp binders (LawfulEqCmp and TransCmp) for all sort identifiers. -/
def Veil.Module.collectPropCmpBinders (mod : Veil.Module)
    : CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let sortIdents ← mod.sortIdents
  let lawfulInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.LawfulEqCmp id)
  let transInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.TransCmp id)
  pure $ lawfulInsts ++ transInsts

/-- Collect binders from specs plus propCmp binders. -/
def Veil.Module.collectBindersWithPropCmp (mod : Veil.Module) (specs : Array BinderSpec)
    : CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let basicBinders ← mod.collectBindersFromSpecs specs
  let propCmpBinders ← mod.collectPropCmpBinders
  pure $ basicBinders ++ propCmpBinders



def mkFieldRepTerms (mod : Veil.Module) (fIdent : TSyntax `ident)
  : CommandElabM (Array (TSyntax `ident) × TSyntax `term × TSyntax `term × TSyntax `term) := do
  let terms ← mkFieldTerms mod fIdent
  pure (terms.sortIdents, terms.domainTerm, terms.codomainTerm, terms.fieldConcreteTerm)

/-- Common dsimp terms for FieldRepresentation instances -/
def fieldRepDSimpTerms : Array Ident := #[
  mkIdent `FieldConcreteType,
  mkIdent `State.Label.toDomain,
  mkIdent `State.Label.toCodomain
]

/-- Generate a field representation instance with cases + first + exact alternatives pattern. -/
def mkFieldRepInstWithAlternatives
    (fIdent : TSyntax `ident)
    (instName className : Name)
    (binders : Array (TSyntax `Lean.Parser.Term.bracketedBinder))
    (domainTerm codomainTerm fieldConcreteTerm : TSyntax `term)
    (extraTypeArgs : Array (TSyntax `term))
    (dsimpTerms : Array Ident)
    (exactAlternatives : Array (TSyntax `term))
    : CommandElabM (TSyntax `command) := do
  -- Build the instance type
  let classIdent := mkIdent className
  let mut typeSyntax ← `(($classIdent ($domainTerm) ($codomainTerm) ($fieldConcreteTerm)))
  for extraArg in extraTypeArgs do
    typeSyntax ← `($typeSyntax ($extraArg))

  `(command |
    instance $(mkIdent instName):ident $[$binders]*
    ($fIdent : $(mkIdent `State.Label):ident)
    : $typeSyntax :=
    by
      cases $fIdent:ident <;>
      first
      | (dsimp only [$[$dsimpTerms:ident],*]; infer_instance)
      $[ | (exact $exactAlternatives) ]*
  )

/-- Helper to derive a single instance for a field. -/
def deriveFieldInstance (mod : Veil.Module) (fieldName : Name) (stateLabelName : Name) (sortIdents : Array (TSyntax `ident)) (className : Name) (instNamePrefix : String) (binderSpec : Array BinderSpec) (useFieldNameForInst : Bool := true) : CommandElabM (TSyntax `command) := do
  let binders ← mod.collectBindersFromSpecs binderSpec
  let instBaseName := if useFieldNameForInst then fieldName else stateLabelName
  mkSimpleFieldConcreteTypeInstance {
    instName := instBaseName.toInstName instNamePrefix
    className := className
    binders := binders
    sortIdents := sortIdents
    fieldLabelName := stateLabelName
  }

/-- Derive BEq and Hashable instances for a single label field. -/
def deriveBEqHashableInstsForLabelField (mod : Veil.Module) (fieldName : Name) : CommandElabM Unit := do
  let stateLabelName := Name.append `State.Label fieldName
  let sortIdents ← mod.sortIdents

  -- Derive BEq instance
  let beqInst ← deriveFieldInstance mod fieldName stateLabelName sortIdents
    ``BEq "instBEqForFieldConcreteType_" BinderSpec.forBEq
  trace[veil.debug] s!"deriving_BEq_FieldConcreteType : {← liftTermElabM <| Lean.PrettyPrinter.formatTactic beqInst}"
  elabVeilCommand beqInst

  -- Derive Hashable instance
  let hashableInst ← deriveFieldInstance mod fieldName stateLabelName sortIdents
    ``Hashable "instHashableForFieldConcreteType_" BinderSpec.forHashable (useFieldNameForInst := false)
  trace[veil.debug] s!"deriving_Hashable_FieldConcreteType : {← liftTermElabM <| Lean.PrettyPrinter.formatTactic hashableInst}"
  elabVeilCommand hashableInst
