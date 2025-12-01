import Lean
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Util
import Mathlib.Data.FinEnum

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

/-- Configuration for collecting binders from a module. -/
structure BinderConfig where
  /-- Optional suffix to append to type names (e.g., "_dec_eq", "_inhabited") -/
  suffix : Option String := none
  /-- Optional instance name to collect (e.g., `Ord`, `FinEnum`, `Hashable`) -/
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
    -- Collect instance binders (e.g., Ord, FinEnum)
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
    | ``FinEnum   => "_fin_enum"
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

/-- Standard pattern for LawfulFieldRepresentation: FinEnum + Ord -/
def BinderSpec.forLawful : Array BinderSpec := #[.inst ``FinEnum, .inst ``Ord]

/-- Standard pattern for Inhabited State: typeExplicit + Ord + Inhabited + DecEq + FinEnum -/
def BinderSpec.forInhabitedState : Array BinderSpec :=
  #[.typeExplicit, .inst ``Ord, .inhabited, .decEq, .inst ``FinEnum]

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
    Includes: FinEnum, Hashable, Ord, LawfulEqCmp, and TransCmp instances. -/
def Veil.Module.collectNextActBinders (mod : Veil.Module) : CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let sortIdents ← mod.sortIdents
  let finEnumInsts ← mod.instBinders ``FinEnum
  let hashInsts ← mod.instBinders ``Hashable
  let ordInsts ← mod.instBinders ``Ord
  let lawfulInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.LawfulEqCmp id)
  let transInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.TransCmp id)
  return finEnumInsts ++ hashInsts ++ ordInsts ++ lawfulInsts ++ transInsts
