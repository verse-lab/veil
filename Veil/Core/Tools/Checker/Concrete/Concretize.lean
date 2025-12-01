import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Action.Elaborators
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Action.Extract
import Veil.Frontend.DSL.State.Repr
import Veil.Core.Tools.Checker.Concrete.State
import Veil.Core.Tools.Checker.Concrete.ConcretizeUtil

import Mathlib.Data.FinEnum
import Mathlib.Tactic.ProxyType

import Veil.Util.Meta

import Veil.Core.Tools.Checker.Concrete.modelCheckerView
import ProofWidgets.Component.HtmlDisplay

import Lean.Parser.Term
open Lean Elab Command Veil



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



syntax (name := abbrevFieldConcreteType) "specify_FieldConcreteType" : command


/-
How to assembly `match...with` syntax
https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/.E2.9C.94.20Optional.20expected.20type.20in.20.60elab_rules.60/near/425853362
-/
/-- Generate the concrete type for a field based on its kind. -/
def fieldKindToType (domainTerm codomainTerm : TSyntax `term) (kind : StateComponentKind)
  : CommandElabM (TSyntax `term) := do
  let mapKeyTerm ← `(term| ($(mkIdent ``Veil.IteratedProd') <| $domainTerm))
  match kind with
  | .individual => pure codomainTerm
  | .relation => `(term| $(mkIdent ``Std.TreeSet) $mapKeyTerm)
  | .function => `(term| $(mkIdent ``Veil.TotalTreeMap) $mapKeyTerm $codomainTerm)
  | .module => throwError "Module kind is not supported in FieldConcreteType"

/-- Generate a match case for FieldConcreteType definition. -/
def fieldsToMatchType (mod : Veil.Module) (fieldName : Name) (kind : StateComponentKind)
  : CommandElabM (TSyntax `Lean.Parser.Term.matchAltExpr) := do
  let caseIdent := mkIdent <| Name.append `State.Label fieldName
  let terms ← mkFieldTerms mod caseIdent
  let caseBody ← fieldKindToType terms.domainTerm terms.codomainTerm kind
  `(Lean.Parser.Term.matchAltExpr| | $caseIdent:ident => $caseBody:term)


/-- Generate match cases for all fields of a given kind. -/
private def mkMatchCasesForKind (mod : Veil.Module) (kind : StateComponentKind)
    : CommandElabM (Array (TSyntax `Lean.Parser.Term.matchAltExpr)) := do
  let names ← mod.fieldNames kind
  names.mapM fun name => fieldsToMatchType mod name kind

@[command_elab abbrevFieldConcreteType]
def specifyFieldConcreteType : CommandElab := fun _stx => do
  let mod ← getCurrentModule
  let typeBinders ← mod.typeExplicitBinders
  let ordInst ← mod.instBinders ``Ord
  let labelBinder ← `(bracketedBinder| ($(mkIdent `f) : $(mkIdent `State.Label)))
  let allBinders := typeBinders ++ ordInst ++ [labelBinder]

  let indivCases ← mkMatchCasesForKind mod .individual
  let relCases ← mkMatchCasesForKind mod .relation
  let funCases ← mkMatchCasesForKind mod .function

  let fieldConcreteTypeCmd : TSyntax `command ←
    `(command|
        abbrev $(mkIdent `FieldConcreteType):ident
          $[$allBinders]* : Type :=
            match $(mkIdent `f):ident with
              $indivCases:matchAlt*
              $relCases:matchAlt*
              $funCases:matchAlt*
    )
  trace[veil.debug] s!"specify_FieldConcreteType : {← liftTermElabM <| Lean.PrettyPrinter.formatTactic fieldConcreteTypeCmd}"
  elabVeilCommand fieldConcreteTypeCmd


private def mkFieldRepTerms (mod : Veil.Module) (fIdent : TSyntax `ident)
  : CommandElabM (Array (TSyntax `ident) × TSyntax `term × TSyntax `term × TSyntax `term) := do
  let terms ← mkFieldTerms mod fIdent
  pure (terms.sortIdents, terms.domainTerm, terms.codomainTerm, terms.fieldConcreteTerm)

/-- Common dsimp terms for FieldRepresentation instances -/
private def fieldRepDSimpTerms : Array Ident := #[
  mkIdent `FieldConcreteType,
  mkIdent `State.Label.toDomain,
  mkIdent `State.Label.toCodomain
]

/-- Generate a field representation instance with cases + first + exact alternatives pattern. -/
private def mkFieldRepInstWithAlternatives
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
private def deriveFieldInstance (mod : Veil.Module) (fieldName : Name) (stateLabelName : Name) (sortIdents : Array (TSyntax `ident)) (className : Name) (instNamePrefix : String) (binderSpec : Array BinderSpec) (useFieldNameForInst : Bool := true) : CommandElabM (TSyntax `command) := do
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



/-- Unified command to derive both BEq and Hashable instances for FieldConcreteType. -/
syntax (name := derivingBEqHashableFieldConcreteTypeCmd) "deriving_BEq_Hashable_FieldConcreteType" : command

@[command_elab derivingBEqHashableFieldConcreteTypeCmd]
def deriveBEqHashableInstForFieldConcreteType : CommandElab := fun _stx => do
  let mod ← getCurrentModule
  let labelFields ← mod.stateFieldNames
  for lfIdent in labelFields do
    deriveBEqHashableInstsForLabelField mod lfIdent


def mkProdFromArray (xs : Array (TSyntax `term)) : TermElabM (TSyntax `term) := do
  match xs.toList with
  | []      =>  `(term| Unit)
  | [t]     =>  return ←`(term | ($t))
  | t :: ts =>  ts.foldlM (init := t) fun acc b => `(term| ($acc × ($b)))

syntax (name := deriveRepInstForFieldRepr) "deriving_rep_FieldRepresentation" : command

/-- Derive both FieldRepresentation and LawfulFieldRepresentation instances together.
This avoids duplication since they share common setup and LawfulFieldRepresentation depends on FieldRepresentation. -/
def deriveRepAndLawfulInstsForFieldRep (mod : Veil.Module) : CommandElabM Unit := do
  /- Make sure `deriveFinEnumInstForToDomain` has been run before this command. -/
  let fIdent := mkIdent `f
  let (repSorts, domainTerm, codomainTerm, fieldConcreteTerm) ← mkFieldRepTerms mod fIdent

  -- Derive FieldRepresentation instance
  let mut repBinders ← mod.collectBindersFromSpecs #[.typeExplicit, .inst ``FinEnum, .inst ``Ord]
  -- Add TransCmp for the prod type of Domain for `.function` fields
  let stateDomains ← mod.getStateDomains
  for (_, doms) in stateDomains do
    let productDomain ← mkProdFromArray doms |> liftTermElabM
    let transInst ← `(bracketedBinder| [$(mkIdent ``Std.TransCmp) ($(mkIdent ``Ord.compare) ( $(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $productDomain) ))])
    repBinders := repBinders.push transInst

  -- Build exact alternatives for FieldRepresentation
  let repAlt1 ← `($(mkIdent ``instFinsetLikeAsFieldRep) $(mkIdent ``Veil.IteratedProd'.equiv) (($(mkIdent `instFinEnumForToDomain) $repSorts*) _))
  let repAlt2 ← `($(mkIdent ``instTotalMapLikeAsFieldRep) $(mkIdent ``Veil.IteratedProd'.equiv) (($(mkIdent `instFinEnumForToDomain) $repSorts*) _))
  let repInst ← mkFieldRepInstWithAlternatives fIdent
    `instRepForFieldRepresentation ``FieldRepresentation
    repBinders domainTerm codomainTerm fieldConcreteTerm
    #[] fieldRepDSimpTerms #[repAlt1, repAlt2]
  trace[veil.debug] s!"deriving_rep_fieldRepresentation : {← liftTermElabM <| Lean.PrettyPrinter.formatTactic repInst}"
  elabVeilCommand repInst

  -- Derive LawfulFieldRepresentation instance
  let lawfulBinders ← mod.collectBindersWithPropCmp BinderSpec.forLawful
  -- Build the extra type argument: the FieldRepresentation instance
  let repInstArg ← `(( ($(mkIdent `instRepForFieldRepresentation):ident $repSorts*) $fIdent ))
  -- Build exact alternative for LawfulFieldRepresentation
  let lawfulAlt ← `($(mkIdent ``Veil.instFinsetLikeLawfulFieldRep) $(mkIdent ``Veil.IteratedProd'.equiv) (($(mkIdent `instFinEnumForToDomain) $repSorts*) _))
  let lawfulInst ← mkFieldRepInstWithAlternatives fIdent
    `instLawfulFieldRepForFieldRepresenzrtation ``Veil.LawfulFieldRepresentation
    lawfulBinders domainTerm codomainTerm fieldConcreteTerm
    #[repInstArg] extendedDSimpTerms #[lawfulAlt]

  trace[veil.debug] s!"deriving_lawful_fieldRepresentation : {← liftTermElabM <| Lean.PrettyPrinter.formatTactic lawfulInst}"
  elabVeilCommand lawfulInst

@[command_elab deriveRepInstForFieldRepr]
def deriveRepInstForFieldReprCmd : CommandElab := fun _stx => do
  let mod ← getCurrentModule
  deriveRepAndLawfulInstsForFieldRep mod


-- syntax (name := deriveLawfulInstForFieldRepr) "deriving_lawful_FieldRepresentation" : command
-- @[command_elab deriveLawfulInstForFieldRepr]
-- def deriveLawfulInstForFieldReprCmd : CommandElab := fun _stx => do
--   let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
--   deriveRepAndLawfulInstsForFieldRep mod


syntax (name := derivingInhabitedInst) "deriving_Inhabited_State" : command

def deriveInhabitedInstForState (mod : Veil.Module) : CommandElabM (TSyntax `command) := do
  let sortIdents ← mod.sortIdents
  /- It's a little bit complex to derive the required minimal instances for this type. -/
  let binders ← mod.collectBindersWithPropCmp BinderSpec.forInhabitedState

  let stateIdent := mkIdent `State
  let fieldConcreteTypeIdent := mkIdent `FieldConcreteType
  return ←
    `(command |
      instance $(mkIdent `instInhabitedFieldConcreteTypeForState):ident $[$binders]*
      : $(mkIdent ``Inhabited) ( $stateIdent ( $fieldConcreteTypeIdent:ident $(sortIdents)* ) ) :=
      by
        constructor; constructor <;>
        dsimp only [$[$commonDSimpTerms:ident],*] <;>
        try exact $(mkIdent ``default)
    )

@[command_elab derivingInhabitedInst]
def deriveInhabitedInstCmd : CommandElab := fun stx => do
  let mod ← getCurrentModule
  let instCmd ← deriveInhabitedInstForState mod
  trace[veil.debug] s!"deriving_inhabited_state : {← liftTermElabM <|Lean.PrettyPrinter.formatTactic instCmd}"
  elabVeilCommand instCmd



syntax (name := genNextActCommand) "gen_NextAct" : command

/-- Generate both NextAct specialization and executable list commands. -/
def genNextActCommands (mod : Veil.Module) : CommandElabM Unit := do
  let binders ← mod.collectNextActBinders
  -- Generate NextAct specialization
  let nextActCmd ← `(command |
    attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet] $(mkIdent `instFinEnumForToDomain) in
    #specialize_nextact with $(mkIdent `FieldConcreteType)
    injection_begin
      $[$binders]*
    injection_end => $(mkIdent `NextAct'))
  trace[veil.debug] "gen_NextAct: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic nextActCmd}"
  elabVeilCommand nextActCmd

  -- Generate executable list
  let execListCmd ← `(command |
    #gen_executable_list! log_entry_being $(mkIdent ``Std.Format)
    targeting $(mkIdent `NextAct')
    injection_begin
      $[$binders]*
    injection_end)
  trace[veil.debug] "gen_executable_NextAct: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic execListCmd}"
  elabVeilCommand execListCmd

@[command_elab genNextActCommand]
def elabGenNextAct : CommandElab := fun stx => do
  let mod ← getCurrentModule
  genNextActCommands mod


-- syntax (name := genExecutableNextAct) "gen_executable_NextAct" : command

-- @[command_elab genExecutableNextAct]
-- def elabGenExecutableNextAct : CommandElab := fun stx => do
--   let mod ← getCurrentModule
--   genNextActCommands mod

/-- Code from Qiyuan. Generate inductive type and instances for `enum` typeclass. -/
def deriveEnumInstance (name : Name) : CommandElabM Unit := do
  let clsName ← resolveGlobalConstNoOverloadCore name.toEnumClass
  let .some info := getStructureInfo? (← getEnv) clsName | throwError "no such structure {clsName}"
  let fields := info.fieldNames.pop.pop
  trace[veil.debug] "info.fieldName: {info.fieldNames}"
  let ctors : Array (TSyntax ``Lean.Parser.Command.ctor) ←
    fields.mapM fun fn => `(Lean.Parser.Command.ctor| | $(mkIdent fn):ident )
  trace[veil.debug] "fields: {fields}"
  let defineIndTypeCmd ← do
    if ctors.size > 0 then
      `(inductive $(mkIdent name) where $[$ctors]* deriving $(mkIdent ``DecidableEq), $(mkIdent ``Repr), $(mkIdent ``Inhabited), $(mkIdent ``Nonempty))
    else
      `(inductive $(mkIdent name) where deriving $(mkIdent ``DecidableEq), $(mkIdent ``Repr))
  let instClauses ←
    fields.mapM fun fn => `(Lean.Parser.Term.structInstField| $(mkIdent fn):ident := $(mkIdent <| name ++ fn):ident )
  let completeRequirement := info.fieldNames.back!
  let distinctRequirement := info.fieldNames.pop.back!
  let proof1 ← `(Lean.Parser.Term.structInstField| $(mkIdent distinctRequirement):ident := (by (first | decide | grind)) )
  let proof2 ← do
    let x := mkIdent `x
    `(Lean.Parser.Term.structInstField| $(mkIdent completeRequirement):ident := (by intro $x:ident ; cases $x:ident <;> (first | decide | grind)) )
  let instClauses := instClauses.push proof1 |>.push proof2
  let instantiateCmd ←
    `(instance : $(mkIdent clsName) $(mkIdent name) where $[$instClauses]*)
  let allConstructors ← do
    let arr := fields.map fun fn => (mkIdent <| name ++ fn)
    `(term| [ $arr,* ] )
  let instantiateFinEnumCmd ←
    `(instance : $(mkIdent ``FinEnum) $(mkIdent name) :=
      $(mkIdent ``FinEnum.ofList) $allConstructors (by simp ; exact $(mkIdent <| clsName ++ completeRequirement)))
  elabCommand defineIndTypeCmd
  trace[veil.debug] "defineIndTypeCmd: {defineIndTypeCmd}"
  elabCommand instantiateCmd
  trace[veil.debug] "instantiateCmd: {instantiateCmd}"
  elabCommand instantiateFinEnumCmd
  trace[veil.debug] "instantiateFinEnumCmd: {instantiateFinEnumCmd}"


def deriveEnumOrdHashable (name : Name) : CommandElabM Unit := do
  let ordInst ← `(command|
    instance $(mkIdent <| Name.appendBefore name "instOrd"):ident : $(mkIdent ``Ord) $(mkIdent name) where
      $(mkIdent `compare):ident $(mkIdent `s1):ident $(mkIdent `s2):ident :=
        $(mkIdent ``compare) $(mkIdent `s1.toCtorIdx) $(mkIdent `s2.toCtorIdx))
  trace[veil.debug] "ordInst: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic ordInst}"
  elabVeilCommand ordInst

  let hashableInst ← `(command|
    instance $(mkIdent <| Name.appendBefore name "instHashable"):ident : $(mkIdent ``Hashable) $(mkIdent name) where
      $(mkIdent `hash):ident $(mkIdent `s):ident :=
        $(mkIdent ``hash) $(mkIdent `s.toCtorIdx))
  trace[veil.debug] "hashableInst: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic hashableInst}"
  elabVeilCommand hashableInst

elab "deriving_ord_hashable_for_enum" name:ident : command => do
  let name := name.getId
  deriveEnumOrdHashable name

def deriveEnumPropCmpInsts (name : Name) : CommandElabM Unit := do
  let orientedCmp ← `(command|
    instance : $(mkIdent ``Std.OrientedCmp) ($(mkIdent ``Ord.compare) ( $(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $(mkIdent name)) )) := by
      apply $(mkIdent ``Std.OrientedCmp.mk)
      unfold $(mkIdent `compare) $(mkIdent `inferInstanceAs) $(mkIdent <| Name.appendBefore name "instOrd")
      intro $(mkIdent `a) $(mkIdent `b); cases $(mkIdent `a):ident <;>
        cases $(mkIdent `b):ident <;> rfl)
  elabVeilCommand orientedCmp

  let transCmp ← `(command|
    instance : $(mkIdent ``Std.TransCmp) ($(mkIdent ``Ord.compare) ( $(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $(mkIdent name)) )) := by
      apply $(mkIdent ``Std.TransCmp.mk)
      unfold $(mkIdent `compare) $(mkIdent `inferInstanceAs) $(mkIdent <| Name.appendBefore name "instOrd")
      decide)
  elabVeilCommand transCmp

  let lawfulCmp ← `(command|
    instance : $(mkIdent ``Std.LawfulEqCmp) ($(mkIdent ``Ord.compare) ( $(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $(mkIdent name)) )) := by
      apply $(mkIdent ``Std.LawfulEqCmp.mk)
      unfold $(mkIdent `compare) $(mkIdent `inferInstanceAs) $(mkIdent <| Name.appendBefore name "instOrd")
      intro $(mkIdent `a) $(mkIdent `b); cases $(mkIdent `a):ident <;>
        cases $(mkIdent `b):ident <;> simp)
  elabVeilCommand lawfulCmp


syntax (name := deriveEnumInsts) "deriving_Enum_Insts" : command
@[command_elab deriveEnumInsts]
def elabDeriveEnumInsts : CommandElab := fun stx => do
  match stx with
  | `(command| deriving_Enum_Insts) =>
    let mod ← getCurrentModule
    let enumTypeIdents ← mod.typeIdents (isEnum := true)
    for t in enumTypeIdents do
      let name := t.getId
      trace[veil.debug] s!"Processing enum type: {name}"
      deriveEnumInstance name
      deriveEnumOrdHashable name
      deriveEnumPropCmpInsts name
  | _ => throwError "unrecognized command {stx}"


elab "deriving_propCmp_for_enum" name:ident : command => do
  let name := name.getId
  deriveEnumPropCmpInsts name



def deriveReprInstForFieldConcreteType (mod : Veil.Module) (stateLabelName : Name) : CommandElabM (TSyntax `command) := do
  let sortIdents ← mod.sortIdents
  let binders ← mod.collectBindersFromSpecs BinderSpec.forRepr
  mkSimpleFieldConcreteTypeInstance {
    instName := Name.appendBefore stateLabelName "instReprForFieldConcreteType_"
    className := ``Repr
    binders := binders
    sortIdents := sortIdents
    fieldLabelName := stateLabelName
  }

syntax (name := derivingReprFieldConcreteTypeCmd) "deriving_Repr_FieldConcreteType" : command
@[command_elab derivingReprFieldConcreteTypeCmd]
def deriveReprInstForFieldConcreteTypeCmd : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
  let labelFields ← mod.stateFieldNames
  for lfIdent in labelFields do
    let lfName := Name.append `State.Label lfIdent
    let lfc ← deriveReprInstForFieldConcreteType mod lfName
    elabVeilCommand lfc



def deriveToJsonInstDomain (mod : Veil.Module) (toDomain : Bool := true): CommandElabM Unit := do
  let typeBinders ← mod.typeExplicitBinders
  let ordInst ← mod.instBinders ``ToJson
  let labelBinder ← `(bracketedBinder| ($(mkIdent `f) : $(mkIdent `State.Label)) )
  let allBinders := typeBinders ++ ordInst ++ [labelBinder]

  let instToJsonName := if toDomain then `instToJsonForToDomain' else `instToJsonForToCodomain

  let stateLabelDomain ←
    if toDomain then
      `(term| $(mkIdent `State.Label.toDomain) $(← mod.sortIdents)*)
    else
      `(term| $(mkIdent `State.Label.toCodomain) $(← mod.sortIdents)*)

  let instTargetTy ←
    if toDomain then
      `(term | ($(mkIdent ``ToJson) ($(mkIdent ``IteratedProd'):ident <| ($stateLabelDomain) $(mkIdent `f))))
    else
      `(term | ($(mkIdent ``ToJson) (($stateLabelDomain) $(mkIdent `f))))

  let dsimpTerms : Array (TSyntax `ident) := #[
    mkIdent ``IteratedProd',
    mkIdent ``List.foldr,
    mkIdent `State.Label.toDomain,
    mkIdent `State.Label.toCodomain
  ]

  let toJsonCmd : TSyntax `command ←
    `(command|
        instance $(mkIdent instToJsonName):ident
          $[$allBinders]* : $instTargetTy := by
            cases $(mkIdent `f):ident <;>
              dsimp only [$[$dsimpTerms:ident],*]
              <;> infer_instance
    )
  trace[veil.debug] s!"toJsonCmd: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic toJsonCmd}"
  elabVeilCommand toJsonCmd




/- Derive `Ord` instance for both `toDomain` and `toCodomain` -/
def deriveOrdInstForDomain (mod : Veil.Module) (toDomain : Bool := true) : CommandElabM Unit := do
  let typeBinders ← mod.typeExplicitBinders
  let ordInst ← mod.instBinders ``Ord
  let labelBinder ← `(bracketedBinder| ($(mkIdent `f) : $(mkIdent `State.Label)) )
  let allBinders := typeBinders ++ ordInst ++ [labelBinder]

  let instName := if toDomain then `instOrdForToDomain' else `instOrdForToCodomain

  let stateLabelDomain ←
    if toDomain then
      `(term| $(mkIdent `State.Label.toDomain) $(← mod.sortIdents)*)
    else
      `(term| $(mkIdent `State.Label.toCodomain) $(← mod.sortIdents)*)

  let instTargetTy ←
    if toDomain then
      `(term| ($(mkIdent ``Ord) ($(mkIdent ``IteratedProd'):ident <| ($stateLabelDomain) $(mkIdent `f))))
    else
      `(term| ($(mkIdent ``Ord) (($stateLabelDomain) $(mkIdent `f))))

  let dsimpTerms : Array (TSyntax `ident) := #[
    mkIdent ``IteratedProd',
    mkIdent ``List.foldr,
    mkIdent `State.Label.toDomain,
    mkIdent `State.Label.toCodomain
  ]

  let ordCmd : TSyntax `command ←
    `(command|
        instance $(mkIdent instName):ident
          $[$allBinders]* : $instTargetTy := by
            cases $(mkIdent `f):ident <;>
              dsimp only [$[$dsimpTerms:ident],*]
              <;>
              infer_instance
    )
  elabVeilCommand ordCmd


def deriveFinEnumInstForToDomain (mod : Veil.Module) : CommandElabM Unit := do
  let typeBinders ← mod.typeExplicitBinders
  let finEnumInst ← mod.instBinders ``FinEnum
  let labelBinder ← `(bracketedBinder| ($(mkIdent `f) : $(mkIdent `State.Label)) )
  let allBinders := typeBinders ++ finEnumInst ++ [labelBinder]

  let stateLabelToDomain ←
    `(term| $(mkIdent `State.Label.toDomain) $(← mod.sortIdents)*)

  let instTargetTy ←
    `(term | ($(mkIdent ``IteratedProd) <| ($(mkIdent ``List.map) $(mkIdent ``FinEnum) <| ($stateLabelToDomain) $(mkIdent `f))))
  let finEnumCmd : TSyntax `command ←
    `(command|
        instance $(mkIdent `instFinEnumForToDomain):ident
          $[$allBinders]* : $instTargetTy := by
            cases $(mkIdent `f):ident <;>
              infer_instance_for_iterated_prod
    )
  elabVeilCommand finEnumCmd


def deriveFinEnumInstForToDomain' (mod : Veil.Module): CommandElabM Unit := do
  let typeBinders ← mod.typeExplicitBinders
  let finEnumInst ← mod.instBinders ``FinEnum
  let labelBinder ←
    `(bracketedBinder| ($(mkIdent `f) : $(mkIdent `State.Label)) )
  let allBinders := typeBinders ++ finEnumInst ++ [labelBinder]

  let stateLabelToDomain ←
    `(term| $(mkIdent `State.Label.toDomain) $(← mod.sortIdents)*)

  let instTargetTy ← `(term | $(mkIdent ``FinEnum) ($(mkIdent ``IteratedProd'):ident <| ($stateLabelToDomain) $(mkIdent `f)))
  let dsimpTerms : Array (TSyntax `ident) := #[
    mkIdent ``IteratedProd',
    mkIdent ``List.foldr,
    mkIdent `State.Label.toDomain
  ]
  let finEnumCmd : TSyntax `command ←
    `(command|
        instance $(mkIdent `instFinEnumForToDomain'):ident
          $[$allBinders]* : $instTargetTy := by
            cases $(mkIdent `f):ident <;>
              dsimp only [$[$dsimpTerms:ident],*]
              <;>
              infer_instance
    )
  elabVeilCommand finEnumCmd



syntax (name := derivingToJsonState) "deriving_FinOrdToJson_Domain" : command

@[command_elab derivingToJsonState]
def GetFieldsNameFieldsName : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
  let sig := mod.signature

  for s in sig do
    let sc := s.type
    trace[veil.debug] s!"Field: {s.name}, Kind: {s.kind}, Mutability: {s.mutability}"
    match sc with
    | .simple t =>
      trace[veil.debug] s!"simple Type: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic t}"
    | .complex binders dom =>
      let stx ← `(def $(mkIdent `NameT):ident $[$binders]* := $dom:term)
      trace[veil.debug] s!"Complex Type: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic stx}\n"

    -- for (name, res) in (← mod.getStateDomains) do
    --   trace[veil.debug] s!"State Domain Field: {name}, Domains: {res}"
  deriveFinEnumInstForToDomain mod
  deriveFinEnumInstForToDomain' mod
  deriveOrdInstForDomain mod (toDomain := true)
  deriveToJsonInstDomain mod (toDomain := true)
  deriveToJsonInstDomain mod (toDomain := false)



syntax (name := derivingDeciableInsts) "deriving_DecidableProps_state" : command
@[command_elab derivingDeciableInsts]
def deriveDecidablePropsForConcreteState : CommandElab := fun stx => do
  match stx with
  | `(command| deriving_DecidableProps_state) => do
    let mut mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
    let props := mod.invariants ++ mod.terminations
    for base in props do
      let explicitBinder := #[
            ← `(bracketedBinder| ($(mkIdent `rd) : $(mkIdent `TheoryConcrete) )),
            ← `(bracketedBinder| ($(mkIdent `st) : $(mkIdent `StateConcrete) )) ]
      let binder := explicitBinder
      let stx ← `(
        instance $[$binder]* : $(mkIdent ``Decidable) ($(mkIdent base.name) $(mkIdent `rd) $(mkIdent `st)) := by
          unfold $(mkIdent base.name):ident
          try dsimp [$(mkIdent base.name):ident, $(mkIdent `FieldConcreteType):ident, $(mkIdent `State.Label.toDomain):ident, $(mkIdent `State.Label.toCodomain):ident];
          infer_instance
      )
      elabVeilCommand stx
      trace[veil.debug] s!"Elaborated invariant definition for Concrete State: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic stx}"
  | _ => throwUnsupportedSyntax


syntax (name := concretizeTypeCmd) "#Concretize" term,* : command
/-- Generate label list (labelList) definition -/
def getLabelList : CommandElabM Unit := do
  trace[veil.info] "[getLabelList] Starting label list generation"
  let labelListDefName := (← getCurrNamespace) ++ `labelList
  if (← getEnv).contains labelListDefName then
    trace[veil.info] "[getLabelList] labelList already exists, skipping"
    return

  let labelConcreteName ← resolveGlobalConstNoOverloadCore `LabelConcrete
  let labelListCmd ← liftTermElabM do
    let labelListIdent := mkIdent `labelList
    let labelConcreteIdent := mkIdent labelConcreteName
    `(command|
      def $labelListIdent := ($(mkIdent ``FinEnum.ofEquiv) _ ($(mkIdent ``Equiv.symm) (proxy_equiv%($labelConcreteIdent)))).toList)
  trace[veil.debug] "[getLabelList] {labelListCmd}"
  elabVeilCommand labelListCmd


def getLabelListWithoutFieldTy : CommandElabM Unit := do
  trace[veil.info] "[getLabelListWithoutFieldTy] Starting label list generation"
  let labelListDefName := (← getCurrNamespace) ++ `labelList
  if (← getEnv).contains labelListDefName then
    trace[veil.info] "[getLabelListWithoutFieldTy] labelList already exists, skipping"
    return

  let labelConcreteName ← resolveGlobalConstNoOverloadCore `LabelConcrete
  let labelListCmd ← liftTermElabM do
    let labelListIdent := mkIdent `labelList
    let labelConcreteIdent := mkIdent labelConcreteName
    `(command|
      def $labelListIdent := ($(mkIdent ``FinEnum.ofEquiv) _ ($(mkIdent ``Equiv.symm) (proxy_equiv%($labelConcreteIdent)))).toList)
  trace[veil.debug] "[getLabelListWithoutFieldTy] {labelListCmd}"
  elabVeilCommand labelListCmd


elab "#Concretize" args:term,* : command => do
    let termArray := args.getElems
    let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
    /- The `State`, `Theory` and `Label` can only be used after `#gen_spec` run -/
    if !Module.isSpecFinalized mod then
      throwError "The module specification should be finalized before concretizing types."
    let FieldConcreteTypeName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo (mkIdent `FieldConcreteType)

    let theoryConcreteName := `TheoryConcrete
    let stateConcreteName := `StateConcrete
    let labelConcreteName := `LabelConcrete

    let theoryCmd ← do
      let assembledTheory ←`(term| @$(mkIdent theoryName) $termArray*)
      `(command| @[reducible] def $(mkIdent theoryConcreteName) := $assembledTheory)

    let labelCmd ← do
      let assembledLabel ←`(term| @$(mkIdent labelTypeName) $termArray*)
      `(command| @[reducible] def $(mkIdent labelConcreteName) := $assembledLabel)

    let fieldConcreteInstCmd ← do
      let assembledFieldConcreteInst ←`(term| $(mkIdent FieldConcreteTypeName) $termArray*)
      `(command| @[reducible] def $(mkIdent `FieldConcreteTypeInst) := $assembledFieldConcreteInst)

    let stateCmd ← do
      let assembledState ←`(term| @$(mkIdent stateName))
      let fieldConcreteInstTerm ← `(term| $(mkIdent `FieldConcreteType) $termArray*)
      `(command| @[reducible] def $(mkIdent stateConcreteName) := ($assembledState) $fieldConcreteInstTerm)
    elabVeilCommand theoryCmd
    elabVeilCommand labelCmd
    elabVeilCommand fieldConcreteInstCmd
    elabVeilCommand stateCmd

    let initCmd ← do
      let assembledInitM ←`(term|
        ((( $(mkIdent `initMultiExec) $(mkIdent `TheoryConcrete) $(mkIdent `StateConcrete) )
        $termArray* )
        $(mkIdent `FieldConcreteTypeInst) ) )
      `(command| def $(mkIdent `initVeilMultiExecM) := $assembledInitM)

    let nextCmd ← do
      let assembledNextM ←`(term|
        ( (( $(mkIdent `nextActMultiExec) $(mkIdent `TheoryConcrete) $(mkIdent `StateConcrete) )
            $termArray* )
          /-$(mkIdent `FieldConcreteTypeInst)-/ ) )
      `(command| def $(mkIdent `nextVeilMultiExecM) := $assembledNextM)
    dbg_trace "nextCmd: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic nextCmd}"
    elabVeilCommand initCmd
    elabVeilCommand nextCmd
    getLabelList


elab "#Concretize_without_FieldTy" args:term,* : command => do
    let termArray := args.getElems

    let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
    /- The `State`, `Theory` and `Label` can only be used after `#gen_spec` run -/
    if !Module.isSpecFinalized mod then
      throwError "The module specification should be finalized before concretizing types."

    let theoryConcreteName := `TheoryConcrete
    let stateConcreteName := `StateConcrete
    let labelConcreteName := `LabelConcrete

    let theoryCmd ← do
      let assembledTheory ←`(term| @$(mkIdent theoryName) $termArray*)
      trace[veil.debug] s!"TheoryConcrete assembledTheory: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic assembledTheory}"
      `(command| @[reducible] def $(mkIdent theoryConcreteName) := $assembledTheory)
    let labelCmd ← do
      let assembledLabel ←`(term| @$(mkIdent labelTypeName) $termArray*)
      trace[veil.debug] s!"LabelConcrete assembledLabel: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic assembledLabel}"
      `(command| @[reducible] def $(mkIdent labelConcreteName) := $assembledLabel)
    let stateCmd ← do
      let assembledState ←`(term| @$(mkIdent stateName) $termArray*)
      `(command| @[reducible] def $(mkIdent stateConcreteName) := $assembledState)

    elabVeilCommand theoryCmd
    elabVeilCommand labelCmd
    elabVeilCommand stateCmd

    let initCmd ← do
      let assembledInitM ←`(term|
        ((( $(mkIdent `initMultiExec) $(mkIdent `TheoryConcrete) $(mkIdent `StateConcrete) )
        $termArray* )
       /- $(mkIdent `FieldConcreteTypeInst)-/ ) )
      `(command| def $(mkIdent `initVeilMultiExecM) := $assembledInitM)

    let nextCmd ← do
      let assembledNextM ←`(term|
        ( (( $(mkIdent `nextActMultiExec) $(mkIdent `TheoryConcrete) $(mkIdent `StateConcrete) )
            $termArray* )
          /-$(mkIdent `FieldConcreteTypeInst)-/ ) )
      `(command| def $(mkIdent `nextVeilMultiExecM) := $assembledNextM)

    elabVeilCommand initCmd
    elabVeilCommand nextCmd
    getLabelList



def deriveBEqForState (mod : Veil.Module) : CommandElabM Unit := do
  let fieldNames ← mod.stateFieldNames
  let s1 := mkIdent `s1
  let s2 := mkIdent `s2
  let eqTerms : Array (TSyntax `term) ← fieldNames.mapM (fun f => do
    `(term| $s1.$(mkIdent f) == $s2.$(mkIdent f)))

  let beqBody : TSyntax `term ← do
    if h : eqTerms.size = 0 then
      `(term| True)
    else
      let mut acc := eqTerms[0]
      for i in [1:eqTerms.size] do
        acc ← `(term| $acc && $(eqTerms[i]!))
      pure acc

  let BEqInstCmd : Syntax ←
    `(command|
        instance : $(mkIdent ``BEq) $(mkIdent `StateConcrete) where
          $(mkIdent `beq):ident := fun $s1 $s2 => $beqBody)
  trace[veil.debug] s!"BEqInstCmd: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic BEqInstCmd}"
  elabVeilCommand BEqInstCmd


def deriveHashableForState (mod : Veil.Module) : CommandElabM Unit := do
  let fieldNames ← mod.stateFieldNames
  let s := mkIdent `s
  let binds : Array (Name × TSyntax `term) ←
    fieldNames.mapM (fun f => do
      let rhs ← `(term| $(mkIdent ``hash) $s.$(mkIdent f))
      pure (f, rhs))

  let hashIds : Array (TSyntax `term) :=
    fieldNames.map (fun f => (mkIdent f : TSyntax `term))
  let finalBody : TSyntax `term ← liftMacroM <| mkTuple hashIds

  let body : TSyntax `term ←
    binds.foldrM (init := finalBody) (fun (f, rhs) acc =>
      `(term| let $(mkIdent f) := $rhs; $acc))

  let HashableInstCmd : TSyntax `command ←
    `(command|
        instance : $(mkIdent ``Hashable) $(mkIdent `StateConcrete) where
          $(mkIdent `hash):ident := fun $s => $(mkIdent ``hash) $body)
  trace[veil.debug] s!"tryVlsUnfold : {← liftTermElabM <|Lean.PrettyPrinter.formatTactic HashableInstCmd}"
  elabVeilCommand HashableInstCmd
where
  mkTuple (xs : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
    match xs.size with
    | 0 => `(term| ())
    | 1 => pure xs[0]!
    | _ =>
      let mut acc : TSyntax `term ← `(term| ($(xs[0]!), $(xs[1]!)))
      for i in [2:xs.size] do
        acc ← `(term| ($acc, $(xs[i]!)))
      return acc

elab "deriving_BEq_ConcreteState" : command => do
  let mod ← getCurrentModule
  deriveBEqForState mod


elab "deriving_BEqHashable_ConcreteState" : command => do
  let mod ← getCurrentModule
  deriveBEqForState mod
  deriveHashableForState mod


def deriveToJsonForState (mod : Veil.Module) : CommandElabM Unit := do
  let sId := mkIdent `s

  let fieldNames ← mod.stateFieldNames
  let pairs : Array (TSyntax `term) ← fieldNames.mapM (fun fName => do
    let fieldStr := fName.toString
    let lit      := Syntax.mkStrLit fieldStr
    let projId   := mkIdent fName
    `(term| ($lit, $(mkIdent ``toJson) $sId.$projId))
  )

  let toJsonRhs ← `(term| fun $sId => $(mkIdent ``Json.mkObj) [ $[$pairs],* ])
  let instToJsonIdent := (mkIdent `jsonOfState)
  let traceToJsonInst ←
    `(command|
      instance $instToJsonIdent:ident : $(mkIdent ``ToJson) $(mkIdent `StateConcrete) where
        $(mkIdent `toJson):ident := $toJsonRhs)
  trace[veil.debug] s!"toJsonCmd: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic traceToJsonInst}"
  elabVeilCommand traceToJsonInst

syntax (name := derivingToJsonForState) "deriving_toJson_for_state" : command

@[command_elab derivingToJsonForState]
def deriveToJsonForStateElab : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
  deriveToJsonForState mod




syntax (name := veilMakeExecutable) "#gen_exec" : command

/--
Generate all required instances and definitions to make the symbolic model executable.
-/
macro_rules
  | `(command| #gen_exec) => do
    `(-- Make symbolic model executable by deriving required instances
      simple_deriving_repr_for' $(mkIdent `State)
      -- deriving instance $(mkIdent ``Repr) for $(mkIdent `Label)
      -- deriving instance $(mkIdent ``Inhabited) for $(mkIdent `Theory)
      deriving_FinOrdToJson_Domain
      specify_FieldConcreteType
      deriving_BEq_Hashable_FieldConcreteType
      deriving_rep_FieldRepresentation
      -- deriving_lawful_FieldRepresentation
      deriving_Inhabited_State
      gen_NextAct
      -- gen_executable_NextAct
      deriving_Enum_Insts
      )


syntax (name := veilFinitizeTypes) "#finitize_types" term,* : command

macro_rules
  | `(command| #finitize_types $args:term,*) => do
    `(-- Step 2: Finitize abstract types to enable model checking
      #Concretize $args,*
      deriving_BEqHashable_ConcreteState
      deriving_toJson_for_state
      deriving_DecidableProps_state)

syntax (name := veilSetTheory) "#set_theory" term : command
elab "#set_theory" theoryConcrete:term : command => do
  let setTheoryCmd ← liftTermElabM do
    `(command| def $(mkIdent `concreteTheory) : $(mkIdent `TheoryConcrete) := $theoryConcrete)
  elabVeilCommand setTheoryCmd


syntax (name := runModelChecker) "#run_model_checker" term : command
elab "#run_checker" propTerm:term : command => do
  let prop ← `(term| fun $(mkIdent `rd) $(mkIdent `st) => $propTerm $(mkIdent `rd) $(mkIdent `st))

  let mod ← getCurrentModule
  let terminate ←
    if mod.terminations.size == 0 then
      `(term| fun $(mkIdent `rd) $(mkIdent `st) => mkIdent ``true)
    else
      let terminateName := mod.terminations[0]!.name |> mkIdent
      `(term| fun $(mkIdent `rd) $(mkIdent `st) => $terminateName $(mkIdent `rd) $(mkIdent `st))

  let runModelCheckerCmd ← liftTermElabM do
    `(command|
      def $(mkIdent `modelCheckerResult) := ($(mkIdent `runModelCheckerx) $(mkIdent `initVeilMultiExecM) $(mkIdent `nextVeilMultiExecM) $(mkIdent `labelList) $prop $terminate $(mkIdent `concreteTheory) $(mkIdent ``hash)).snd
)
  elabVeilCommand runModelCheckerCmd

  let statesJsonCmd ← liftTermElabM do
    `(command|
      def $(mkIdent `statesJson) : $(mkIdent ``Lean.Json) := $(mkIdent ``Lean.toJson) ( $(mkIdent `recoverTrace) $(mkIdent `initVeilMultiExecM) $(mkIdent `nextVeilMultiExecM) $(mkIdent `concreteTheory) ( $(mkIdent `collectTrace') $(mkIdent `modelCheckerResult) ) )
    )
  elabVeilCommand statesJsonCmd
