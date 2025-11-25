import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Action.Elaborators
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.State

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


/-- Given name of instance like `Ord`, return all the instance binders for all the types. -/
def Veil.Module.instBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module) (instName : Name)
  : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let instNamePostfix := match instName with
    | ``Ord       => "_ord"
    | ``FinEnum   => "_fin_enum"
    | ``Hashable  => "_hash"
    | ``ToJson    => "_to_json"
    | _ => "_anonymous_inst"
  let ids : Array Ident ← mod.sortIdents
  ids.mapM (fun t : Ident =>
    let name' := t.getId.appendAfter instNamePostfix
    do `(bracketedBinder| [$(mkIdent name') : $(mkIdent instName) $t]) )


/-- Generate propCmp (e.g., `transCmp`, `LawfulEqCmp`) binder for a given type.
[Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord states)))]
-/
def Veil.propCmpBinder [Monad m] [MonadQuotation m] [MonadError m] (propName : Name) (sortIdent : Ident)
  : m (TSyntax `Lean.Parser.Term.bracketedBinder) := do
  let instNamePostfix := match propName with
    | ``Std.TransCmp     => "_trans_cmp"
    | ``Std.LawfulEqCmp   => "_lawful_cmp"
    | _ => "_anonymous_prop_cmp"
    let name' := sortIdent.getId.appendAfter instNamePostfix
  `(bracketedBinder| [$(mkIdent name') : $(mkIdent propName) ($(mkIdent ``Ord.compare) ( $(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $sortIdent) ))])


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


def lookupBindersWithSuffix [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module) (suf? : Option String) (errHead : String)
  : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let typeIdents : Array (TSyntax `ident) ← mod.sortIdents
  let varsBinders ← mod.collectVeilVarsBinders
  typeIdents.mapM fun t : (TSyntax `ident) => do
    let base := t.getId
    let key  := match suf? with
                | none      => base
                | some suf  => base.appendAfter suf
    match varsBinders.get? key with
    | some b => pure b
    | none   => throwError m!"{errHead} for type {t}"


def Veil.Module.typeExplicitBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module)
  : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) :=
  lookupBindersWithSuffix mod none "No type binder found"

def Veil.Module.typeDecEqBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module)
: m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) :=
  lookupBindersWithSuffix mod (some "_dec_eq") "No DecidableEq binder found"

def Veil.Module.typeInhabitedBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module)
  : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) :=
  lookupBindersWithSuffix mod (some "_inhabited") "No Inhabited binder found"



syntax (name := abbrevFieldConcreteType) "specify_FieldConcreteType" : command


/-
How to assembly `match...with` syntax
https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/.E2.9C.94.20Optional.20expected.20type.20in.20.60elab_rules.60/near/425853362
-/
def fieldsToMatchType (mod : Veil.Module) (fieldName : Name) (kind : StateComponentKind)
  : CommandElabM (TSyntax `Lean.Parser.Term.matchAltExpr) := do
  let caseIdent := mkIdent <| Name.append `State.Label fieldName
  let sortIdents ← mod.sortIdents
  let domainTerm : TSyntax `term ←
    `(term| ($(mkIdent `State.Label.toDomain) $sortIdents*) $caseIdent:ident)
  let codomainTerm : TSyntax `term ←
    `(term| ($(mkIdent `State.Label.toCodomain) $sortIdents*) $caseIdent:ident)
  let mapKeyTerm : TSyntax `term ←
    `(term| ($(mkIdent ``Veil.IteratedProd') <| $domainTerm))

  let caseBody ←
    match kind with
    | .individual => pure codomainTerm
    | .relation =>
        `(term| $(mkIdent ``Std.TreeSet) $mapKeyTerm)
    | .function =>
        `(term| $(mkIdent ``Veil.TotalTreeMap) $mapKeyTerm $codomainTerm)
    | .module =>
        throwError "Module kind is not supported in FieldConcreteType"

  `(Lean.Parser.Term.matchAltExpr|
    | $caseIdent:ident =>
      $caseBody:term)


@[command_elab abbrevFieldConcreteType]
def specifyFieldConcreteType : CommandElab := fun stx => do
  let mod ← getCurrentModule
  let typeBinders ← mod.typeExplicitBinders
  let ordInst ← mod.instBinders ``Ord
  let labelBinder ← `(bracketedBinder| ($(mkIdent `f) : $(mkIdent `State.Label)))
  let allBinders := typeBinders ++ ordInst ++ [labelBinder]

  let casesForKind (kind : StateComponentKind) := do
    let names ← mod.fieldNames kind
    names.mapM fun name => fieldsToMatchType mod name kind

  let relCases ← casesForKind .relation
  let funCases ← casesForKind .function
  let indivCases ← casesForKind .individual

  let fieldConcreteTypeCmd : TSyntax `command ←
    `(command|
        abbrev $(mkIdent `FieldConcreteType):ident
          $[$allBinders]* : Type :=
            match $(mkIdent `f):ident with
              $indivCases:matchAlt*
              $relCases:matchAlt*
              $funCases:matchAlt*
    )
  trace[veil.debug] s!"specify_FieldConcreteType : {← liftTermElabM <|Lean.PrettyPrinter.formatTactic fieldConcreteTypeCmd}"
  elabVeilCommand fieldConcreteTypeCmd



syntax (name := derivingBEqFieldConcreteTypeCmd) "deriving_BEq_FieldConcreteType" : command

private def concatArrays {α} (xs : Array (Array α)) : Array α :=
  xs.foldl (init := #[]) fun acc arr => acc ++ arr

private def mkFieldConcreteTypeInstance
    (mod : Veil.Module)
    (fieldLabelName instName instClass : Name)
    (extraBinderFns :
      Array (Veil.Module → CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder))))
    (dsimpTerms : Array (TSyntax `ident))
    : CommandElabM (TSyntax `command) := do
  let typeBinders ← mod.typeExplicitBinders
  let extraBinderGroups ← extraBinderFns.mapM fun f => f mod
  let extraBinders := concatArrays extraBinderGroups
  let allBinders := typeBinders ++ extraBinders
  let instTargetTy ←
      `(term |
        ($(mkIdent instClass) ($(mkIdent `FieldConcreteType):ident $(← mod.sortIdents)* $(mkIdent fieldLabelName))))
  `(command |
    instance $(mkIdent instName):ident
      $[$allBinders]* : $instTargetTy := by
          dsimp only [$[$dsimpTerms:ident],*]
          repeat' (first | infer_instance | constructor)
  )

private def mkFieldRepTerms (mod : Veil.Module) (fIdent : TSyntax `ident)
  : CommandElabM (Array (TSyntax `ident) × TSyntax `term × TSyntax `term × TSyntax `term) := do
  let sortIdents ← mod.sortIdents
  let domainTerm : TSyntax `term ←
    `(term|
      ($(mkIdent `State.Label.toDomain):ident $sortIdents*) $fIdent:ident)
  let codomainTerm : TSyntax `term ←
    `(term|
      ($(mkIdent `State.Label.toCodomain):ident $sortIdents*) $fIdent:ident)
  let fieldConcreteTerm : TSyntax `term ←
    `(term|
      ($(mkIdent `FieldConcreteType):ident $sortIdents*) $fIdent:ident)
  pure (sortIdents, domainTerm, codomainTerm, fieldConcreteTerm)

def deriveBEqInstForLabelField (mod : Veil.Module) (fieldName : Name)
  : CommandElabM (TSyntax `command) := do
  let stateLabelName := Name.append `State.Label fieldName
  mkFieldConcreteTypeInstance mod stateLabelName
    (fieldName.toInstName "instBEqForFieldConcreteType_") ``BEq
    #[
      fun mod => mod.typeDecEqBinders,
      fun mod => mod.instBinders ``Ord
    ]
    #[
      mkIdent `FieldConcreteType,
      mkIdent ``Veil.IteratedProd',
      mkIdent `State.Label.toDomain,
      mkIdent `State.Label.toCodomain
    ]

@[command_elab derivingBEqFieldConcreteTypeCmd]
def deriveBEqInstForFieldConcreteType : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
  let labelFields ← mod.stateFieldNames

  for lfIdent in labelFields do
    let lfc ← deriveBEqInstForLabelField mod lfIdent
    trace[veil.debug] s!"deriving_BEq_FieldConcreteType : {← liftTermElabM <|Lean.PrettyPrinter.formatTactic lfc}"
    elabVeilCommand lfc





def deriveHashableInstForLabelField (mod : Veil.Module) (fieldName : Name) : CommandElabM (TSyntax `command) := do
  let stateLabelName := Name.append `State.Label fieldName
  /- Deriving `Hashable` instance for each field (FieldConcreteType ... f) will
  finally reduce to giving an instance for `TreeSet α`, `TotalTreeMap α β`, e.g.,
  `⊢ Hashable (TreeSet (process × states) compare)`. Therefore, we should provide
  `Hashable` and `BEq` instances for used type parameters. We provide `DecideableEq`
  Here rather than `BEq`.

  This is an ad-hoc implementation, as sometimes we do not require that much instances.
   -/
  mkFieldConcreteTypeInstance mod stateLabelName
    (stateLabelName.toInstName "instHashableForFieldConcreteType_") ``Hashable
    #[
      fun mod => mod.typeDecEqBinders,
      fun mod => mod.instBinders ``Ord,
      fun mod => mod.instBinders ``Hashable
    ]
    #[
      mkIdent `FieldConcreteType,
      mkIdent ``IteratedProd',
      mkIdent `State.Label.toDomain,
      mkIdent `State.Label.toCodomain
    ]

syntax (name := derivingHashableFieldConcreteTypeCmd) "deriving_Hashable_FieldConcreteType" : command
@[command_elab derivingHashableFieldConcreteTypeCmd]
def deriveHashableInstForFieldConcreteType : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
  let labelFields ← mod.stateFieldNames
  for lfIdent in labelFields do
    let lfc ← deriveHashableInstForLabelField mod lfIdent
    trace[veil.debug] s!"deriving_Hashable_FieldConcreteType : {← liftTermElabM <|Lean.PrettyPrinter.formatTactic lfc}"
    elabVeilCommand lfc


def mkProdFromArray (xs : Array (TSyntax `term)) : TermElabM (TSyntax `term) := do
  match xs.toList with
  | []      =>  `(term| Unit)
  | [t]     =>  return ←`(term | ($t))
  | t :: ts =>  ts.foldlM (init := t) fun acc b => `(term| ($acc × ($b)))

syntax (name := deriveRepInstForFieldRepr) "deriving_rep_FieldRepresentation" : command

def deriveRepInstForFieldReprentation (mod : Veil.Module) : CommandElabM (TSyntax `command) := do
  /- Make sure `deriveFinEnumInstForToDomain` has been run before this command. -/
  let typeBinders ← mod.typeExplicitBinders
  let sortIdents ← mod.sortIdents
  let finEnumInsts ← mod.instBinders ``FinEnum
  let ordInsts ← mod.instBinders ``Ord

  /- It seems that we do not need `propCmp` instances for each sort ident.
  We only need `transCmp` for the prod type of `Domain` for `.function`. -/
  let mut binders := typeBinders ++ concatArrays #[finEnumInsts, ordInsts]

  let stateDomains ← mod.getStateDomains
  for (_, doms) in stateDomains do
    let productDomain ← mkProdFromArray doms |> liftTermElabM
    let transInst ← `(bracketedBinder| [$(mkIdent ``Std.TransCmp) ($(mkIdent ``Ord.compare) ( $(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $productDomain) ))])
    binders := binders.push transInst


  let dsimpTerms : Array Ident := #[
    mkIdent `FieldConcreteType,
    mkIdent `State.Label.toDomain,
    mkIdent `State.Label.toCodomain
  ]

  let fIdent := mkIdent `f
  let (repSorts, domainTerm, codomainTerm, fieldConcreteTerm) ← mkFieldRepTerms mod fIdent

  return ←
    `(command |
      instance $(mkIdent `instRepForFieldRepresentation):ident $[$binders]*
      ($fIdent : $(mkIdent `State.Label):ident)
      : $(mkIdent ``FieldRepresentation) ($domainTerm) ($codomainTerm) ($fieldConcreteTerm) :=
      by
        cases $fIdent:ident <;>
        first
        | (dsimp only [$[$dsimpTerms:ident],*]; infer_instance)
        | (exact $(mkIdent ``instFinsetLikeAsFieldRep) $(mkIdent ``Veil.IteratedProd'.equiv) (($(mkIdent `instFinEnumForToDomain) $repSorts*) _))
        | (exact $(mkIdent ``instTotalMapLikeAsFieldRep) $(mkIdent ``Veil.IteratedProd'.equiv) (($(mkIdent `instFinEnumForToDomain) $repSorts*) _))
    )


@[command_elab deriveRepInstForFieldRepr]
def deriveRepInstForFieldReprCmd : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
  let instCmd ← deriveRepInstForFieldReprentation mod
  trace[veil.debug] s!"deriving_rep_fieldRepresentation : {← liftTermElabM <|Lean.PrettyPrinter.formatTactic instCmd}"
  elabVeilCommand instCmd





syntax (name := deriveLawfulInstForFieldRepr) "deriving_lawful_FieldRepresentation" : command

def deriveLawfulInstForFieldRepresentation (mod : Veil.Module) : CommandElabM (TSyntax `command) := do
  /- Make sure `deriveFinEnumInstForToDomain` and `deriveRepInstForFieldReprentation` have been run before this command. -/
  let sortIdents ← mod.sortIdents
  let finEnumInsts ← mod.instBinders ``FinEnum
  let ordInsts ← mod.instBinders ``Ord
  let lawfulInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.LawfulEqCmp id)
  let transInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.TransCmp id)
  let binders := concatArrays #[finEnumInsts, ordInsts, lawfulInsts, transInsts]


  /- I do not know the reason compeletely now, but here we only need the `LawfulEqCmp` and `TransCmp` instances for the domain of `relation`.-/
  let dsimpTerms : Array Ident := #[
    mkIdent `FieldConcreteType,
    mkIdent `State.Label.toDomain,
    mkIdent `State.Label.toCodomain,
    mkIdent `instRepForFieldRepresentation,
    mkIdent ``Veil.IteratedProd',
    mkIdent `id
  ]
  let fIdent := mkIdent `f
  let (repSorts, domainTerm, codomainTerm, fieldConcreteTerm) ← mkFieldRepTerms mod fIdent
  return ←
    `(command |
      instance $(mkIdent `instLawfulFieldRepForFieldRepresentation):ident $[$binders]*
      ($fIdent : $(mkIdent `State.Label):ident)
      : $(mkIdent ``Veil.LawfulFieldRepresentation) ($domainTerm)
          ($codomainTerm)
          ($fieldConcreteTerm)
          ( ($(mkIdent `instRepForFieldRepresentation):ident $repSorts*) $fIdent ) :=
      by
        cases $fIdent:ident <;>
        first
        | (dsimp only [$[$dsimpTerms:ident],*]; infer_instance)
        | (exact $(mkIdent ``Veil.instFinsetLikeLawfulFieldRep) $(mkIdent ``Veil.IteratedProd'.equiv) (($(mkIdent `instFinEnumForToDomain) $repSorts*) _))
    )

@[command_elab deriveLawfulInstForFieldRepr]
def deriveLawfulInstForFieldReprCmd : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
  let instCmd ← deriveLawfulInstForFieldRepresentation mod
  trace[veil.debug] s!"deriving_lawful_fieldRepresentation : {← liftTermElabM <|Lean.PrettyPrinter.formatTactic instCmd}"
  elabVeilCommand instCmd



syntax (name := derivingInhabitedInst) "deriving_Inhabited_State" : command

def deriveInhabitedInstForState (mod : Veil.Module) : CommandElabM (TSyntax `command) := do
  let sortIdents ← mod.sortIdents
  let typeBinders ← mod.typeExplicitBinders
  let ordInsts ← mod.instBinders ``Ord
  let finEnumInst ← mod.instBinders ``FinEnum
  let inhabitedInsts ← mod.typeInhabitedBinders
  let decideableEqInsts ← mod.typeDecEqBinders
  let lawfulInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.LawfulEqCmp id)
  let transInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.TransCmp id)

  /- It's a little bit complex to derive the required minimal instances for this type. -/
  let binders := typeBinders ++ ordInsts ++ inhabitedInsts ++ decideableEqInsts ++ finEnumInst ++ lawfulInsts ++ transInsts

  let stateIdent := mkIdent `State
  let fieldConcreteTypeIdent := mkIdent `FieldConcreteType
  let dsimpTerms : Array Ident := #[
    mkIdent `FieldConcreteType,
    mkIdent `State.Label.toDomain,
    mkIdent `State.Label.toCodomain,
    mkIdent ``Veil.IteratedProd'
  ]
  return ←
    `(command |
      instance $(mkIdent `instInhabitedFieldConcreteTypeForState):ident $[$binders]*
      : $(mkIdent ``Inhabited) ( $stateIdent ( $fieldConcreteTypeIdent:ident $(sortIdents)* ) ) :=
      by
        constructor; constructor <;>
        dsimp only [$[$dsimpTerms:ident],*] <;>
        try exact $(mkIdent ``default)
    )

@[command_elab derivingInhabitedInst]
def deriveInhabitedInstCmd : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
  let instCmd ← deriveInhabitedInstForState mod
  trace[veil.debug] s!"deriving_inhabited_state : {← liftTermElabM <|Lean.PrettyPrinter.formatTactic instCmd}"
  elabVeilCommand instCmd



syntax (name := genNextActCommand) "gen_NextAct" : command

def genNextAct' (mod : Veil.Module) : CommandElabM (TSyntax `command) := do
  let sortIdents ← mod.sortIdents
  let finEnumInsts ← mod.instBinders ``FinEnum
  let hashInsts ← mod.instBinders ``Hashable
  let ordInsts ← mod.instBinders ``Ord
  let lawfulInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.LawfulEqCmp id)
  let transInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.TransCmp id)
  let mut binders := finEnumInsts ++ hashInsts ++ ordInsts ++ lawfulInsts ++ transInsts

  return ← `(command |
    attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet] $(mkIdent `instFinEnumForToDomain) in
    #specialize_nextact with $(mkIdent `FieldConcreteType)
    injection_begin
      $[$binders]*
    injection_end => $(mkIdent `NextAct'))


@[command_elab genNextActCommand]
def elabGenNextAct : CommandElab := fun stx => do
  let mod ← getCurrentModule
  let instCmd ← genNextAct' mod
  trace[veil.debug] "{← liftTermElabM <|Lean.PrettyPrinter.formatTactic instCmd}"
  elabVeilCommand instCmd



syntax (name := genExecutableNextAct) "gen_executable_NextAct" : command

def genExecutableList (mod : Veil.Module) : CommandElabM (TSyntax `command) := do
  let sortIdents ← mod.sortIdents
  let finEnumInsts ← mod.instBinders ``FinEnum
  let hashInsts ← mod.instBinders ``Hashable
  let ordInsts ← mod.instBinders ``Ord
  let lawfulInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.LawfulEqCmp id)
  let transInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.TransCmp id)
  let mut binders := finEnumInsts ++ hashInsts ++ ordInsts ++ lawfulInsts ++ transInsts


  return ← `(command |
    #gen_executable_list! log_entry_being $(mkIdent ``Std.Format)
    targeting $(mkIdent `NextAct')
    injection_begin
      $[$binders]*
    injection_end)

@[command_elab genExecutableNextAct]
def elabGenExecutableNextAct : CommandElab := fun stx => do
  let mod ← getCurrentModule
  let instCmd ← genExecutableList mod
  trace[veil.debug] "{← liftTermElabM <|Lean.PrettyPrinter.formatTactic instCmd}"
  elabVeilCommand instCmd




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
  trace[veil.debug] "orientedCmp: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic orientedCmp}"
  elabVeilCommand orientedCmp

  let transCmp ← `(command|
    instance : $(mkIdent ``Std.TransCmp) ($(mkIdent ``Ord.compare) ( $(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $(mkIdent name)) )) := by
      apply $(mkIdent ``Std.TransCmp.mk)
      unfold $(mkIdent `compare) $(mkIdent `inferInstanceAs) $(mkIdent <| Name.appendBefore name "instOrd")
      decide)
  trace[veil.debug] "transCmp: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic transCmp}"
  elabVeilCommand transCmp

  let lawfulCmp ← `(command|
    instance : $(mkIdent ``Std.LawfulEqCmp) ($(mkIdent ``Ord.compare) ( $(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $(mkIdent name)) )) := by
      apply $(mkIdent ``Std.LawfulEqCmp.mk)
      unfold $(mkIdent `compare) $(mkIdent `inferInstanceAs) $(mkIdent <| Name.appendBefore name "instOrd")
      intro $(mkIdent `a) $(mkIdent `b); cases $(mkIdent `a):ident <;>
        cases $(mkIdent `b):ident <;> simp)
  trace[veil.debug] "lawfulCmp: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic lawfulCmp}"
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
  let ordInst ← mod.instBinders ``Ord
  let reprInst ← mod.instBinders ``Repr
  let instBinders := ordInst ++ reprInst
  let instTargetTy ←
      `(term | ($(mkIdent ``Repr) ($(mkIdent `FieldConcreteType):ident $(← mod.sortIdents)* $(mkIdent stateLabelName))))
  let dsimpTerms : Array Ident := #[
    mkIdent `FieldConcreteType,
    mkIdent ``Veil.IteratedProd',
    mkIdent `State.Label.toDomain,
    mkIdent `State.Label.toCodomain
  ]
  return ← `(command |
    instance $(mkIdent $ (Name.appendBefore stateLabelName "instReprForFieldConcreteType_")):ident
      $[$instBinders]* : $instTargetTy := by
          dsimp only [$[$dsimpTerms:ident],*]
          repeat' (first | infer_instance | constructor)
  )
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

    for (name, res) in (← mod.getStateDomains) do
      trace[veil.debug] s!"State Domain Field: {name}, Domains: {res}"


  deriveFinEnumInstForToDomain mod
  deriveFinEnumInstForToDomain' mod
  deriveOrdInstForDomain mod (toDomain := true)
  deriveToJsonInstDomain mod (toDomain := true)
  deriveToJsonInstDomain mod (toDomain := false)



syntax (name := derivingDecInsts) "deriving_Decidable_Props" : command


/- `mod.mkVeilTerm` was `private def` before, which is in `Veil.Frontend.DSL.Module.Util`. Here I made it accessible, removing `private`. -/
/- Derive `Decidable` instanecs for invariants should be  -/
@[command_elab derivingDecInsts]
def deriveDecidableForProps : CommandElab := fun stx => do
  match stx with
  | `(command| deriving_Decidable_Props) => do
    let mut mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
    let props := mod.invariants ++ mod.terminations
    for base in props do
      let sortIdents ← mod.sortIdents
      let explicitBinder := #[
            ← `(bracketedBinder| ($(mkIdent `rd) : $(mkIdent `ρ))),
            ← `(bracketedBinder| ($(mkIdent `st) : $(mkIdent `σ))) ]
      let finEnumInst ← sortIdents.mapM (fun t => do
          `(bracketedBinder| [$(mkIdent ``FinEnum) $t])
      )
      let binder := explicitBinder ++ finEnumInst
      let stx ← `(
        instance $[$binder]* : $(mkIdent ``Decidable) ($(mkIdent base.name) $(mkIdent `rd) $(mkIdent `st)) := by
          dsimp [$(mkIdent base.name):ident];
          infer_instance
      )
      elabVeilCommand stx
      trace[veil.debug] s!"Elaborated invariant definition: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic stx}"
  | _ => throwUnsupportedSyntax



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
      let assembledFieldConcreteInst ←`(term | $(mkIdent FieldConcreteTypeName) $termArray*)
      `(command| @[reducible] def $(mkIdent `FieldConcreteTypeInst) := $assembledFieldConcreteInst)

    let stateCmd ← do
      let assembledState ←`(term| @$(mkIdent stateName))
      let fieldConcreteInstTerm ← `(term | $(mkIdent `FieldConcreteType) $termArray*)
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
      deriving instance $(mkIdent ``Repr) for $(mkIdent `Label)
      deriving instance $(mkIdent ``Inhabited) for $(mkIdent `Theory)
      deriving_FinOrdToJson_Domain
      specify_FieldConcreteType
      deriving_BEq_FieldConcreteType
      deriving_Hashable_FieldConcreteType
      deriving_rep_FieldRepresentation
      deriving_lawful_FieldRepresentation
      deriving_Inhabited_State
      gen_NextAct
      gen_executable_NextAct
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
  let terminate ← `(term| fun $(mkIdent `rd) $(mkIdent `st) => true)
  let runfuncName := mkIdent `runModelCheckerx
  let runModelCheckerCmd ← liftTermElabM do
    `(command|
      def $(mkIdent `modelCheckerResult) := ($runfuncName $(mkIdent `initVeilMultiExecM) $(mkIdent `nextVeilMultiExecM) $(mkIdent `labelList) $prop $terminate $(mkIdent `concreteTheory) $(mkIdent ``hash)).snd
    )
  elabVeilCommand runModelCheckerCmd

  let statesJsonCmd ← liftTermElabM do
    `(command|
      def $(mkIdent `statesJson) : $(mkIdent ``Lean.Json) := $(mkIdent ``Lean.toJson) ( $(mkIdent `recoverTrace) $(mkIdent `initVeilMultiExecM) $(mkIdent `nextVeilMultiExecM) $(mkIdent `concreteTheory) ( $(mkIdent `collectTrace') $(mkIdent `modelCheckerResult) ) )
    )
  elabVeilCommand statesJsonCmd

