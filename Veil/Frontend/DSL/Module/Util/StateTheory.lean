import Veil.Frontend.DSL.Module.Util.Basic
import Veil.Frontend.DSL.State.ConcreteRegistry
import Veil.Backend.SMT.Quantifiers

open Lean Parser Elab Command Term

namespace Veil

def Module.declareUninterpretedSort [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (name : Name) (userStx : Syntax) (sortKind : SortKind := .uninterpretedSort) : m Module := do
  mod.throwIfAlreadyDeclared name
  let typeT ← `(term|Type)
  let param : Parameter := { kind := .sort sortKind, name := name, «type» := typeT, userSyntax := userStx }
  let id := mkIdent name
  let dec_eq_type ← `(term|$(mkIdent ``DecidableEq).{1} $id)
  let dec_inhabited_type ← `(term|$(mkIdent ``Inhabited).{1} $id)
  let dec_eq : Parameter := { kind := .moduleTypeclass .sortAssumption, name := Name.mkSimple s!"{name}_dec_eq", «type» := dec_eq_type, userSyntax := userStx }
  let inhabited : Parameter := { kind := .moduleTypeclass .sortAssumption, name := Name.mkSimple s!"{name}_inhabited", «type» := dec_inhabited_type, userSyntax := userStx }
  let params := #[param, dec_eq, inhabited]
  let newDecls := #[(name, DeclarationKind.moduleParameter)] ++ params.map (fun p => (p.name, DeclarationKind.moduleParameter))
  return { mod with parameters := mod.parameters.append params, _declarations := mod._declarations.insertMany newDecls }

def isValidStateComponentType (kind : StateComponentKind) (tp : Expr) : CommandElabM Bool := do
  let (returnsProp, returnsBool) ← liftTermElabM $ Meta.forallTelescope tp (fun _ b => return (b.isProp, b.isBool))
  -- To keep actions executable without requiring `Decidable` instances
  -- for `State` and `Theory` fields, we disallow `Prop` return types.
  if returnsProp then
    return false
  match kind with
  | .individual => return !tp.isArrow
  | .relation => return returnsBool
  | .function => return tp.isArrow
  | .module =>
    -- `tp` must be a structure
    let constName := tp.getAppFn.constName?
    match constName with
    | .some constName => return (isStructure (←  getEnv) constName)
    | .none => return false

def Module.declareStateComponent (mod : Module) (sc : StateComponent) : CommandElabM Module := do
  if sc.kind == StateComponentKind.module || sc.mutability == Mutability.inherit then
    throwErrorAt sc.userSyntax "declareStateComponent called with `module` kind or `inherit` mutability; use `declareChildModule` instead"
  if !sc.name.isAtomic then
    throwErrorAt sc.userSyntax s!"Invalid name: {sc.name} is not an atomic name."
  mod.throwIfAlreadyDeclared sc.name
  let sig ← sc.getSimpleBinder
  let tp ← match sig with
  | `(Command.structSimpleBinder| $_:ident : $tp:term) => liftTermElabMWithBinders (← mod.sortBinders) (fun _ => do Meta.reduceAll $ ← elabTerm tp .none)
  | _ => throwErrorAt sc.userSyntax "Unsupported syntax for state component"
  if !(← isValidStateComponentType sc.kind tp) then
    failureMsg sig sc
  let mod := { mod with signature := mod.signature.push sc, _declarations := mod._declarations.insert sc.name sc.declarationKind }
  return mod
where
  failureMsg (_sig : TSyntax `Lean.Parser.Command.structSimpleBinder) (comp : StateComponent) : CommandElabM Unit := do
    throwErrorAt comp.userSyntax match comp.kind with
    | .individual => m!"Invalid type: individuals must not be arrow types, and cannot be Prop."
    | .relation => m!"Invalid type: relations must return Bool."
    | .function => m!"Invalid type: functions must have arrow type and not return Bool or Prop."
    | .module => m!"Invalid type: module state components must be structures."

def Module.immutableComponents (mod : Module) : Array StateComponent :=
  mod.signature.filter fun sc => sc.mutability == Mutability.immutable

def Module.mutableComponents (mod : Module) : Array StateComponent :=
  mod.signature.filter fun sc => sc.mutability == Mutability.mutable

def Module.getStateComponentTypeStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (name : Name) : m Term := do
  match mod.signature.find? (fun sc => sc.name == name) with
  | some sc => return ← sc.typeStx
  | none => throwErrorAt (← getRef) s!"State component {name} not found in module {mod.name}"

def Module.getTheoryBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  mod.signature.filterMapM fun sc => do
    match sc.mutability with
    | .immutable => return .some $ ← mkBinder sc
    | _ => pure .none
  where
    -- FIXME: this is a workaround for [lean4#10429](https://github.com/leanprover/lean4/pull/10429)
    mkBinder (sc : StateComponent) : m (TSyntax `Lean.Parser.Term.bracketedBinder) := do
      `(bracketedBinder| ($(mkIdent sc.name) : $(← sc.typeStx)))

/-
def Module.getStateBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  mod.signature.filterMapM fun sc => do
    match sc.mutability with
    | .mutable =>
      dbg_trace "getStateBinders: adding binder for state component {sc.name} of type {← sc.typeStx}"
      let (res, base) ← splitForallArgsCodomain (← sc.typeStx)
      dbg_trace "  splitForallArgsCodomain: base = {base}, res = {res}"
      return .some $ ← `(bracketedBinder| ($(mkIdent sc.name) : $(← sc.typeStx)))
    | _ => pure .none
-/

def Module.assumeForOneSort [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (className : Name) (sort : Term) (filterWithHeuristics : Bool := true) : m (Option (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  -- Special case `TransCmp` and `LawfulEqCmp`
  if #[``Std.TransCmp, ``Std.LawfulEqCmp, ``Std.ReflCmp].contains className then
    `(bracketedBinder|[$(mkIdent className) ($(mkIdent ``Ord.compare) ( $(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $sort) ))])
  else if className == ``Veil.Enumeration then
    -- A special check for `Enumeration`: if this sort does not appear in the
    -- domain of any *state field*, then *do not* add `Enumeration` instance binder.
    -- FIXME: This is a very ad-hoc condition checking; ideally, we should
    -- check *semantically* by using `remove_unused_args%` or something similar
    if !filterWithHeuristics || (mod.mutableComponents.any fun sc => sc.domainTerms.any fun tm => Option.isSome <| tm.raw.find? fun subtm => subtm == sort) then
      `(bracketedBinder|[$(mkIdent className) $sort])
    else pure none
  else
    `(bracketedBinder|[$(mkIdent className) $sort])

def Module.assumeInstArgsWithConcreteRepConfig [Monad m] [MonadQuotation m] [MonadError m] (mod : Module)
  (fields : Array StateComponent) (repConfigs : ResolvedConcreteRepConfigs)
  (domainInsts codomainInsts : ConcreteRepConfig → Array Name)
  (filterWithHeuristics : Bool := true) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  -- first compute all pairs of `(sort, className)` to assume
  -- NOTE: using `Name` here since there is no `Hashable` for `Ident`
  let sorts := mod.sortNames
  let mut sortToAssumingClasses : Std.HashMap Name (Array Name) := Std.HashMap.ofList <| sorts.toList.map fun a => (a, #[])
  for sc in fields do
    match sc.kind with
    | .relation =>
      for nm in sc.domainTerms.map (·.raw.getId) do
        for className in domainInsts repConfigs.relationConfig do
          sortToAssumingClasses := updateSortToAssumingClassesTable sortToAssumingClasses nm className
    | .function =>
      for nm in sc.domainTerms.map (·.raw.getId) do
        for className in domainInsts repConfigs.functionConfig do
          sortToAssumingClasses := updateSortToAssumingClassesTable sortToAssumingClasses nm className
      let codNm := sc.codomainTerm.raw.getId
      for className in codomainInsts repConfigs.functionConfig do
        sortToAssumingClasses := updateSortToAssumingClassesTable sortToAssumingClasses codNm className
    | _ => pure ()
  -- then generate binders
  let mut binders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) := #[]
  for (sortName, classNames) in sortToAssumingClasses do
    let sortIdent := mkIdent sortName
    for className in classNames do
      match ← mod.assumeForOneSort className sortIdent filterWithHeuristics with
      | some binder => binders := binders.push binder
      | none => pure ()
  return binders
where updateSortToAssumingClassesTable (tb : Std.HashMap Name (Array Name)) (domainTypeName className : Name) : Std.HashMap Name (Array Name) :=
  tb.alter domainTypeName fun
    | some arr => some <| if arr.contains className then arr else arr.push className
    | none => none      -- if this type is not a sort, we do nothing

/-- Get binders for assuming that every sort has an instance of `className` (e.g. `Ord node`). -/
def Module.assumeForEverySort [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (className : Name) (filterWithHeuristics : Bool := true) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  (← mod.sortIdents).filterMapM fun sortIdent => mod.assumeForOneSort className sortIdent filterWithHeuristics

/-! ## Structure Definition Helpers -/

/-- Given a list of state components, return the syntax for a structure
definition including those components. -/
private def structureDefinitionStx [Monad m] [MonadQuotation m] [MonadError m] (name : Name) (params : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (deriveInstances : Bool := true)
  (fields : Array (TSyntax `Lean.Parser.Command.structSimpleBinder)) : m (Array Syntax) := do
  if deriveInstances then
    let instances := #[``Inhabited, ``Nonempty].map Lean.mkIdent
    let defCmd ← `(structure $(mkIdent name) $params* where
        $(mkIdent `mk):ident :: $[$fields]*
      deriving $[$instances:ident],*)
    return #[defCmd]
  else
    let defCmd ← `(structure $(mkIdent name) $params* where
      $(mkIdent `mk):ident :: $[$fields]*)
    return #[defCmd]

/-! ## Structure Definitions (Private) -/

/-- Syntax for *defining* the mutable state of a module as a `structure`. The
syntax for the type is `mod.stateStx`. -/
private def Module.stateDefinitionStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Array Syntax) := do
  let defCmds ← structureDefinitionStx stateName (← mod.sortBindersForTheoryOrState false) (deriveInstances := true)
    (← mod.mutableComponents.mapM fun sc => sc.getSimpleBinder)
  let isHOInst ← mkIsHigherOrderInstance
  return defCmds ++ #[← `(command| veil_deriving $(mkIdent ``Repr) for $stateIdent), isHOInst]
where
  mkIsHigherOrderInstance : m (TSyntax `command) := do
    let binders ← mod.sortBinders
    let sorts ← mod.sortIdents
    let hoTy ← `(term|$(mkIdent ``Veil.IsHigherOrder) ($stateIdent $sorts*))
    `(scoped instance (priority := default) $(mkIdent $ Name.mkSimple s!"{stateName}_ho"):ident $[$binders]* : $hoTy := ⟨⟩)

/-- Similar to `Module.stateDefinitionStx` but each field of `State` is
abstracted by a function from its label to a certain type. Note that
in this case, `deriveInstances` has to be `false`. -/
private def Module.fieldsAbstractedStateDefinitionStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Array Syntax) := do
  let stateLabelTypeName := structureFieldLabelTypeName stateName
  let fields ← mod.mutableComponents.mapM fun sc => do
    let ty ← `($fieldConcreteType $(mkIdent <| stateLabelTypeName ++ sc.name):ident)
    `(Command.structSimpleBinder| $(mkIdent sc.name):ident : $ty)
  let defCmds ← structureDefinitionStx stateName (← mod.sortBindersForTheoryOrState true) (deriveInstances := false) fields
  return defCmds ++ #[← mkInhabitedInstance, ← mkHashableInstance, ← mkBEqInstance, ← mkDecidableEqInstance] ++ (← mkToJsonInstances) ++ #[← `(command| veil_deriving $(mkIdent ``Repr) for $stateIdent), ← mkIsHigherOrderInstance]
where
  /-- Generate an `IsHigherOrder` instance for `State χ`. -/
  mkIsHigherOrderInstance : m (TSyntax `command) := do
    let χBinder ← Parameter.fieldConcreteType >>= Parameter.binder
    let binders := (← mod.sortBinders) ++ #[χBinder]
    let hoTy ← `(term|$(mkIdent ``Veil.IsHigherOrder) ($stateIdent $fieldConcreteType))
    `(scoped instance (priority := default) $(mkIdent $ Name.mkSimple s!"{stateName}_ho"):ident $[$binders]* : $hoTy := ⟨⟩)
  /-- Generate binders of the form `(χ : State.Label → Type) [∀ f : State.Label, C (χ f)]` -/
  mkFieldConcreteTypeBinders (typeclass : Name) : m (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) := do
    let χBinder ← Parameter.fieldConcreteType >>= Parameter.binder
    let f := mkIdent `f
    let stateLabelType := structureFieldLabelType stateName
    let constraint ← `(bracketedBinder| [∀ $f : $stateLabelType, $(mkIdent typeclass) ($fieldConcreteType $f)])
    return #[χBinder, constraint]
  -- NOTE: By using instances generated by `veil_deriving`, we can potentially
  -- avoiding defining instances in the shape of `∀ f : State.Label, C (FieldConcreteType f)`
  -- in advance
  mkInhabitedInstance : m Syntax := do
    `(veil_deriving $(mkIdent ``Inhabited) for $stateIdent with_name $instInhabitedStateFieldConcreteType with_priority low)
  mkHashableInstance : m Syntax := do
    `(veil_deriving $(mkIdent ``Hashable) for $stateIdent with_priority low)
  mkBEqInstance : m Syntax := do
    `(veil_deriving $(mkIdent ``BEq) for $stateIdent with_priority low)
  mkDecidableEqInstance : m Syntax := do
    `(veil_deriving $(mkIdent ``DecidableEq) for $stateIdent with_priority low)
  mkToJsonInstances : m (Array Syntax) := do
    let sorts ← mod.sortIdents
    let concreteInst ← `(veil_deriving $(mkIdent ``Lean.ToJson) for $stateIdent with_priority low)
    -- Abstract instance: ToJson (FieldAbstractType sorts* f)
    let fieldLabelIdent := mkVeilImplementationDetailIdent `f
    let fieldLabel ← `(bracketedBinder|($fieldLabelIdent : $(structureFieldLabelType stateName)))
    let abstractBinders := (← mod.sortBinders) ++ (← #[``Lean.ToJson, ``Ord, ``Enumeration].flatMapM mod.assumeForEverySort) ++ #[fieldLabel]
    let abstractTy ← `(term| $(mkIdent ``Lean.ToJson) ($fieldAbstractDispatcher $sorts* $fieldLabelIdent))
    let abstractInst ← `(scoped instance $[$abstractBinders]* : $abstractTy := by cases $fieldLabelIdent:ident <;> infer_instance_for_iterated_prod')
    return #[concreteInst, abstractInst]


/-- Syntax for *defining* the immutable background theory of a module as a
`structure`. The syntax for the type is `mod.theoryStx`. -/
private def Module.theoryDefinitionStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Array Syntax) := do
  let defCmds ← structureDefinitionStx theoryName (← mod.sortBindersForTheoryOrState false) (deriveInstances := true)
    (← mod.immutableComponents.mapM fun sc => sc.getSimpleBinder)
  return defCmds ++ #[← `(command| veil_deriving $(mkIdent ``Repr) for $theoryIdent), (← mkToJsonInstance)]
where
  mkToJsonInstance : m Command := do
    let toJsonTy ← `(term| $(mkIdent ``Lean.ToJson) ($(mkIdent theoryName) $(← mod.sortIdents)*))
    let ρ := mkIdent `ρ
    let fieldNames := mod.immutableComponents.map (·.name)
    let jsonPairs ← fieldNames.mapM fun field => do
      let fieldStr := toString field
      `(term| ($(Syntax.mkStrLit fieldStr), $(mkIdent ``Lean.ToJson.toJson) $ρ.$(mkIdent field)))
    let toJsonBody ← `(term| $(mkIdent ``Lean.Json.mkObj) [$[$jsonPairs],*])
    let sortBinders ← mod.sortBinders
    let assumedInstances ← #[``Lean.ToJson, ``Enumeration].flatMapM fun className => mod.assumeForEverySort className
    `(scoped instance $[$sortBinders]* $[$assumedInstances]* : $toJsonTy where toJson := fun $ρ => $toJsonBody)

/-! ## Public Structure Declaration APIs -/

def Module.declareStateStructure [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Module × Array Syntax) := do
  mod.throwIfAlreadyDeclared environmentSubStateName
  let stx ← mod.stateDefinitionStx
  let stateStx ← mod.stateStx
  let substate : Parameter := { kind := .moduleTypeclass .environmentState, name := environmentSubStateName, «type» := ← `($(mkIdent ``IsSubStateOf) $stateStx $environmentState), userSyntax := .missing }
  return ({ mod with parameters := mod.parameters.push substate, _declarations := mod._declarations.insert environmentSubStateName .moduleParameter }, stx)

def Module.declareTheoryStructure [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Module × Array Syntax) := do
  mod.throwIfAlreadyDeclared environmentSubTheoryName
  let stxs ← mod.theoryDefinitionStx
  let theoryStx ← mod.theoryStx
  let subtheory : Parameter := { kind := .moduleTypeclass .backgroundTheory, name := environmentSubTheoryName, «type» := ← `($(mkIdent ``IsSubReaderOf) $theoryStx $environmentTheory), userSyntax := .missing }
  return ({ mod with parameters := mod.parameters.push subtheory, _declarations := mod._declarations.insert environmentSubTheoryName .moduleParameter }, stxs)

/-- Similar to `Module.declareStateStructure` but here `FieldRepresentation`
is involved. -/
def Module.declareFieldsAbstractedStateStructure [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (repConfigs : ResolvedConcreteRepConfigs) : m (Module × (Array Syntax)) := do
  mod.throwIfAlreadyDeclared environmentSubStateName
  let stateDefs ← mod.fieldsAbstractedStateDefinitionStx
  let concreteFieldRepInsts ← mkFieldRepresentationInstancesForConcrete mod repConfigs
  let abstractFieldRepInsts ← mkFieldRepresentationInstancesForAbstract mod
  -- TODO revisit this later
  -- let enumerationInst ← mkEnumerationInstance mod
  let stateStx ← mod.stateStx (withFieldConcreteType? := true)
  let smtAttr ← `(attribute [$(mkIdent `smtSimp):ident] $(mkIdent $ stateName ++ `mk ++ `injEq):ident)
  let eqMkTheorem ← mkEqMkTheorem mod
  let substate : Parameter := { kind := .moduleTypeclass .environmentState, name := environmentSubStateName, «type» := ← `($(mkIdent ``IsSubStateOf) $stateStx $environmentState), userSyntax := .missing }
  return ({ mod with parameters := mod.parameters.push substate, _declarations := mod._declarations.insert environmentSubStateName .moduleParameter }, stateDefs ++ concreteFieldRepInsts ++ abstractFieldRepInsts ++ #[/- enumerationInst, -/ smtAttr, eqMkTheorem])
where
  /-- Generate `FieldRepresentation` and `LawfulFieldRepresentation` instances for a given field type dispatcher. -/
  mkFieldRepresentationInstancesCore (mod : Module)
      (fieldTypeDispatcher : Ident) (instName lawfulInstName : Ident)
      (fieldRepAssumed lawfulAssumed : Array (TSyntax `Lean.Parser.Term.bracketedBinder))
      (mkTactic : Array Ident → Ident → m (TSyntax `tactic))
      (mkLawfulTactic : Array Ident → Ident → m (TSyntax `tactic)) : m (Array Syntax) := do
    let (sorts, fieldLabelIdent) := (← mod.sortIdents, mkVeilImplementationDetailIdent `f)
    let fieldLabel ← `(bracketedBinder|($fieldLabelIdent:ident : $(mkIdent `State.Label)))
    let toDomainTerm ← `(($(fieldLabelToDomain stateName) $sorts* $fieldLabelIdent))
    let toCodomainTerm ← `(($(fieldLabelToCodomain stateName) $sorts* $fieldLabelIdent))
    let fieldTypeApplied ← `(($fieldTypeDispatcher $sorts* $fieldLabelIdent))
    -- Field representation instance
    let fieldRepTy ← `(term|$(mkIdent ``FieldRepresentation) $toDomainTerm $toCodomainTerm $fieldTypeApplied)
    let fieldRepBinders := (← mod.sortBinders) ++ fieldRepAssumed ++ #[fieldLabel]
    let fieldRepStx ← `(scoped instance $instName:ident $fieldRepBinders* : $fieldRepTy := by $(← mkTactic sorts fieldLabelIdent):tactic)
    -- Lawful field representation instance
    let lawfulFieldRepTy ← `(term|$(mkIdent ``LawfulFieldRepresentation) $toDomainTerm $toCodomainTerm $fieldTypeApplied ($instName $sorts* $fieldLabelIdent))
    let lawfulFieldRepBinders := (← mod.sortBinders) ++ lawfulAssumed ++ #[fieldLabel]
    let lawfulFieldRepStx ← `(scoped instance $lawfulInstName:ident $lawfulFieldRepBinders* : $lawfulFieldRepTy := by $(← mkLawfulTactic sorts fieldLabelIdent):tactic)
    return #[fieldRepStx, lawfulFieldRepStx]
  mkFieldRepresentationInstancesForConcrete (mod : Module) (repConfigs : ResolvedConcreteRepConfigs) : m (Array Syntax) := do
    -- Combine domain and codomain requirements (for now we apply all to every sort)
    let fields := mod.mutableComponents
    let fieldRepAssumed ← mod.assumeInstArgsWithConcreteRepConfig fields repConfigs
      ConcreteRepConfig.domainFieldRepInstances ConcreteRepConfig.codomainFieldRepInstances
    let lawfulAssumed ← mod.assumeInstArgsWithConcreteRepConfig fields repConfigs
      ConcreteRepConfig.domainLawfulFieldRepInstances ConcreteRepConfig.codomainLawfulFieldRepInstances
    mkFieldRepresentationInstancesCore mod fieldConcreteDispatcher instFieldRepresentation instLawfulFieldRepresentation
      fieldRepAssumed
      lawfulAssumed
      -- Use hardcoded hybrid instance names (they don't need to be parameterized)
      (mkFieldRepresentationSolverTactic
        repConfigs.relationConfig.fieldRepInstance
        repConfigs.functionConfig.fieldRepInstance
        ``NotNecessarilyFinsetLikeUpdates.instHybridFinsetLikeAsFieldRep
        ``NotNecessarilyFinmapLikeUpdates.instHybridFinmapLikeAsFieldRep)
      (mkLawfulFieldRepresentationSolverTactic
        repConfigs.relationConfig.lawfulFieldRepInstance
        repConfigs.functionConfig.lawfulFieldRepInstance
        ``NotNecessarilyFinsetLikeUpdates.instHybridFinsetLikeLawfulFieldRep
        ``NotNecessarilyFinmapLikeUpdates.instHybridFinmapLikeLawfulFieldRep)
    -- (← fieldRepAssumed.flatMapM mod.assumeForEverySort)
    -- (← lawfulAssumed.flatMapM mod.assumeForEverySort)
  mkFieldRepresentationInstancesForAbstract (mod : Module) : m (Array Syntax) := do
    let abstractTactic : Array Ident → Ident → m (TSyntax `tactic) := fun _ f =>
      `(tactic| cases $f:ident <;> (apply $(mkIdent ``Veil.canonicalFieldRepresentation); infer_instance_for_iterated_prod))
    let lawfulAbstractTactic : Array Ident → Ident → m (TSyntax `tactic) := fun _ f =>
      `(tactic| cases $f:ident <;> apply $(mkIdent ``Veil.canonicalFieldRepresentationLawful))
    let repInsts ← do
      let fieldRepAssumed ← #[``DecidableEq].flatMapM mod.assumeForEverySort
      let lawfulAssumed ← #[``DecidableEq].flatMapM mod.assumeForEverySort
      mkFieldRepresentationInstancesCore mod fieldAbstractDispatcher instAbstractFieldRepresentation instLawfulAbstractFieldRepresentation
        fieldRepAssumed lawfulAssumed abstractTactic lawfulAbstractTactic
    -- Inhabited instance for State (FieldAbstractType sorts*)
    let sorts ← mod.sortIdents
    let inhabitedTy ← `(term|$(mkIdent ``Inhabited) ($stateIdent ($fieldAbstractDispatcher $sorts*)))
    let inhabitedBinders := (← mod.sortBinders) ++ (← #[``Inhabited, ``DecidableEq].flatMapM mod.assumeForEverySort)
    let (toDomainId, toCodomainId) := (mkIdent (fieldLabelToDomainName stateName), mkIdent (fieldLabelToCodomainName stateName))
    let inhabitedStx ← `(scoped instance $[$inhabitedBinders]* : $inhabitedTy := by constructor; constructor <;> (dsimp [$toDomainId:ident, $toCodomainId:ident]; exact $(mkIdent ``Inhabited.default)))
    return repInsts ++ #[inhabitedStx]
  /-- `NN` indicates "not necessarily". -/
  mkFieldRepresentationSolverTactic (relTFinCase funTFinCase relTNNFinCase funTNNFinCase : Name) (sorts : Array Ident) (fieldLabelIdent : Ident) : m (TSyntax `tactic) := do
    let fieldLabelIdentBackup := mkVeilImplementationDetailIdent `f_backup
    let instEnumerationForIteratedProdApplied ← `(($instEnumerationForIteratedProd $sorts*) $fieldLabelIdentBackup)
    let realEnumerationForIteratedProd ← do
      let domainGetter ← `(term|($(fieldLabelToDomain stateName):ident $sorts*) $fieldLabelIdentBackup:ident)
      let optionBindProd ← do
        let (a, b, bd, va, vb) := (mkIdent `a, mkIdent `b, mkIdent ``Option.bind, mkIdent `va, mkIdent `vb)
        `(term| fun $a $b => $bd $(mkIdent `a.body) fun $va => $bd $b fun $vb => $(mkIdent ``Option.some) ($va, $vb))
      `(@$(mkIdent ``Veil.IteratedProd.fold) ($(mkIdent ``List.map) $(mkIdent ``Veil.Enumeration) ($domainGetter))
        $(mkIdent ``Veil.OptionalTC) $(mkIdent ``Option) ($(mkIdent ``Option.some) $(mkIdent ``Unit.unit))
        $optionBindProd $instEnumerationForIteratedProdApplied)
    let equiv := mkIdent ``Veil.IteratedProd'.equiv
    let tacLet ← `(tactic|let $fieldLabelIdentBackup := $fieldLabelIdent)
    `(tactic|($tacLet:tactic ; cases $fieldLabelIdent:ident) <;>
    first
    | infer_instance
    | (exact (meta_match_option $realEnumerationForIteratedProd
        => ($(mkIdent relTFinCase) ($equiv) ·)      -- `·` is required here!
        => ($(mkIdent relTNNFinCase) ($equiv) ($instEnumerationForIteratedProdApplied) (by infer_instance_for_iterated_prod))))
    | (exact (meta_match_option $realEnumerationForIteratedProd
        => ($(mkIdent funTFinCase) ($equiv) ·)
        => ($(mkIdent funTNNFinCase) ($equiv) ($instEnumerationForIteratedProdApplied) (by infer_instance_for_iterated_prod)))))
  -- Since the `FieldRepresentation` instances are determined, just apply the appropriate ones
  mkLawfulFieldRepresentationSolverTactic (relTFinCase funTFinCase relTNNFinCase funTNNFinCase : Name) (_ : Array Ident) (fieldLabelIdent : Ident) : m (TSyntax `tactic) := do
    `(tactic|cases $fieldLabelIdent:ident <;>
    first
    | infer_instance
    | apply $(mkIdent ``instLawfulFieldRepresentationIndividual)
    | apply $(mkIdent relTFinCase)
    | apply $(mkIdent relTNNFinCase)
    | apply $(mkIdent funTFinCase)
    | apply $(mkIdent funTNNFinCase))
  /-- Build the chained flatMap/map expression for `Enumeration` instance.
      For fields [f1, f2, f3], generates:
      ```
      Enumeration.allValues |>.flatMap fun l =>
      Enumeration.allValues |>.flatMap fun p =>
      Enumeration.allValues |>.map fun f =>
      State.mk l p f
      ```
  -/
  mkEnumerationAllValuesBody (fields : List Name) (varNames : Array Ident) : m Term := do
    match fields with
    | [] => `(term| [$(mkIdent `State.mk)])
    | [f] =>
      let varName := mkIdent $ Name.mkSimple s!"{f}"
      let allVars := varNames.push varName
      let ctorApp ← `(term| $(mkIdent `State.mk) $allVars*)
      `(term| $(mkIdent ``Enumeration.allValues) |>.$(mkIdent `map) fun $varName => $ctorApp)
    | f :: rest =>
      let varName := mkIdent $ Name.mkSimple s!"{f}"
      let innerBody ← mkEnumerationAllValuesBody rest (varNames.push varName)
      `(term| $(mkIdent ``Enumeration.allValues) |>.$(mkIdent `flatMap) fun $varName => $innerBody)
  /-- Generate an `Enumeration` instance for `State (FieldConcreteType sorts*)`.
      This allows enumerating all possible state values when sorts are finite. -/
  mkEnumerationInstance (mod : Module) : m Syntax := do
    let sorts ← mod.sortIdents
    -- Generate binders: (node : Type) [Inhabited node] [Ord node] [DecidableEq node] [Enumeration node] ...
    let assumedInstances := #[``Ord, ``DecidableEq, ``Enumeration]
    let sortInstanceBinders := (← mod.sortBinders) ++ (← assumedInstances.flatMapM mod.assumeForEverySort)
    -- Generate [Veil.Enumeration (FieldConcreteType $sorts* State.Label.$fieldName)] for each field
    -- We add these as explicit assumptions to avoid `grind` throwing errors
    -- in `#gen_spec` when they're not satisfied at runtime
    let fieldEnumerationBinders ← mod.mutableComponents.mapM fun sc => do
      let fieldLabel := mkIdent <| Name.append (structureFieldLabelTypeName stateName) sc.name
      `(bracketedBinder|[$(mkIdent ``Veil.Enumeration) ($fieldConcreteDispatcher $sorts* $fieldLabel)])
    -- Generate [DecidableEq (State (FieldConcreteType sorts*))]
    let stateType ← `(term| $stateIdent ($fieldConcreteDispatcher $sorts*))
    let allBinders := sortInstanceBinders ++ fieldEnumerationBinders
    -- Generate instance type: Veil.Enumeration (State (FieldConcreteType sorts*))
    let instType ← `(term| $(mkIdent ``Veil.Enumeration) $stateType)
    -- Generate allValues body with nested flatMap/map calls
    let fieldNames := mod.mutableComponents.map (·.name)
    let allValuesBody ← mkEnumerationAllValuesBody fieldNames.toList #[]
    -- Generate complete proof tactic
    `(scoped instance $[$allBinders]* : $instType where
      $(mkIdent `allValues):ident := $allValuesBody
      $(mkIdent `complete):ident := by simp only [$(mkIdent ``List.mem_flatMap):ident, $(mkIdent ``List.mem_map):ident]; grind only [← $(mkIdent ``Enumeration.complete):ident])
  /-- Generate a theorem `State.eqMk` that characterizes equality of a state with a structure literal.
      For fields [leader, pending], generates:
      ```
      theorem State.eqMk {χ : State.Label → Type} (st : State χ)
        (leader : χ State.Label.leader) (pending: χ State.Label.pending) :
        (st = { leader := leader, pending := pending }) = (st.leader = leader ∧ st.pending = pending) :=
        by grind only [cases State, cases Or]
      ```
  -/
  mkEqMkTheorem (mod : Module) : m Command := do
    let fieldNames := mod.mutableComponents.map (·.name)
    let (χ, st) := (mkIdent `χ, mkIdent `st)
    let χBinder ← `(bracketedBinder| {$χ : $(structureFieldLabelType stateName) → Type})
    let stBinder ← `(bracketedBinder| ($st : $stateIdent $χ))
    let fieldBinders ← fieldNames.mapM fun f =>
      `(bracketedBinder| ($(mkIdent f) : $χ $(mkIdent <| structureFieldLabelTypeName stateName ++ f)))
    let structFields ← fieldNames.mapM fun f =>
      `(Lean.Parser.Term.structInstField| $(mkIdent f):ident := $(mkIdent f))
    let eqTerms ← fieldNames.mapM fun f => `(term| $st.$(mkIdent f) = $(mkIdent f))
    let prop ← `(term| ($st = { $[$structFields:structInstField],* }) = $(← repeatedAnd eqTerms))
    let allBinders := #[χBinder, stBinder] ++ fieldBinders
    `(@[$(mkIdent `smtSimp):ident] theorem $(mkIdent <| stateName ++ `eqMk) $[$allBinders]* : $prop :=
        by grind only [cases $stateIdent, cases $(mkIdent ``Or)])

/-! ## Field Label Type & Metadata (Private) -/

/-- Declare an inductive type with each constructor corresponding to each
field of `State` (i.e., each `State` component). -/
private def declareStructureFieldLabelType [Monad m] [MonadQuotation m] [MonadError m] (base : Name) (components : Array StateComponent) : m (Name × TSyntax `command) := do
  let fields ← components.mapM fun sc => `(Command.ctor| | $(mkIdent sc.name):ident )
  let name := structureFieldLabelTypeName base
  let res ← `(inductive $(mkIdent name) : Type where $[$fields]*)
  return (name, res)

/-! ## Field Dispatchers (Private) -/

/-- Declare dispatchers that given the label for a specific field, returns the
types of its arguments and its codomain, as well as the concrete and abstract
types of the field. -/
private def Module.declareFieldDispatchers [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (base : Name) (fields : Array StateComponent) (params : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (repConfigs : ResolvedConcreteRepConfigs)
  : m ((Array (Name × Syntax)) × (Name × Syntax) × (Name × Syntax)) := do
  let domainComponents ← fields.mapM (·.domainList)
  let coDomainComponents := fields.map (·.codomainTerm)
  let f := mkVeilImplementationDetailIdent `f
  let casesOnName := structureFieldLabelTypeName base ++ `casesOn
  let fieldLabel ← `(bracketedBinder| ($f : $(structureFieldLabelType base)))
  let dParams := params ++ [fieldLabel]
  -- to domain dispatcher
  let todomain ← `(abbrev $(fieldLabelToDomain base) $dParams* : $(mkIdent ``List) Type := $(mkIdent casesOnName) $f $domainComponents*)
  -- to codomain dispatcher
  let tocodomain ← `(abbrev $(fieldLabelToCodomain base) $dParams* : Type := $(mkIdent casesOnName) $f $coDomainComponents*)
  -- abstract field representation dispatcher (CanonicalField Domain Codomain)
  let sortIdents ← mod.sortIdents
  let abstractTypes ← fields.mapM (fieldKindToAbstractType sortIdents)
  let toabstracttype ← `(abbrev $fieldAbstractDispatcher $dParams* : Type := $(mkIdent casesOnName) $f $abstractTypes*)
  -- concrete field representation dispatcher
  -- Use domain type instances from the resolved configs (codomain instances are separate)
  let typeInstanceBinders ← mod.assumeInstArgsWithConcreteRepConfig fields repConfigs
    ConcreteRepConfig.domainTypeInstances ConcreteRepConfig.codomainTypeInstances
  let cParams := params ++ typeInstanceBinders ++ [fieldLabel]
  let concreteTypes ← fields.mapM (fieldKindToConcreteType sortIdents repConfigs)
  let toconcretetype ← `(abbrev $fieldConcreteDispatcher $cParams* : Type := $(mkIdent casesOnName) $f $concreteTypes*)
  return (#[(fieldLabelToDomainName base, todomain), (fieldLabelToCodomainName base, tocodomain)], (fieldAbstractDispatcherName, toabstracttype), (fieldConcreteTypeName, toconcretetype))
  where
  /-- Get domain and codomain getter terms for a field (e.g.,
  `State.Label.toDomain sorts State.Label.foo`). -/
  fieldDomainCodomainGetters (sortIdents : Array Ident) (sc : StateComponent) : m (Ident × TSyntax `term × TSyntax `term) := do
    let f := mkIdent <| Name.append (structureFieldLabelTypeName base) sc.name
    let domainGetter ← `(term|($(fieldLabelToDomain base):ident $sortIdents*) $f:ident)
    let codomainGetter ← `(term|($(fieldLabelToCodomain base):ident $sortIdents*) $f:ident)
    return (f, domainGetter, codomainGetter)
  /-- Generate the abstract (canonical/functional) type for a field: `CanonicalField Domain Codomain`. -/
  fieldKindToAbstractType (sortIdents : Array Ident) (sc : StateComponent) : m (TSyntax `term) := do
    let (_, domainGetter, codomainGetter) ← fieldDomainCodomainGetters sortIdents sc
    `(term| $(mkIdent ``Veil.CanonicalField) $domainGetter $codomainGetter)
  /-- Generate the concrete type for a field based on its kind, using the configured representation. -/
  fieldKindToConcreteType (sortIdents : Array Ident) (repConfigs : ResolvedConcreteRepConfigs) (sc : StateComponent) : m (TSyntax `term) := do
    let (stateLabelCtor, domainGetter, codomainGetter) ← fieldDomainCodomainGetters sortIdents sc
    let (mapKeyTerm, mapValueTerm) := (← `(term| ($(mkIdent ``Veil.IteratedProd') <| $domainGetter)), codomainGetter)
    match sc.kind with
    | .individual => pure codomainGetter
    | .relation =>
      let allSomeCase ← `(term| $(mkIdent repConfigs.relationConfig.typeName) $mapKeyTerm)
      let notNecessarilyFiniteCase ← `($(mkIdent ``Veil.NotNecessarilyFinsetLikeUpdates.HybridFinsetLike) ($allSomeCase) ($domainGetter))
      chooseFieldConcreteTypeByEnumAllSomeCheck stateLabelCtor allSomeCase notNecessarilyFiniteCase
    | .function =>
      let allSomeCase ← `(term| $(mkIdent repConfigs.functionConfig.typeName) $mapKeyTerm $mapValueTerm)
      let notNecessarilyFiniteCase ← `($(mkIdent ``Veil.NotNecessarilyFinmapLikeUpdates.HybridFinmapLike) ($allSomeCase) ($domainGetter) ($codomainGetter))
      chooseFieldConcreteTypeByEnumAllSomeCheck stateLabelCtor allSomeCase notNecessarilyFiniteCase
    | .module => throwError "[fieldKindToConcreteType] module kind is not supported"
  /-- Choose between two concrete field types based on whether the domain is
  finite or not. -/
  chooseFieldConcreteTypeByEnumAllSomeCheck (stateLabelCtor allSomeCase notNecessarilyFiniteCase : Term) : m Term := do
    let body ← `(term| bif $instEnumerationForIteratedProdAllSomeCheck $stateLabelCtor then $allSomeCase else $notNecessarilyFiniteCase)
    `(veil_dsimp% [$instEnumerationForIteratedProdAllSomeCheck, $(mkIdent ``cond)] ($body))

/-! ## Instance Lifting Infrastructure (Private) -/

/-- Helper function to generate typeclass instance lifting declarations. -/
@[inline]
private def Module.declareInstanceLifting [Monad m] [MonadQuotation m] [MonadError m]
    (mod : Module) (assumingClasses : Array Name) (fieldLabelIdent : Ident)
    (instanceType : Term) (instanceName : Option Name := .none) (tactic : Option (TSyntax `tactic) := .none) : m Syntax := do
  let tactic := tactic.getD (← `(tactic| infer_instance_for_iterated_prod'))
  let assumedInstances ← assumingClasses.flatMapM fun className => mod.assumeForEverySort className
  let fieldLabel ← `(bracketedBinder|($fieldLabelIdent:ident : $(mkIdent `State.Label)))
  let binders := (← mod.sortBinders) ++ assumedInstances ++ [fieldLabel]
  match instanceName with
  | some name => `(scoped instance (priority := low) $(mkIdent name):ident $[$binders]* : $instanceType := by cases $fieldLabelIdent:ident <;> $tactic)
  | none => `(scoped instance (priority := low) $[$binders]* : $instanceType := by cases $fieldLabelIdent:ident <;> $tactic)

/-- NOTE: This is actually needed.-/
private def Module.declareInstanceLiftingForIteratedProd [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (deriveClass : Name) (assumingClasses : Array Name := #[deriveClass]) (instName : Option Name := .none) (tactic : Option (TSyntax `tactic) := .none) : m (Array Syntax) := do
  let (cls, sorts, fieldLabelIdent) := (mkIdent deriveClass, ← mod.sortIdents, mkVeilImplementationDetailIdent `f)
  let ty ← `(term | ($(mkIdent ``IteratedProd) <| ($(mkIdent ``List.map) $cls <| ($(fieldLabelToDomain stateName) $sorts*) $fieldLabelIdent)))
  let inst ← mod.declareInstanceLifting assumingClasses fieldLabelIdent ty instName tactic
  return #[inst]

/-- States that if every sort has an instance of `className` (e.g. `Ord node`),
then the domain has instances of that class.

[AutomaticallyInferred] NOTE: These typeclass instances can be automatically
inferred if `IteratedProd'`, `toDomain` and `toCodomain` are defined as
`abbrev`. We keep this code for explicitness, in case we want to change the
representation and typeclass inference will then fail. -/
private def Module.declareInstanceLiftingForDomain [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (deriveClass : Name) (assumingClasses : Array Name := #[deriveClass]) (instName : Option Name := .none) : m (Array Syntax) := do
  let (cls, sorts, fieldLabelIdent) := (mkIdent deriveClass, ← mod.sortIdents, mkVeilImplementationDetailIdent `f)
  let domainInst ← mod.declareInstanceLifting assumingClasses fieldLabelIdent (← `(term|$cls ($(mkIdent ``IteratedProd') (($(fieldLabelToDomain stateName) $sorts*) $fieldLabelIdent)))) instName
  return #[domainInst]
/-- States that if every sort has an instance of `className` (e.g. `Ord node`),
then the codomain has instances of that class. See NOTE [AutomaticallyInferred].-/
private def Module.declareInstanceLiftingForCodomain [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (deriveClass : Name) (assumingClasses : Array Name := #[deriveClass]) (instName : Option Name := .none) : m (Array Syntax) := do
  let (cls, sorts, fieldLabelIdent) := (mkIdent deriveClass, ← mod.sortIdents, mkVeilImplementationDetailIdent `f)
  let codomainInst ← mod.declareInstanceLifting assumingClasses fieldLabelIdent (← `(term|$cls (($(fieldLabelToCodomain stateName) $sorts*) $fieldLabelIdent))) instName
  return #[codomainInst]

/-- States that `deriveClass` can be inferred assuming `assumingClasses` for
every concrete type of every field. See NOTE [AutomaticallyInferred]. -/
private def Module.declareInstanceLiftingForDispatcher [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (deriveClass : Name) (assumingClasses : Array Name := #[deriveClass]) (dispatcher : Ident := fieldConcreteDispatcher) (instName : Option Name := .none) : m (Array Syntax) := do
  let (cls, sorts, fieldLabelIdent) := (mkIdent deriveClass, ← mod.sortIdents, mkVeilImplementationDetailIdent `f)
  let inst ← mod.declareInstanceLifting assumingClasses fieldLabelIdent (← `(term|$cls ($dispatcher $sorts* $fieldLabelIdent))) instName
  return #[inst]

/-! ## Public Field Label & Dispatcher Declaration -/

/-- Return the syntax for declaring `State.Label` and dispatchers; also
update the module to include the new parameters for concrete field type,
`FieldRepresentation` and `LawfulFieldRepresentation`. -/
def Module.declareStateFieldLabelTypeAndDispatchers [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (repConfigs : ResolvedConcreteRepConfigs) : m (Module × Array Syntax) := do
  let components := mod.mutableComponents
  -- this might be useful later, so store it as metadata in the module
  let argTypesAsMap : Std.HashMap Name (Array Term) := Std.HashMap.ofList (components.zipWith (fun sc args => (sc.name, args)) (components.map (·.domainTerms)) |>.toList)
  -- declare field label type
  let (stateLabelTypeName, stateLabelTypeDefStx) ← declareStructureFieldLabelType stateName components
  -- declare field dispatchers
  let (dispatchers, (fieldAbstractTypeName, fieldAbstractTypeStx), (fieldConcreteTypeName', fieldConcreteTypeStx)) ← mod.declareFieldDispatchers stateName components (← mod.sortBinders) repConfigs
  let (dispatcherNames, dispatcherStxs) := Array.unzip dispatchers
  for name in (#[stateLabelTypeName, fieldAbstractTypeName, fieldConcreteTypeName'] ++ dispatcherNames) do
    mod.throwIfAlreadyDeclared name
  -- declare liftings for needed instances
  -- FIXME: this specific instance is really required; the rest can be automatically inferred (see NOTE [AutomaticallyInferred])
  let specificInstances ← #[``OptionalEnumeration].flatMapM fun inst => return (← mod.declareInstanceLiftingForIteratedProd inst (assumingClasses := #[``Enumeration]) (instName := instEnumerationForIteratedProdName)
    (tactic := (← `(tactic| (unfold $(mkIdent ``Veil.OptionalEnumeration) $(mkIdent ``Function.comp) ; infer_instance_for_iterated_prod)))))
  -- define the all-some checker
  let allSomeCheckStx ← OptionalTC.genAllSomePredicateCmd instEnumerationForIteratedProdName instEnumerationForIteratedProdAllSomeCheckName
  -- NOTE: not actually needed, but left here for completeness to document what needs to exist
  -- let instances ← #[``Enumeration, ``Ord, ``ToJson].flatMapM fun inst => return (← mod.declareInstanceLiftingForDomain inst) ++ (← mod.declareInstanceLiftingForCodomain inst)
  let instances : Array Syntax := #[]
  -- Use the domain type instances from the config for instance lifting
  let abstractInstances ← #[(``ToJson, #[``ToJson, ``Enumeration])].flatMapM fun (deriveClass, assumingClasses) => mod.declareInstanceLiftingForDispatcher deriveClass assumingClasses (dispatcher := fieldAbstractDispatcher)
  -- add the `fieldConcreteType` parameter
  let fieldConcreteTypeParam ← Parameter.fieldConcreteType
  -- add the `FieldRepresentation` and `LawfulFieldRepresentation` typeclass parameters
  let f := mkVeilImplementationDetailIdent `f
  let paramsArgs ← mod.sortIdents
  let toDomainTerm ← `(($(fieldLabelToDomain stateName) $paramsArgs* $f))
  let toCodomainTerm ← `(($(fieldLabelToCodomain stateName) $paramsArgs* $f))
  let fieldConcreteTypeApplied ← `(($fieldConcreteType $f))
  let fieldRepType ← `(∀ $f, $(mkIdent ``FieldRepresentation) $toDomainTerm $toCodomainTerm $fieldConcreteTypeApplied)
  let fieldRep : Parameter := { kind := .moduleTypeclass .fieldRepresentation, name := fieldRepresentationName, «type» := fieldRepType, userSyntax := .missing }
  let lawfulFieldRepType ← `(∀ $f, $(mkIdent ``LawfulFieldRepresentation) $toDomainTerm $toCodomainTerm $fieldConcreteTypeApplied ($fieldRepresentation $f))
  let lawfulFieldRep : Parameter := { kind := .moduleTypeclass .lawfulFieldRepresentation, name := lawfulFieldRepresentationName, «type» := lawfulFieldRepType, userSyntax := .missing }
  return ({ mod with parameters := mod.parameters ++ #[fieldConcreteTypeParam, fieldRep, lawfulFieldRep] ,
                     _declarations := mod._declarations.insert fieldConcreteTypeParam.name .moduleParameter ,
                     _fieldRepMetaData := argTypesAsMap }, (#[stateLabelTypeDefStx] ++ dispatcherStxs ++ #[fieldAbstractTypeStx] ++ specificInstances ++ #[allSomeCheckStx] ++ instances ++ #[fieldConcreteTypeStx] ++ abstractInstances))

end Veil
