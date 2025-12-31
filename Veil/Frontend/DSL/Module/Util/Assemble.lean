import Veil.Frontend.DSL.Module.Util.LocalRProp
import Veil.Core.Tools.ModelChecker.TransitionSystem

open Lean Parser Elab Command Term Meta Tactic

namespace Veil

/-! ## Assertion Definition -/

/-- Register the assertion (and any optional `Decidable` instances)
in the module, and return the syntax to elaborate. -/
def Module.defineAssertion (mod : Module) (base : StateAssertion) : CommandElabM (Command × Module) := do
  mod.throwIfAlreadyDeclared base.name
  let mut mod := mod
  let justTheory := match base.kind with | .assumption => true | _ => false
  let (extraParams, thstBinders, term, _) ← liftTermElabM $ mod.mkVeilTerm base.name base.declarationKind (params := .none) base.term (justTheory := justTheory)
  mod ← mod.registerAssertion { base with extraParams := extraParams }
  -- This includes the required `Decidable` instances
  let (binders, _) ← mod.declarationAllParamsMapFn (·.binder) base.name base.declarationKind
  -- NOTE(SUBTLE): we do something counter-intuitive here. Making the `ρ` and `σ`
  -- arguments implicit ensures that whenever the default values for `thstBinders`
  -- are evaluated (i.e. not provided explicitly), the assertion is forced to be
  -- evaluated with `ρ := Theory` and `σ := State`. This makes it possible to do
  -- things like `assert invariant` in action without having to provide any
  -- explicit arguments.
  let preBinders ← binders.mapM mkImplicitBinder
  let binders := preBinders ++ thstBinders
  let attrs ← #[`invSimp].mapM (fun attr => `(attrInstance| $(Lean.mkIdent attr):ident))
  let stx ← `(@[$attrs,*] abbrev $(mkIdent base.name) $[$binders]* := $term)
  return (stx, mod)

/-! ## Derived Definition Management -/

def Module.registerDerivedDefinition [Monad m] [MonadError m] [MonadQuotation m] (mod : Module) (ddef : DerivedDefinition) : m Module := do
  mod.throwIfAlreadyDeclared ddef.name
  return { mod with _declarations := mod._declarations.insert ddef.name ddef.declarationKind, _derivedDefinitions := mod._derivedDefinitions.insert ddef.name ddef }

def Module.defineGhostRelation (mod : Module) (name : Name) (params : Option (TSyntax `Lean.explicitBinders)) (term : Term) (justTheory : Bool := false) : CommandElabM (Command × Module) := do
  mod.throwIfAlreadyDeclared name
  let kind? := .stateAssertion .invariant -- a ghost relation is a predicate that depends on the state
  let ddKind : DerivedDefinitionKind := if justTheory then .theoryGhost else .ghost
  let dk : DeclarationKind := .derivedDefinition ddKind (Std.HashSet.emptyWithCapacity 0)
  let (baseParams, _) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) dk
  let (extraParams, thstBinders, term, _) ← liftTermElabM $ mod.mkVeilTerm name kind? params term justTheory
  let params := (← explicitBindersToParameters params name) ++ (← thstBinders.mapM (bracketedBinderToParameter · name))
  let baseBinders ← (baseParams ).mapM (·.binder)
  -- FIXME: for the following line, we implicitly assume that this is the order in
  -- which binders get generated for the definition. We should instead first
  -- create a definition without `stx`, use the relevant functions to get the
  -- binders, and then create the syntax.
  -- See NOTE(SUBTLE).
  let binders := (← baseBinders.mapM mkImplicitBinder) ++ (← params.mapM (·.binder)) ++ (← extraParams.mapM (·.binder))
  let attrs ← #[(if justTheory then `invSimp else `ghostRelSimp)].mapM (fun attr => `(attrInstance| $(Lean.mkIdent attr):ident))
  let stx ← `(@[$attrs,*] abbrev $(mkIdent name) $[$binders]* := $term)
  trace[veil.debug] "stx: {stx}"
  let ddef : DerivedDefinition := { name := name, kind := ddKind, params := params, extraParams := extraParams, derivedFrom := Std.HashSet.emptyWithCapacity 0, stx := stx }
  let mod ← mod.registerDerivedDefinition ddef
  return (stx, mod)

/-! ## Assertion Assembly (Private) -/

private def Module.assembleAssertions [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (kind : DerivedDefinitionKind) (assembledName : Name) (specificBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) (onlySafety : Bool := false) : m (Command × Module) := do
  mod.throwIfAlreadyDeclared assembledName
  let assertions ← match kind with
    | .assumptionLike => pure mod.assumptions
    | .invariantLike => pure (if onlySafety then mod.safeties else mod.invariants)
    | _ => throwError s!"[Module.assembleAssertions] invalid kind: {repr kind}"
  let conjunctsSet := Std.HashSet.ofArray $ assertions.map (·.name)
  let (baseParams, extraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition kind conjunctsSet)
  let specificArgs ← bracketedBindersToTerms specificBinders
  let apps ← assertions.mapM (fun a => do
    let (params, _) ← mod.declarationAllParams a.name a.declarationKind
    let args ← params.mapM (·.arg)
    `(term| @$(mkIdent a.name):ident $args* $specificArgs*))
  let body ← repeatedAnd apps
  let binders ← (baseParams ++ extraParams).mapM (·.binder)
  -- The `reducible` is needed such that we can apply lemmas like
  -- `triple_strengthen_postcondition` without unfolding the definition of
  -- `Invariants`. Note that for this to work, the definition must return
  -- `Prop` rather than `Bool`. TODO: a Bool-specific weakening?
  let attrs ← #[`derivedInvSimp, `invSimp, `reducible].mapM (fun attr => `(attrInstance| $(Lean.mkIdent attr):ident))
  let cmd ← `(command|@[$attrs,*] def $(mkIdent assembledName) $[$(binders)]* $specificBinders* : Prop := $body)
  let derivedDef : DerivedDefinition := { name := assembledName, kind := kind, params := #[], extraParams := extraParams, derivedFrom := conjunctsSet, stx := cmd }
  let mod ← mod.registerDerivedDefinition derivedDef
  return (cmd, mod)

/-! ## Public Assembly Methods -/

/-- Syntax for the conjunction of all `invariant`, `safety`, and
`trusted invariant` clauses. This modifies the `Module` to record which
parameters are necessary for this definition. -/
def Module.assembleInvariants [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Command × Module) := do
  let binders := #[← `(bracketedBinder| ($(mkIdent `rd) : $environmentTheory)), ← `(bracketedBinder| ($(mkIdent `st) : $environmentState))]
  mod.assembleAssertions .invariantLike assembledInvariantsName binders

def Module.assembleAssumptions [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Command × Module) := do
  let binders := #[← `(bracketedBinder| ($(mkIdent `rd) : $environmentTheory))]
  mod.assembleAssertions .assumptionLike assembledAssumptionsName binders

def Module.assembleSafeties [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Command × Module) := do
  let binders := #[← `(bracketedBinder| ($(mkIdent `rd) : $environmentTheory)), ← `(bracketedBinder| ($(mkIdent `st) : $environmentState))]
  mod.assembleAssertions .invariantLike assembledSafetiesName binders (onlySafety := true)

/-! ## Label Type Utilities -/

def Module.labelTypeStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m Term := do
  `(term|$labelType $(← mod.sortIdents)*)

/-! ## Label Assembly (Private) -/

private def Module.assembleLabelDef [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Command × Module) := do
  mod.throwIfAlreadyDeclared labelTypeName
  let labelT ← mod.labelTypeStx
  let actionNames := Std.HashSet.ofArray $ mod.actions.map (·.name)
  let ctors ← mod.actions.mapM (fun a => do
    `(Command.ctor| | $(mkIdent a.name):ident $(← a.binders)* : $labelT ))
  let labelDef ← do
    let instances := #[``DecidableEq,``Repr, ``ToJson].map Lean.mkIdent
    if ctors.isEmpty then
      `(inductive $labelType $(← mod.sortBinders)* where $[$ctors]* deriving $[$instances:ident],*)
    else
      let instances := instances ++ #[``Inhabited, ``Nonempty].map Lean.mkIdent
      `(inductive $labelType $(← mod.sortBinders)* where $[$ctors]* deriving $[$instances:ident],*)
  let derivedDef : DerivedDefinition := { name := labelTypeName, kind := .stateLike, params := #[], extraParams := #[], derivedFrom := actionNames, stx := labelDef }
  let mod ← mod.registerDerivedDefinition derivedDef
  return (labelDef, mod)

private def Module.assembleLabelCasesLemma [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Command × Module) := do
  mod.throwIfAlreadyDeclared labelCasesName
  let P := mkIdent `P
  let labelT ← mod.labelTypeStx
  let exs ← mod.actions.mapM (fun a => do
    let constructor := Lean.mkIdent $ labelTypeName ++ a.name
    match a.params with
    | #[] => `(term| $P ($constructor))
    | params =>
      let br ← parametersToExplicitBinders params
      `(term| (∃ $br, $P ($constructor $(← explicitBindersToTerms br)*))))
  let label := mkIdent `label
  let casesLemma ← `(command|set_option linter.unusedSectionVars false in
    theorem $labelCases ($P : $labelT -> Prop) :
      (∃ $label:ident : $labelT, $P $label) ↔
      $(← repeatedOr exs) :=
    by
      constructor
      { rintro ⟨$(mkIdent `l), $(mkIdent `r)⟩; rcases $(mkIdent `l):ident <;> aesop }
      { aesop })
  let derivedDef : DerivedDefinition := { name := labelCasesName, kind := .stateLike, params := #[], extraParams := #[], derivedFrom := {labelTypeName}, stx := casesLemma }
  let mod ← mod.registerDerivedDefinition derivedDef
  return (casesLemma, mod)

def Module.mkLabelEnumeration [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m Command := do
  let binders := (← mod.sortBinders) ++ (← #[``DecidableEq, ``FinEnum].flatMapM mod.assumeForEverySort)
  let labelT ← mod.labelTypeStx
  `(instance $[$binders]* : $(mkIdent ``Veil.Enumeration) ($labelT) where
    $(mkIdent `allValues):ident := ($(mkIdent ``FinEnum.ofEquiv) _ ($(mkIdent ``Equiv.symm) (proxy_equiv% ($labelT)))).toList
    $(mkIdent `complete):ident := by simp)
where
  assumeForEverySort (className : Name) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
    (← mod.sortIdents).mapM fun sort => do
      `(bracketedBinder|[$(mkIdent className) $sort])

def Module.mkInstantiationStructure [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m Command := do
  let sortParams := mod.sortParams
  let fields ← sortParams.mapM fun (param, sortKind) => do
    let sort ← param.ident
    match sortKind with
    | .enumSort =>
      -- Enum type: add default value of SortName_IndT
      let defaultType := Ident.toEnumConcreteType sort
      `(Command.structSimpleBinder| $sort:ident : Type := $defaultType)
    | .uninterpretedSort =>
      -- Regular sort: no default
      `(Command.structSimpleBinder| $sort:ident : Type)
  let instances := #[``Inhabited, ``Repr].map Lean.mkIdent
  `(structure $instantiationType where $[$fields]* deriving $[$instances:ident],*)

/-! ## Public Label Assembly -/

def Module.assembleLabel [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Array Command × Module) := do
  let (labelDef, mod) ← mod.assembleLabelDef
  let (casesLemma, mod) ← mod.assembleLabelCasesLemma
  let labelEnumeration ← mod.mkLabelEnumeration
  return (#[labelDef, casesLemma, labelEnumeration], mod)

/-! ## Next Action Assembly -/

def Module.assembleNext [Monad m] [MonadQuotation m] [MonadError m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] (mod : Module) : m (Command × Module) := do
  mod.throwIfAlreadyDeclared assembledNextActName
  let actionNames := Std.HashSet.ofArray $ mod.actions.map (·.name)
  let (baseParams, extraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition .actionLike actionNames)
  let binders ← (baseParams ++ extraParams).mapM (·.binder)
  let acts ← mod.actions.mapM (fun s => do
    let name := Lean.mkIdent $ toExtName s.name
    let (params, _) ← mod.declarationAllParams s.name s.declarationKind
    let args ← params.mapM (·.arg)
    `(@$name $args*))
  let labelT ← mod.labelTypeStx
  let nextT ← `(term|$labelT → $(mkIdent ``VeilM) $(mkIdent ``Mode.external) $environmentTheory $environmentState $(mkIdent ``Unit))
  let label := mkIdent `label
  let casesOn := mkIdent $ Name.append label.getId `casesOn
  let attrs ← #[`nextSimp].mapM (fun attr => `(attrInstance| $(Lean.mkIdent attr):ident))
  let nextDef ← `(command|@[$attrs,*] def $assembledNextAct $[$(binders)]* : $nextT := fun ($label : $labelT) => $casesOn $acts*)
  let nextParam := { kind := .definitionParameter assembledNextActName .explicit, name := label.getId, «type» := labelT, userSyntax := .missing }
  let derivedDef : DerivedDefinition := { name := assembledNextActName, kind := .actionLike, params := #[nextParam], extraParams := extraParams, derivedFrom := actionNames, stx := nextDef }
  let mod ← mod.registerDerivedDefinition derivedDef
  return (nextDef, mod)

/-! ## Next Transition Relation Assembly -/

/-- Assembles the `Next` transition relation from `NextAct`.
`Next rd st l st'` holds iff there exists an execution of `NextAct l`
from state `(rd, st)` to state `(rd, st')`. -/
def Module.assembleNextTransition [Monad m] [MonadQuotation m] [MonadError m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] (mod : Module) : m (Command × Module) := do
  mod.throwIfAlreadyDeclared assembledNextName
  let actionNames := Std.HashSet.ofArray $ mod.actions.map (·.name)
  let (baseParams, extraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition .actionLike actionNames)
  let binders ← (baseParams ++ extraParams).mapM (·.binder)
  let labelT ← mod.labelTypeStx
  let nextTrT ← `(term| $environmentTheory → $environmentState → $labelT → $environmentState → Prop)
  let (rd, st, st', label) := (mkIdent `rd, mkIdent `st, mkIdent `st', mkIdent `label)
  let (nextActParams, _) ← mod.declarationAllParams assembledNextActName (.derivedDefinition .actionLike actionNames)
  let nextActArgs ← nextActParams.mapM (·.arg)
  let body ← `(term| (@$assembledNextAct $nextActArgs* $label).toTransitionDerived $rd $st $st')
  let attrs ← #[`actSimp, `nextSimp].mapM (fun attr => `(attrInstance| $(Lean.mkIdent attr):ident))
  let nextTrDef ← `(command|
    @[$attrs,*] def $assembledNext $[$(binders)]* : $nextTrT :=
      fun ($rd : $environmentTheory) ($st : $environmentState) ($label : $labelT) ($st' : $environmentState) => $body)
  let derivedDef : DerivedDefinition := { name := assembledNextName, kind := .actionLike, params := #[], extraParams := extraParams, derivedFrom := {assembledNextActName}, stx := nextTrDef }
  let mod ← mod.registerDerivedDefinition derivedDef
  return (nextTrDef, mod)

/-! ## Init Predicate Assembly -/

/-- Assembles the `Init` predicate from the initializer.
`Init rd st` holds iff `st` is a valid initial state under theory `rd`. -/
def Module.assembleInit [Monad m] [MonadQuotation m] [MonadError m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] (mod : Module) : m (Command × Module) := do
  mod.throwIfAlreadyDeclared assembledInitName
  -- Get the initializer transition name
  let initTrName := Lean.mkIdent $ toTransitionName (toExtName initializerName)
  -- Get parameters for the initializer
  let (initParams, _) ← mod.declarationAllParams initializerName (.procedure .initializer)
  let initArgs ← initParams.mapM (·.arg)
  -- Get base parameters
  let initExtraParams := Array.flatten <|
    mod.procedures.filterMap (fun a => if initializerName == a.name then .some a.extraParams else .none)
  let actionNames := Std.HashSet.ofArray $ mod.actions.map (·.name)
  let (baseParams, extraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition .actionLike actionNames)
  -- We need `Inhabited σ` since we use `default` as the pre-state
  let inhType ← `(term| $(mkIdent ``Inhabited).{1} $environmentState)
  let inhParam : Parameter := { kind := .definitionParameter assembledInitName .typeclass, name := `σ_inhabited, «type» := inhType, userSyntax := .missing }
  let initExtraParams := initExtraParams.push inhParam
  let binders ← (baseParams ++ extraParams ++ initExtraParams).mapM (·.binder)
  let initT ← `(term| $environmentTheory → $environmentState → Prop)
  let (rd, st) := (mkIdent `rd, mkIdent `st)
  -- We use `default` as the pre-state; this matches the behaviour in the explicit model checker
  let body ← `(term| @$initTrName $initArgs* $rd $(mkIdent ``default) $st)
  let attrs ← #[`actSimp, `nextSimp].mapM (fun attr => `(attrInstance| $(Lean.mkIdent attr):ident))
  let initDef ← `(command|
    @[$attrs,*] def $assembledInit $[$(binders)]* : $initT :=
      fun ($rd : $environmentTheory) ($st : $environmentState) => $body)
  let derivedDef : DerivedDefinition := { name := assembledInitName, kind := .actionLike, params := #[], extraParams := extraParams ++ initExtraParams, derivedFrom := {initializerName}, stx := initDef }
  let mod ← mod.registerDerivedDefinition derivedDef
  return (initDef, mod)

/-! ## Relational Transition System Assembly -/

/-- Assembles a `RelationalTransitionSystem` instance combining `Assumptions`, `Init`, and `Next`.
    This is a noncomputable definition that uses Classical logic. -/
def Module.assembleRelationalTransitionSystem [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Command × Module) := do
  mod.throwIfAlreadyDeclared assembledRTSName
  let sorts ← mod.sortIdents
  -- Sort binders: (node : Type)
  let sortBinders ← mod.sortBinders
  -- Inhabited instances for every sort: [Inhabited node]
  let inhabitedBinders ← mod.assumeForEverySort ``Inhabited
  -- User-defined typeclass parameters
  let userDefinedParams : Array Parameter := mod.parameters.filter fun p =>
    match p.kind with
    | .moduleTypeclass .userDefined => true
    | _ => false
  let userDefinedBinders ← userDefinedParams.mapM (·.binder)
  let allBinders := sortBinders ++ inhabitedBinders ++ userDefinedBinders
  -- Construct type arguments
  let theoryT ← mod.theoryStx
  let stateT ← `(term| $(mkIdent stateName) ($fieldAbstractDispatcher $sorts*))
  let labelT ← `(term| $labelType $sorts*)
  -- Construct the RTS type
  let rtsType ← `(term| $(mkIdent ``RelationalTransitionSystem) $theoryT $stateT $labelT)
  -- Construct field values with explicit type annotations
  let (ρArg, σArg, χArg) := (mkIdent `ρ, mkIdent `σ, mkIdent `χ)
  let assumptionsVal ← `(term| $assembledAssumptions ($ρArg := $theoryT) $sorts*)
  let initVal ← `(term| $assembledInit ($ρArg := $theoryT) ($σArg := $stateT) ($χArg := $fieldAbstractDispatcher $sorts*) $sorts*)
  let nextVal ← `(term| $assembledNext ($ρArg := $theoryT) ($σArg := $stateT) ($χArg := $fieldAbstractDispatcher $sorts*) $sorts*)
  -- Generate the definition
  let attrs ← #[`actSimp, `nextSimp].mapM (fun attr => `(attrInstance| $(Lean.mkIdent attr):ident))
  let rtsDef ← `(command|
    open Classical in
    @[$attrs,*] noncomputable def $assembledRTS $[$allBinders]* : $rtsType where
      assumptions := $assumptionsVal
      init := $initVal
      tr := $nextVal)
  -- Register as derived definition
  let derivedFrom := Std.HashSet.ofArray #[assembledAssumptionsName, assembledInitName, assembledNextName]
  let derivedDef : DerivedDefinition := { name := assembledRTSName, kind := .actionLike, params := #[], extraParams := userDefinedParams, derivedFrom := derivedFrom, stx := rtsDef }
  let mod ← mod.registerDerivedDefinition derivedDef
  return (rtsDef, mod)

end Veil
