module

public meta import Lean
public meta import Lean.Meta.Tactic.TryThis
public meta import Veil.Base
public meta import Veil.Frontend.DSL.Module.Syntax
public meta import Veil.Frontend.DSL.Infra.EnvExtensions
public meta import Veil.Frontend.DSL.Module.Util
public meta import Veil.Frontend.DSL.Module.Util.ExecutionWorkflow
public meta import Veil.Frontend.DSL.Action.Elaborators
public meta import Veil.Frontend.DSL.State.SubState
public meta import Veil.Frontend.DSL.State.ConcreteRegistry
public meta import Veil.Core.UI.Trace.TraceDisplay
public meta import Veil.Core.Tools.ModelChecker.Concrete.Checker
public meta import Veil.Core.Tools.ModelChecker.Simulation
public meta import Veil.Frontend.DSL.Action.Extract
public meta import Veil.Frontend.DSL.Module.Util.Enumeration
public meta import Veil.Util.Multiprocessing
public meta import Veil.Frontend.DSL.Module.AssertionInfo

public meta section

open Lean Parser Elab Command Term
open scoped Veil.Extract

namespace Veil

/-- Extract the name identifier from a Veil procedure/transition/ghost syntax.
    Returns `unknown if the syntax doesn't match any known pattern. -/
def extractDefinitionName (stx : Syntax) : Name :=
  match stx with
  -- procedureDefinition (without spec)
  | `(command|action $nm:ident $_br:explicitBinders ? {$_l:doSeq}) => nm.getId
  | `(command|procedure $nm:ident $_br:explicitBinders ? {$_l:doSeq}) => nm.getId
  -- procedureDefinitionWithSpec
  | `(command|action $nm:ident $_br:explicitBinders ? $_spec:doSeq {$_l:doSeq}) => nm.getId
  | `(command|procedure $nm:ident $_br:explicitBinders ? $_spec:doSeq {$_l:doSeq}) => nm.getId
  -- transitionDefinition
  | `(command|transition $nm:ident $_br:explicitBinders ? { $_t:term }) => nm.getId
  -- ghostRelationDefinition
  | `(command|ghost relation $nm:ident $_br:explicitBinders ? := $_t:term) => nm.getId
  | `(command|theory ghost relation $nm:ident $_br:explicitBinders ? := $_t:term) => nm.getId
  -- ghostFunctionDefinition
  | `(command|ghost function $nm:ident $_br:explicitBinders ? $[: $_tp:term]? := $_t:term) => nm.getId
  | `(command|theory ghost function $nm:ident $_br:explicitBinders ? $[: $_tp:term]? := $_t:term) => nm.getId
  | _ => `unknown

private def overrideLeanDefaults : CommandElabM Unit := do
  -- FIXME: make this go through `elabVeilCommand` so it shows up in desugaring
  for (name, value) in veilDefaultOptions do
    modifyScope fun scope => { scope with opts := scope.opts.insert name value }

private def checkVeilIsPubliclyImported (stx : Syntax) : CommandElabM Unit := do
  if ((← getEnv).setExporting true).find? ``Veil.Enumeration |>.isSome then return
  logErrorAt stx "Veil is only imported into this module's private scope, but `veil module` \
    elaborates its generated declarations into the public scope. Write `public import Veil` \
    instead of `import Veil` at the top of this file."

@[command_elab Veil.moduleDeclaration]
def elabModuleDeclaration : CommandElab := fun stx => do
  match stx with
  | `(veil module $modName:ident) => do
    /- `veil module` elaborates the declarations it generates into the public scope, so every
    Veil name their signatures and bodies mention must be publicly visible as well. A plain
    `import Veil` only reaches the private scope; without this check that surfaces much later,
    as a wall of unknown-identifier errors from `#gen_state`. `setExporting` is a no-op outside
    the module system, so files without a `module` header are unaffected. -/
    checkVeilIsPubliclyImported stx
    overrideLeanDefaults
    let genv ← globalEnv.get
    let name := modName.getId
    let lenv ← localEnv.get
    if let some mod := lenv.currentModule then
      throwError s!"Module {mod.name} is already open, but you are now trying to open module {name}. Nested modules are not supported!"
    elabVeilCommand $ ← `(open Veil)
    elabVeilCommand $ ← `(namespace $modName)
    -- Generated declarations form the reusable API of a Veil module. Scope these
    -- defaults to its namespace, so `end` restores the surrounding Lean defaults.
    let exposeAttr ← `(Parser.Term.attrInstance| expose)
    modifyScope fun scope => { scope with isPublic := true, attrs := exposeAttr :: scope.attrs }
    if genv.containsModule name then
      logInfo m!"Module {name} has been previously defined. Importing it here."
      let mod := genv.modules[name]!
      localEnv.modifyModule (fun _ => mod)
    else
      let mod ← Module.freshWithName name
      localEnv.modifyModule (fun _ => mod)
  | _ => throwUnsupportedSyntax

@[command_elab Veil.typeDeclaration]
def elabTypeDeclaration : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare a type outside of a Veil module!")
  mod.throwIfStateAlreadyDefined
  match stx with
  | `(type $id:ident) => do
      let mod ← mod.declareUninterpretedSort id.getId stx
      localEnv.modifyModule (fun _ => mod)
  | _ => throwUnsupportedSyntax

@[command_elab Veil.parameterDeclaration]
def elabParameterDeclaration : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare a parameter outside of a Veil module!")
  mod.throwIfStateAlreadyDefined
  let (id, tp) ← match stx with
  | `(param $id:ident : $tp:term) => pure (id, tp)
  | _ => throwUnsupportedSyntax
  let nm := id.getId
  mod.throwIfAlreadyDeclared nm
  let p : Parameter := { kind := .userParameter, name := nm, «type» := tp, userSyntax := stx }
  let newMod := { mod with parameters := mod.parameters.push p, _declarations := mod._declarations.insert nm .moduleParameter }
  localEnv.modifyModule (fun _ => newMod)

@[command_elab Veil.stateComponentDeclaration]
def elabStateComponent : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare a state component outside of a Veil module!")
  mod.throwIfStateAlreadyDefined
  let new_mod : Module ← match stx with
  | `($mutab:stateMutability ? $kind:stateComponentKind $name:ident $br:bracketedBinder* : $dom:term) =>
    defineStateComponentFromSyntax mod mutab kind name br dom stx
  | `(command|$mutab:stateMutability ? relation $name:ident $br:bracketedBinder*) => do
    defineStateComponentFromSyntax mod mutab (← `(stateComponentKind|relation)) name br (← `(term|$(mkIdent ``Bool))) stx
  | _ => throwUnsupportedSyntax
  localEnv.modifyModule (fun _ => new_mod)
where
  defineStateComponentFromSyntax
  (mod : Module) (mutability : Option (TSyntax `stateMutability)) (kind : TSyntax `stateComponentKind)
  (name : Ident) (br : TSyntaxArray ``Term.bracketedBinder) (dom : Term) (userStx : Syntax) : CommandElabM Module := do
    let mutability := Mutability.fromStx mutability
    let kind := StateComponentKind.fromStx kind
    let sctype ← (
      if br.isEmpty then
        return StateComponentType.simple (← `(Command.structSimpleBinder|$name:ident : $dom))
      else
        return StateComponentType.complex br dom)
    let (domainTerms, codomainTerm) ← analyzeTypesOfStateComponents sctype
    let sc : StateComponent := { mutability := mutability, kind := kind, name := name.getId, «type» := sctype, userSyntax := userStx, domainTerms, codomainTerm }
    Module.declareStateComponent mod sc
  /-- For each `sc` in `components`, analyze its type to extract the arguments
  (domain) and codomain. -/
  analyzeTypesOfStateComponents (sct : StateComponentType) : CommandElabM (Array Term × Term) := do
    match sct with
    | .simple t =>
      let (domainTerms, codomainTerm) ← getSimpleBinderType t >>= splitForallArgsCodomain
      pure (domainTerms, codomainTerm)
    | .complex b codomainTerm =>
      -- overlapped with `complexBinderToSimpleBinder`
      let domainTerms ← b.mapM fun m => match m with
        | `(bracketedBinder| ($_arg:ident : $tp:term)) => return tp
        | _ => throwError "unable to extract type from binder {m}"
      pure (domainTerms, codomainTerm)

@[command_elab Veil.instanceDeclaration]
def elabInstantiate : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot instantiate a typeclass outside of a Veil module!")
  mod.throwIfStateAlreadyDefined
  let new_mod : Module ← match stx with
  | `(instantiate $inst:ident : $tp:term) => do
    let p : Parameter := { kind := .moduleTypeclass .userDefined, name := inst.getId, «type» := tp, userSyntax := stx }
    pure { mod with parameters := mod.parameters.push p }
  | _ => throwUnsupportedSyntax
  localEnv.modifyModule (fun _ => new_mod)

@[command_elab Veil.concreteRepresentationDecl]
def elabConcreteRepresentation : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot configure concrete representation outside of a Veil module!")
  mod.throwIfStateAlreadyDefined
  match stx with
  | `(veil_set_field_representation $c:concreteRepField $typeName:ident) => do
    let kind := match c with
      | `(concreteRepField| relation) => StateComponentKind.relation
      | `(concreteRepField| function) => StateComponentKind.function
      | _ => unreachable!
    let name := typeName.getId
    -- Verify the type is registered in the registry
    let some cfg ← ConcreteRepRegistry.lookupConcreteRep name
      | throwErrorAt typeName s!"Unknown concrete representation type '{name}'"
    unless (cfg.kind == .finsetLike && kind == StateComponentKind.relation) ||
            (cfg.kind == .finmapLike && kind == StateComponentKind.function) ||
            (cfg.kind == .canonical && (kind == StateComponentKind.relation || kind == StateComponentKind.function)) do
      throwErrorAt typeName s!"Concrete representation '{name}' is not compatible with state component kind '{kind}'"
    let new_mod := { mod with _concreteRepConfig := mod._concreteRepConfig.insert kind name }
    localEnv.modifyModule (fun _ => new_mod)
  | _ => throwUnsupportedSyntax

@[command_elab Veil.enumDeclaration]
def elabEnumDeclaration : CommandElab := fun stx => do
  match stx with
  | `(enum $id:ident = { $[$elems:ident],* }) => do
    -- Declare the enum sort (using .enumSort instead of .uninterpretedSort)
    let mod ← getCurrentModule (errMsg := "You cannot declare an enum outside of a Veil module!")
    mod.throwIfStateAlreadyDefined
    let mod ← mod.declareUninterpretedSort id.getId stx .enumSort
    localEnv.modifyModule (fun _ => mod)
    -- Declare an axiomatisation class for the enum type
    let (class_name, class_decl) ← mkEnumAxiomatisation id elems
    elabVeilCommand class_decl
    -- Declare the concrete type and show it satisfies the axiomatisation
    for cmd in (← mkEnumConcreteType id elems) do
      elabVeilCommand cmd
    -- Add the enum to the Veil DSL environment
    let instanceV ← `(command|instantiate $(Ident.toEnumInst id) : @$class_name $id)
    trace[veil.debug] "Elaborated enum instance: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic instanceV}"
    elabVeilCommand instanceV
    elabVeilCommand $ ← `(open $class_name:ident)
  | _ => throwUnsupportedSyntax

/-- Check if the syntax stack contains a Veil procedure context.
    Returns true if we're inside an `after_init`, `action`, `procedure`, or `transition` block. -/
def isVeilProcedureContext (stack : Syntax.Stack) : Bool :=
  stack.any fun (s, _) =>
    s.isOfKind `Veil.initializerDefinition ||
    s.isOfKind `Veil.procedureDefinition ||
    s.isOfKind `Veil.procedureDefinitionWithSpec ||
    s.isOfKind `Veil.transitionDefinition

/-- Instruct the linter to not mark state variables as unused in our
  `after_init` and `action` definitions. Also ignores capitalized identifiers
  (universally quantified variables) in Veil procedure contexts. -/
private def generateIgnoreFn (mod : Module) : CommandElabM Unit := do
  let cmd ← Command.runTermElabM fun _ => do
    let fnIdents ← mod.mutableComponents.mapM (fun sc => `($(quote sc.name)))
    let namesArrStx ← `(#[$[$fnIdents],*])
    let id := mkIdent `id
    let stack := mkIdent `stack
    -- Ignore if:
    -- 1. The identifier is a state component name (existing behavior), OR
    -- 2. The identifier is capitalized (universally quantified) AND we're in a Veil procedure context
    let fnStx ← `(fun $id $stack _ =>
      $(mkIdent ``Array.contains) ($namesArrStx) ($(mkIdent ``Lean.Syntax.getId) $id) ||
      ($(mkIdent ``Veil.isCapital) ($(mkIdent ``Lean.Syntax.getId) $id) && $(mkIdent ``Veil.isVeilProcedureContext) $stack))
    let nm := mkIdent `ignoreStateFields
    let ignoreFnStx ← `(@[$(mkIdent `unused_variables_ignore_fn):ident] meta def $nm : $(mkIdent ``Lean.Linter.IgnoreFunction) := $fnStx)
    return ignoreFnStx
  elabVeilCommand cmd


/-- Crystallizes the state of the module, i.e. it defines it as a Lean
`structure` definition, if that hasn't already happened. -/
def Module.ensureStateIsDefined (mod : Module) : CommandElabM Module := do
  if mod.isStateDefined then
    return mod
  -- Resolve concrete representation configurations
  let repConfigs ← resolveConcreteRepConfigs mod._concreteRepConfig
  let (mod, fieldStxs) ← mod.declareStateFieldLabelTypeAndDispatchers repConfigs
  let (mod, stateStxs) ← mod.declareFieldsAbstractedStateStructure repConfigs
  let stateStxs := fieldStxs ++ stateStxs
  let (mod, theoryStxs) ← mod.declareTheoryStructure
  let instantiationStxs ← mod.mkInstantiationStructure
  for stx in stateStxs ++ theoryStxs ++ instantiationStxs do
    elabVeilCommand stx
  generateIgnoreFn mod
  let mod := { mod with _stateDefined := true }
  if mod._useLocalRPropTC then
    let stxs ← liftTermElabM mod.declareLocalTheoryPropTC
    for stx in stxs do
      elabVeilCommand stx.raw
    let stxs ← liftTermElabM mod.declareLocalRPropTC
    for stx in stxs do
      elabVeilCommand stx.raw
    -- Generate the transition weakening theorem for this module
    try
      let cmd ← liftTermElabM mod.declareTransitionWeakeningLemma
      elabVeilCommand cmd
    catch ex =>
      logWarning m!"unable to generate transition weakening lemma: {ex.toMessageData}"
  pure mod

private def Module.ensureExecutableModelCheckerDefinitions (mod : Module) : CommandElabM Unit := do
  if (← getEnv).contains (mod.name ++ enumerableTransitionSystemName) then
    return
  let savedState ← get
  let stepOrAbort (act : CommandElabM Unit) : CommandElabM Unit := do
    act
    if (← get).messages.hasErrors then
      modify fun s => { savedState with messages := s.messages, traceState := s.traceState }
      throwAbortCommand
  stepOrAbort <| Extract.runGenExtractCommand mod
  stepOrAbort <| elabVeilCommand (← Extract.Module.assembleEnumerableTransitionSystem mod)

@[command_elab Veil.genExecutable]
def elabGenExecutable : CommandElab := fun _stx => do
  let mod ← getCurrentModule (errMsg := "You cannot #gen_executable outside of a Veil module!")
  mod.throwIfSpecNotFinalized
  mod.ensureExecutableModelCheckerDefinitions

@[command_elab Veil.genState]
def elabGenState : CommandElab := fun _stx => do
  -- Use dynamic trace class name for detailed profiling
  withTraceNode `veil.perf.elaborator.genState (fun _ => return "#gen_state") do
    let mut mod ← getCurrentModule (errMsg := "You cannot #gen_state outside of a Veil module!")
    mod.throwIfStateAlreadyDefined ; mod.throwIfSpecAlreadyFinalized
    mod ← mod.ensureStateIsDefined
    localEnv.modifyModule (fun _ => mod)

@[command_elab Veil.initializerDefinition]
def elabInitializer : CommandElab := fun stx => do
  -- Use dynamic trace class name for detailed profiling
  withTraceNode `veil.perf.elaborator.afterInit (fun _ => return "after_init") do
    let mut mod ← getCurrentModule (errMsg := "You cannot elaborate an initializer outside of a Veil module!")
    mod ← mod.ensureStateIsDefined
    mod.throwIfSpecAlreadyFinalized
    let new_mod ← match stx with
    | `(command|after_init {$l:doSeq}) => mod.defineProcedure (ProcedureInfo.initializer) .none .none l stx
    | _ => throwUnsupportedSyntax
    localEnv.modifyModule (fun _ => new_mod)

@[command_elab Veil.procedureDefinition]
def elabProcedure : CommandElab := fun stx => do
  let nm := extractDefinitionName stx
  -- Use dynamic trace class name that includes the action name
  withTraceNode (`veil.perf.elaborator.action ++ nm) (fun _ => return s!"action {nm}") do
    let mut mod ← getCurrentModule (errMsg := "You cannot elaborate an action outside of a Veil module!")
    mod ← mod.ensureStateIsDefined
    mod.throwIfSpecAlreadyFinalized
    let new_mod ← match stx with
    | `(command|action $nm:ident $br:explicitBinders ? {$l:doSeq}) => mod.defineProcedure (ProcedureInfo.action nm.getId) br .none l stx
    | `(command|procedure $nm:ident $br:explicitBinders ? {$l:doSeq}) => mod.defineProcedure (ProcedureInfo.procedure nm.getId) br .none l stx
    | _ => throwUnsupportedSyntax
    localEnv.modifyModule (fun _ => new_mod)

@[command_elab Veil.transitionDefinition]
def elabTransition : CommandElab := fun stx => do
  let nm := extractDefinitionName stx
  -- Use dynamic trace class name that includes the transition name
  withTraceNode (`veil.perf.elaborator.transition ++ nm) (fun _ => return s!"transition {nm}") do
    let mut mod ← getCurrentModule (errMsg := "You cannot elaborate a transition outside of a Veil module!")
    mod ← mod.ensureStateIsDefined
    mod.throwIfSpecAlreadyFinalized
    let new_mod ← match stx with
    | `(command|transition $nm:ident $br:explicitBinders ? { $t:term }) =>
      -- check immutability of changed fields
      let changedFn (f : Name) := t.raw.find? (·.getId == f.appendAfter "'") |>.isSome
      let fields ← mod.getFieldsRecursively
      for f in fields.filter changedFn do
        mod.throwIfImmutable f (isTransition := true)
      -- Only mutable fields need "unchanged" constraints
      -- (immutable fields don't have primed versions in transitions)
      let mutableFieldNames := mod.mutableComponents.map (·.name)
      let unchangedFields := mutableFieldNames.filter (!changedFn ·)
      -- obtain the "real" transition term
      let trStx ← do
        let (th, st, st') := (mkIdent `th, mkIdent `st, mkIdent `st')
        let unchangedFields := unchangedFields.map Lean.mkIdent
        let tmp ← liftTermElabM <| mod.withTheoryAndStateTermTemplate [(.theory, th, true), (.state .none "conc", st, true), (.state "'" "conc'", st', true)]
          (some $ ← `(term|Prop))
          (fun _ _ => `([unchanged|"'"| $unchangedFields*] ∧ ($t)))
        -- NOTE: We wrap the transition in a `decide` to ensure the required `Decidable` instance
        -- becomes an instance argument and can be used in extraction
        `(term| (fun ($th : $environmentTheory) ($st $st' : $environmentState) => $(mkIdent ``decide) ($tmp) = $(mkIdent ``true)))
      mod.defineTransition (ProcedureInfo.action nm.getId (definedViaTransition := true)) br trStx stx
      -- FIXME: Is this required?
      -- -- warn if this is not first-order
      -- Command.liftTermElabM $ warnIfNotFirstOrder nm.getId
    | _ => throwUnsupportedSyntax
    localEnv.modifyModule (fun _ => new_mod)

@[command_elab Veil.procedureDefinitionWithSpec]
def elabProcedureWithSpec : CommandElab := fun stx => do
  let nm := extractDefinitionName stx
  -- Use dynamic trace class name that includes the action name
  withTraceNode (`veil.perf.elaborator.actionWithSpec ++ nm) (fun _ => return s!"action+spec {nm}") do
    let mut mod ← getCurrentModule (errMsg := "You cannot elaborate an action outside of a Veil module!")
    mod ← mod.ensureStateIsDefined
    mod.throwIfSpecAlreadyFinalized
    let new_mod ← match stx with
    | `(command|action $nm:ident $br:explicitBinders ? $spec:doSeq {$l:doSeq}) => mod.defineProcedure (ProcedureInfo.action nm.getId) br spec l stx
    | `(command|procedure $nm:ident $br:explicitBinders ? $spec:doSeq {$l:doSeq}) => mod.defineProcedure (ProcedureInfo.procedure nm.getId) br spec l stx
    | _ => throwUnsupportedSyntax
    localEnv.modifyModule (fun _ => new_mod)

@[command_elab Veil.ghostRelationDefinition, command_elab Veil.ghostFunctionDefinition]
def elabGhostDefinition : CommandElab := fun stx => do
  let nm := extractDefinitionName stx
  -- Use dynamic trace class name that includes the ghost relation name
  withTraceNode (`veil.perf.elaborator.ghostDefinition ++ nm) (fun _ => return s!"ghost {nm}") do
    let mut mod ← getCurrentModule (errMsg := "You cannot elaborate a ghost definition outside of a Veil module!")
    mod ← mod.ensureStateIsDefined
    mod.throwIfSpecAlreadyFinalized
    let new_mod ← match stx with
    | `(command|$[theory%$forTheory]? ghost relation $nm:ident $br:explicitBinders ? := $t:term) =>
      mod.defineGhostDefinition nm.getId br t (justTheory := forTheory.isSome) (isRelation := true)
    | `(command|$[theory%$forTheory]? ghost function $nm:ident $br:explicitBinders ? $[: $retTy:term]? := $t:term) =>
      mod.defineGhostDefinition nm.getId br t (justTheory := forTheory.isSome) (isRelation := false) (retType := retTy)
    | _ => throwUnsupportedSyntax
    localEnv.modifyModule (fun _ => new_mod)

@[command_elab Veil.assertionDeclaration]
def elabAssertion : CommandElab := fun stx => do
  let mut mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
  mod ← mod.ensureStateIsDefined
  mod.throwIfSpecAlreadyFinalized
  -- TODO: handle assertion sets correctly
  let assertion : StateAssertion ← match stx with
  | `(command|assumption $name:propertyName ? $prop:term) => mod.mkAssertion .assumption name prop stx
  | `(command|invariant $name:propertyName ? $prop:term) => mod.mkAssertion .invariant name prop stx
  | `(command|safety $name:propertyName ? $prop:term) => mod.mkAssertion .safety name prop stx
  | `(command|trusted invariant $name:propertyName ? $prop:term) => mod.mkAssertion .trustedInvariant name prop stx
  | `(command|termination $name:propertyName ? $prop:term) => mod.mkAssertion .termination name prop stx
  | `(command|state_constraint $name:propertyName ? $prop:term) => mod.mkAssertion .stateConstraint name prop stx
  | _ => throwUnsupportedSyntax
  -- Use dynamic trace class name that includes the assertion name and kind
  let kindStr := match assertion.kind with
    | .assumption => "assumption"
    | .invariant => "invariant"
    | .safety => "safety"
    | .trustedInvariant => "trusted_invariant"
    | .termination => "termination"
    | .stateConstraint => "state_constraint"
  withTraceNode (`veil.perf.elaborator.assertion ++ assertion.name) (fun _ => return s!"{kindStr} {assertion.name}") do
    -- Elaborate the assertion in the Lean environment
    let mod' ← mod.defineAssertion assertion
  --   dbg_trace s!"Elaborated assertion: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic stx}"
    localEnv.modifyModule (fun _ => mod')

open Lean Meta Elab Command Veil in
/-- Developer tool. Import all module parameters into section scope. -/
elab "veil_variables" : command => do
  let mod ← getCurrentModule
  let binders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ← mod.parameters.mapM (·.binder)
  for binder in binders do
    match binder with
    | `(bracketedBinder| ($id:ident : $ty:term) )
    | `(bracketedBinder| [$id:ident : $ty:term] )
      =>
      let varId := id.getId
      trace[veil.debug] s!"{varId} :  {← liftTermElabM <| Lean.PrettyPrinter.formatTerm ty}"
    | _ => throwError "unsupported veil_variables binder syntax"
    let varUIds ← (← getBracketedBinderIds binder) |>.mapM (withFreshMacroScope ∘ MonadQuotation.addMacroScope)
    trace[veil.debug] s!"with unique IDs: {varUIds}"
    modifyScope fun scope => { scope with varDecls := scope.varDecls.push binder, varUIds := scope.varUIds ++ varUIds}

/-- Configuration options for the `#model_check` command. -/
structure ModelCheckerConfig where
  /-- Maximum depth (number of transitions) to explore. If it's 0, explores all
  reachable states. -/
  maxDepth : Nat := 0
  /-- If true, run the model checker sequentially (no parallelization). -/
  sequential : Bool := false
  /-- Parallel configuration. Only used if `sequential` is false. -/
  parallelCfg : Option ModelChecker.ParallelConfig := none
  deriving Repr

/-- Default threshold for parallelizing model checking subtasks. -/
def defaultThresholdToParallel : Nat := 20

declare_command_config_elab elabModelCheckerConfig ModelCheckerConfig

/-- Frontend configuration for `#model_check`, retaining the fingerprint type and the seen set's
shard type as syntax. -/
structure ModelCheckCommandConfig extends ModelCheckerConfig where
  /-- Elaborated with the generated checker call; defaults to `Nat` (`StateFingerprint.ofHashNat`). -/
  fingerprintType : Term := mkCIdent ``Nat
  /-- Applied to the fingerprint type, the set type of the shards of the parallel search's seen set;
  defaults to `TreeSetShard` (`Std.TreeSet`). -/
  seenSet : Term := mkCIdent ``TreeSetShard

declare_command_config_elab elabModelCheckCommandConfig ModelCheckCommandConfig where
  option fingerprintType := fun cfg item => do
    item.checkNotBool
    return { cfg with fingerprintType := ⟨item.value⟩ }
  option seenSet := fun cfg item => do
    item.checkNotBool
    return { cfg with seenSet := ⟨item.value⟩ }
  -- A full ordinary configuration leaves the separately specified fingerprint type and seen set
  -- unchanged.
  option config := fun cfg item => do
    item.checkNotBool
    let base : ModelCheckerConfig ← Lean.Elab.ConfigEval.evalExprWithElab ⟨item.value⟩
    return { cfg with toModelCheckerConfig := base }

declare_command_config_elab elabSimulateConfig ModelChecker.Simulation.SimulateConfig

/--
Check whether a particular config field was written explicitly in the command syntax.

`elabSimulateConfig` returns a complete `SimulateConfig`, so omitted fields are
indistinguishable from fields explicitly written with their structure defaults
after elaboration. Inspect the raw `Parser.Tactic.optConfig` only for this
distinction. A `(config := cfg)` item is an opaque full `SimulateConfig`, so it
is treated as explicitly providing all fields rather than being overlaid with
global options.
-/
def simulateConfigHasField (cfgStx : Syntax) (fieldName : Name) : Bool :=
  Lean.Elab.Tactic.mkConfigItemViews (Lean.Parser.Tactic.getConfigItems cfgStx) |>.any
    (fun item =>
      let optionName := item.option.getId.eraseMacroScopes
      optionName == fieldName || optionName == `config)

/-- Return which `#simulate` trace-bound fields were supplied by command syntax. -/
private def simulateTraceBoundFieldsExplicit (cfgStx : Syntax) : Bool × Bool :=
  (simulateConfigHasField cfgStx `numTraces, simulateConfigHasField cfgStx `maxSteps)

/-- Resolve `#simulate` trace-bound fields, preserving explicit default literals. -/
def resolveSimulateTraceBounds (cfg0 : ModelChecker.Simulation.SimulateConfig)
    (commandHasNumTraces commandHasMaxSteps : Bool) (optionNumTraces optionMaxSteps : Nat) : Nat × Nat :=
  let numTraces := if commandHasNumTraces then cfg0.numTraces else optionNumTraces
  let maxSteps := if commandHasMaxSteps then cfg0.maxSteps else optionMaxSteps
  (numTraces, maxSteps)

open ExecutionWorkflow

def mkVeilExecActionResultTerm [Monad m] [MonadQuotation m]
    [MonadExceptOf Exception m] [AddErrorMessageContext m]
    (mod : Module) (instTerm theoryTerm stateTerm actionTerm : Term) : m Term := do
  let inst := mkVeilImplementationDetailIdent `inst
  let th := mkVeilImplementationDetailIdent `th
  let st := mkVeilImplementationDetailIdent `st
  let act := mkVeilImplementationDetailIdent `act
  let exec := mkVeilImplementationDetailIdent `exec
  let instSortArgs ← (← mod.uninterpretedParamIdents).mapM fun paramIdent => `($inst.$(paramIdent))
  let theoryTy ← `(@$theoryIdent $instSortArgs*)
  let fieldConcrete ← `($fieldConcreteDispatcher $instSortArgs*)
  let stateTy ← `(@$stateIdent $fieldConcrete)
  let actionTy ← `($(mkIdent ``VeilM) _ $theoryTy $stateTy _)
  let execTy ← `($(mkIdent ``VeilMultiExecM) $(mkIdent ``Std.Format) $(mkIdent ``Int) $theoryTy $stateTy _)
  `(term|
    let $inst : $instantiationType := $instTerm
    let $th : $theoryTy := $theoryTerm
    let $st : $stateTy := $stateTerm
    let $act : $actionTy := $actionTerm
    let $exec : $execTy :=
      ($(mkIdent ``MultiExtractor.NonDetT.extractList) $(mkIdent ``Std.Format) _ _ $act
        (h := by veil_extract_list_tactic) : $execTy)
    $(mkIdent ``Veil.Extract.extractAllResults) $exec $th $st)

elab_rules : term
  | `(__veil_exec_action% $instTerm:term $theoryTerm:term $stateTerm:term $actionTerm:term) => do
    let mod ← getCurrentModule (errMsg := "You cannot use __veil_exec_action% outside of a Veil module!")
    elabTerm (← mkVeilExecActionResultTerm mod instTerm theoryTerm stateTerm actionTerm) none

elab_rules : command
  | `(#__veil_exec_action $instTerm:term $theoryTerm:term $stateTerm:term $actionTerm:term) => do
    let mod ← getCurrentModule (errMsg := "You cannot #__veil_exec_action outside of a Veil module!")
    let resultTerm ← mkVeilExecActionResultTerm mod instTerm theoryTerm stateTerm actionTerm
    elabVeilCommand <| ← `(command| #eval $resultTerm)

/-- Warn if the module contains transitions (which are slow to model check). -/
private def warnAboutTransitions (mod : Module) : CommandElabM Unit := do
  let transitions := mod.procedures.filter (·.info.isTransition)
  if transitions.isEmpty then return
  let names := ", ".intercalate (transitions.map (·.info.name.toString) |>.toList)
  logWarning m!"Explicit state model checking of transitions is SLOW!\n\n\
    The current implementation enumerates all possible states and filters those satisfying \
    the transition relation. Your specification has {transitions.size} \
    transition{if transitions.size > 1 then "s" else ""}: {names}\n\n\
    Consider encoding transitions as imperative actions where possible."

/-- Get the theory term, defaulting to `{}` if not provided and there are no theory fields.
      Throws a helpful error if theory fields exist but no term was provided. -/
private def getTheoryTerm (cmdName : String) (theoryTermOpt : Option Term)
    (mod : Module) (instTerm : Term) : CommandElabM Term := do
  match theoryTermOpt with
  | some t => pure t
  | none =>
    unless mod.immutableComponents.isEmpty do
      let fieldStrs := mod.immutableComponents.map (fun c => s!"{c.name} := ...")
      let theoryExample := "{ " ++ ", ".intercalate fieldStrs.toList ++ " }"
      throwError "This module has immutable fields, so you must specify the theory instantiation:\n\
        {cmdName} {instTerm} {theoryExample}"
    `({})

/-- Prepend `name` with `mod.name`. Useful when expressions are printed out for debugging. -/
private def mkIdentWithModName (mod : Module) (name : Name) : Ident :=
  Lean.mkIdent (mod.name ++ name)

/-- The module's `enumerableTransitionSystem`, logging picks or not (`LogSwitch`). Only recovering
a counterexample trace runs with the log; searches and simulations do not read it. -/
private def mkTransitionSystemTerm (mod : Module) (instSortArgs : Array Term) (th : Ident)
    (logPicks : Bool) : CommandElabM Term :=
  `(letI : $(mkIdent ``LogSwitch) := ⟨$(quote logPicks)⟩
    $(mkIdentWithModName mod `enumerableTransitionSystem) $instSortArgs* $th)

/-- Build search parameters for model checking / simulation. -/
private def mkSearchParameters (mod : Module) (config : ModelCheckerConfig) : CommandElabM Term := do
  let mkAssumption (sa : StateAssertion) : CommandElabM Term :=
    `($(mkIdent ``Veil.ModelChecker.TheoryProperty.mk)
        ($(mkIdent `name) := $(quote sa.name))
        ($(mkIdent `property) := fun $(mkIdent `th) => $(mkIdentWithModName mod sa.name) $(mkIdent `th)))
  -- Build SafetyProperty.mk syntax for a StateAssertion
  let mkProp (sa : StateAssertion) : CommandElabM Term :=
    `($(mkIdent ``Veil.ModelChecker.SafetyProperty.mk)
        ($(mkIdent `name) := $(quote sa.name))
        ($(mkIdent `property) := fun $(mkIdent `th) $(mkIdent `st) => $(mkIdentWithModName mod sa.name) $(mkIdent `th) $(mkIdent `st)))
  let assumptionList ← `([$((← mod.assumptions.mapM mkAssumption)),*])
  let safetyList ← `([$((← mod.invariants.mapM mkProp)),*])
  -- FIXME: Only recognizing the first termination property might confuse users
  let terminatingProp ← match mod.terminations[0]? with
    | some t => mkProp t
    | none => `($(mkIdent `default))
  let constraintList ← `([$((← mod.stateConstraints.mapM mkProp)),*])
  let earlyTermConds ← do
    let base ← `([$(mkIdent ``Veil.ModelChecker.EarlyTerminationCondition.foundViolatingState),
                  $(mkIdent ``Veil.ModelChecker.EarlyTerminationCondition.assertionFailed),
                  $(mkIdent ``Veil.ModelChecker.EarlyTerminationCondition.deadlockOccurred)])
    if config.maxDepth > 0 then `($base ++ [$(mkIdent ``Veil.ModelChecker.EarlyTerminationCondition.reachedDepthBound) $(quote config.maxDepth)])
    else pure base
  `({ $(mkIdent `assumptions):ident := $assumptionList, $(mkIdent `invariants):ident := $safetyList, $(mkIdent `terminating):ident := $terminatingProp,
        $(mkIdent `stateConstraints):ident := $constraintList,
        $(mkIdent `earlyTerminationConditions):ident := $earlyTermConds })

/-- Check that the provided theory satisfies all module assumptions by
    elaborating a proof obligation using the assembled `Assumptions` definition.
    Always unfolds `Assumptions` via `dsimp` first, then runs the user's tactic
    or defaults to `first | decide | native_decide`. -/
def checkTheorySatisfiesAssumptions (mod : Module) (instTerm theoryTerm : Term)
    (tac : Option (TSyntax `Lean.Parser.Tactic.tacticSeq)) : CommandElabM Unit := do
  let inst := mkVeilImplementationDetailIdent `inst
  let th := mkVeilImplementationDetailIdent `th
  let instSortArgs ← (← mod.uninterpretedParamIdents).mapM fun paramIdent => `($inst.$(paramIdent))
  -- Wrap the user tactic (a tacticSeq) as a single tactic via parentheses,
  -- or default to `first | decide | native_decide`.
  let userTac : TSyntax `tactic ← match tac with
    | some t => `(tactic| ($t:tacticSeq))
    | none => `(tactic| first | decide | native_decide)
  -- Call `Assumptions` using the same named-argument pattern as in
  -- `assembleRelationalTransitionSystem`: `Assumptions (ρ := TheoryType) sorts* th`
  let ρArg := mkIdent `ρ
  let theoryT ← `($theoryIdent $instSortArgs*)
  let proofCmd ← `(command|
    example : (let $inst : $instantiationType := $instTerm
               let $th : $theoryIdent $instSortArgs* := $theoryTerm
               $assembledAssumptions ($ρArg := $theoryT) $instSortArgs* $th) := by
      dsimp only [$assembledAssumptions:ident]
      $userTac:tactic)
  elabVeilCommand proofCmd

private structure ExecutionCallContext where
  instSortArgs : Array Term
  theoryArg : Ident
  searchParams : Term
  sysWithoutLog : Term

/-- Bind the concrete instantiation and theory around a command-specific call.
Simplify field reads in the `Decidable` instances synthesized by the call. -/
private def mkExecutionCall (mod : Module) (config : ModelCheckerConfig)
    (instTerm theoryTerm : Term)
    (mkCall : ExecutionCallContext → CommandElabM Term) : CommandElabM Term := do
  let inst := mkVeilImplementationDetailIdent `inst
  let th := mkVeilImplementationDetailIdent `th
  let instSortArgs ← (← mod.uninterpretedParamIdents).mapM fun paramIdent => `($inst.$(paramIdent))
  let sp ← mkSearchParameters mod config
  let sysWithoutLog ← mkTransitionSystemTerm mod instSortArgs th (logPicks := false)
  let call ← mkCall {
    instSortArgs := instSortArgs
    theoryArg := th
    searchParams := sp
    sysWithoutLog := sysWithoutLog
  }
  -- `veil_dsimp_field_reads%` simplifies the field reads in the `Decidable` instances synthesized here
  `(veil_dsimp_field_reads% (
      let $inst : $instantiationType := $instTerm
      let $th : $theoryIdent $instSortArgs* := $theoryTerm
      $call))

/-- Build the core model checker call syntax (without parallel config). -/
private def mkModelCheckerCall (mod : Module) (config : ModelCheckerConfig) (fingerprintType seenSet : Term)
    (instTerm theoryTerm : Term) : CommandElabM Term :=
  mkExecutionCall mod config instTerm theoryTerm fun ectx => do
  -- A counterexample's trace is recovered in a system that logs picks.
  let traceSys ← mkTransitionSystemTerm mod ectx.instSortArgs ectx.theoryArg (logPicks := true)
  -- Model checker call with type annotation to help inference
  -- Note: findReachableThen takes parallelCfg, progressInstanceId, cancelToken, and the
  -- continuation for the result as the last four args
  -- The fingerprint type comes from the `fingerprintType` option, the seen set's shard type from
  -- `seenSet`. The checker is generic in both and gets specialized to them at this call site.
  `(($(mkIdent ``Veil.ModelChecker.Concrete.findReachableThen)
       ($(mkIdent `inhabσ) := $instInhabitedStateFieldConcreteType)
       ($(mkIdent `σₕ) := $fingerprintType)
       ($(mkIdent `Shard) := $seenSet $fingerprintType)
       ($(ectx.sysWithoutLog)) (fun _ => $traceSys)
       $(ectx.searchParams) : _ → _ → _ → _ → IO _))

/-- Build the simulator call for the shared execution workflow, including display JSON conversion. -/
private def mkSimulateCall (mod : Module) (instTerm theoryTerm : Term)
    (cfg : ModelChecker.Simulation.SimulateConfig) : CommandElabM Term := do
  let cfgTerm ← `($(mkIdent ``Veil.ModelChecker.Simulation.SimulateConfig.mk)
      $(quote cfg.numTraces) $(quote cfg.maxSteps) $(quote cfg.seed))
  let runtimeCallExpr ← mkExecutionCall mod {} instTerm theoryTerm fun ectx =>
    `(($(mkIdent ``Veil.ModelChecker.Simulation.simulateWithProgress)
        $(ectx.sysWithoutLog) $(ectx.searchParams) $(ectx.theoryArg) $cfgTerm : _ → _ → IO _))
  let resultIdent := mkVeilImplementationDetailIdent `simulateRuntimeResult
  `(fun (_ : Option Veil.ModelChecker.ParallelConfig)
      (progressInstanceId : Nat) (cancelToken : IO.CancelToken) (finish : Lean.Json → IO _) => do
    let $resultIdent ← ($runtimeCallExpr progressInstanceId cancelToken)
    finish ($(mkIdent ``Veil.ModelChecker.Simulation.SimulateResult.toDisplayJson) $resultIdent))

private structure ExecutionCallCommandContext (Config : Type) where
  mod : Module
  config : Config
  instantiation : Term
  «theory» : Term

/-- Shared elaboration for execution commands with command-specific configuration and calls. -/
private def elabExecutionCommand {α : Type} (cmdName : String) (traceClass : Name)
    (kind : TraceDisplay.ResultKind) (elabConfig : Syntax → CommandElabM α)
    (assumptionsHoldByIndex : Nat)
    (mkCall : ExecutionCallCommandContext α → CommandElabM (Term × Option ModelChecker.ParallelConfig))
    : CommandElab := fun stx => do
  -- Use dynamic trace class name for detailed profiling
  withTraceNode traceClass (fun _ => return s!"#{cmdName}") do
    -- All commands through this interface use the same syntax layout for the first three arguments:
    -- stx[1] is the optional mode, stx[2] is instTerm, stx[3] is optional theory
    let mode := getModelCheckingMode stx[1]
    let instTerm : Term := ⟨stx[2]⟩
    let theoryTermOpt : Option Term := if stx[3].isNone then none else some ⟨stx[3][0]⟩
    let assumptionsHoldBy : Option (TSyntax `Lean.Parser.Tactic.tacticSeq) :=
      if stx[assumptionsHoldByIndex].isNone then none else some ⟨stx[assumptionsHoldByIndex][0][1]⟩
    let mod ← getCurrentModule (errMsg := s!"You cannot #{cmdName} outside of a Veil module!")
    mod.throwIfSpecNotFinalized
    let theoryTerm ← getTheoryTerm s!"#{cmdName}" theoryTermOpt mod instTerm
    warnAboutTransitions mod
    -- Let `elabConfig` choose which part should be the configuration.
    let cfg ← elabConfig stx
    -- Optionally prove assumptions statically; both algorithms also evaluate them at runtime.
    if assumptionsHoldBy.isSome && !mod.assumptions.isEmpty then
      checkTheorySatisfiesAssumptions mod instTerm theoryTerm assumptionsHoldBy
    mod.ensureExecutableModelCheckerDefinitions
    let (callExpr, parallelCfg) ← mkCall {
      mod := mod
      config := cfg
      instantiation := instTerm
      «theory» := theoryTerm
    }
    ExecutionWorkflow.run { name := cmdName } kind mod stx mode callExpr parallelCfg

@[command_elab Veil.modelCheck]
def elabModelCheck : CommandElab :=
  elabExecutionCommand "model_check" `veil.perf.elaborator.modelCheck .modelCheck
    (fun stx => elabModelCheckCommandConfig stx[4]) 5 fun ecctx => do
    let commandCfg := ecctx.config
    let config := commandCfg.toModelCheckerConfig
    -- Resolve parallelCfg: sequential flag takes precedence, otherwise default to parallel
    let parallelCfg ← match config.sequential, config.parallelCfg with
      | true, _ => pure none
      | false, some cfg => pure (some cfg)
      | false, none => pure (some { numSubTasks := ← getNumCores, thresholdToParallel := defaultThresholdToParallel })
    let callExpr ← mkModelCheckerCall ecctx.mod config commandCfg.fingerprintType commandCfg.seenSet ecctx.instantiation ecctx.theory
    return (callExpr, parallelCfg)

/-- Resolve simulation bounds from command syntax and options, and choose a seed. -/
private def elabSimulateCommandConfig (cfgStx : Syntax)
    : CommandElabM ModelChecker.Simulation.SimulateConfig := do
  let cfg0 ← elabSimulateConfig cfgStx
  let opts ← getOptions
  let (hasNumTraces, hasMaxSteps) := simulateTraceBoundFieldsExplicit cfgStx
  let optionNumTraces := veil.simulate.numTraces.get opts
  let optionMaxSteps := veil.simulate.maxSteps.get opts
  let (numTraces, maxSteps) := resolveSimulateTraceBounds cfg0 hasNumTraces hasMaxSteps
    optionNumTraces optionMaxSteps
  let seed ← liftIO <| if cfg0.seed == 0 then IO.rand 0 0xFFFFFFFFFFFFFFFF else pure cfg0.seed
  return { cfg0 with numTraces, maxSteps, seed }

@[command_elab Veil.simulate]
def elabSimulate : CommandElab :=
  elabExecutionCommand "simulate" `veil.perf.elaborator.simulate .simulate
    (fun stx => elabSimulateCommandConfig stx[4]) 5 fun ecctx => do
    return (← mkSimulateCall ecctx.mod ecctx.instantiation ecctx.theory ecctx.config, none)

end Veil
