module

public meta import Veil.Frontend.DSL.Module.Util.Basic
public meta import Veil.Frontend.DSL.Action.Syntax
public meta import Veil.Frontend.DSL.Action.DoElab.Context
public meta import Veil.Frontend.DSL.Action.Elaborators
public meta import Veil.Frontend.DSL.Module.Util.TemplateHygiene
public meta import Veil.Frontend.DSL.Module.Util.InvSet
public meta import Veil.Frontend.DSL.Module.Util.SourceInstances

public meta section

open Lean Parser

namespace Veil

/-- A concrete occurrence of a reusable module, together with the instances
whose implementations and proved facts are present in its proof context. -/
scoped syntax (name := isolateDeclaration) "isolate " ident " : " ident
  Term.namedArgument* (" with " ident,*)? : command

open Elab Command Term

/-- Unlike the scoped current module, templates survive `end` and imports. -/
initialize moduleTemplateExt : SimplePersistentEnvExtension Module (Std.HashMap Name Module) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s mod => s.insert mod.name mod
    addImportedFn := fun arrays => arrays.foldl (init := {}) fun s mods =>
      mods.foldl (init := s) fun s mod => s.insert mod.name mod
  }

def saveModuleTemplate (mod : Module) : CommandElabM Unit :=
  modifyEnv (moduleTemplateExt.addEntry · mod)

def getModuleTemplate? (name : Name) : CommandElabM (Option Module) := do
  let templates := moduleTemplateExt.getState (← getEnv)
  return templates[name]?

/-- User-written module names follow Lean namespace resolution, including
parent namespaces and opens. Internal references already store a canonical
name and use `getModuleTemplate?` directly instead. -/
private def resolveModuleTemplate? (id : Syntax) : CommandElabM (Option Module) := do
  let .ident _ _ name preResolved := id | return none
  let templates := moduleTemplateExt.getState (← getEnv)
  let pinned := preResolved.filterMap fun
    | .namespace name => some name
    | _ => none
  let namespaces ← if pinned.isEmpty then resolveNamespaceCore name (allowEmpty := true)
    else pure pinned
  let candidates := namespaces.filter templates.contains |>.eraseDups
  match candidates with
  | [] => return none
  | [candidate] => return templates[candidate]?
  | _ => throwError "ambiguous Veil module {name}; use a qualified name ({candidates})"

private def nameTemplateAssertion (mod : Module) (stx : Syntax) : CommandElabM Syntax := do
  unless stx.isOfKind ``assertionDeclaration && stx[1].isNone do return stx
  let ordinal := (mod.templateCommands.filter fun command =>
    command.isOfKind ``assertionDeclaration && command[0].getKind == stx[0].getKind).size
  let stem := match stx with
    | `(command| invariant $_:term) => "inv"
    | `(command| safety $_:term) => "safety"
    | `(command| assumption $_:term) => "assumption"
    | `(command| trusted invariant $_:term) => "trusted_inv"
    | `(command| termination $_:term) => "termination"
    | _ => "state_constraint"
  let label ← `(propertyName| [$(mkIdent (.mkSimple s!"{stem}_{ordinal}"))])
  return stx.setArg 1 (mkNullNode #[label.raw])

private def sourceFieldIsInstance (mod : Module) (stx : Syntax) : CommandElabM Bool := do
  unless stx.isOfKind ``stateComponentDeclaration do return false
  try
    let ty ← match stx with
      | `(command| $_:stateMutability ? $_:stateComponentKind $_name:ident $br:bracketedBinder* : $tp:term) =>
        if br.isEmpty then pure tp else
          (StateComponentType.complex br tp).stx
      | _ => return false
    liftTermElabMWithBinders (← mod.uninterpretedParamBinders) fun _ => do
      return (← Meta.isClass? (← Term.withoutErrToSorry <| elabType ty)).isSome
  catch ex =>
    if ex.isInterrupt then throw ex
    return false

/-- Record source before elaboration. References are deferred until an isolate
supplies an occurrence, rather than elaborating a namespace as a Lean type. -/
def recordModuleCommand (mod : Module) (stx : Syntax) : CommandElabM Module := do
  mod.throwIfSpecAlreadyFinalized
  if mod.replayingInstance then return mod
  let stored ← nameTemplateAssertion mod stx
  let scope : TemplateCommandScope := {
    namespaceName := ← getCurrNamespace, openDecls := ← getOpenDecls, options := ← getOptions
    instances := Lean.Meta.instanceExtension.getState (← getEnv)
    defaultInstances := Lean.Meta.defaultInstanceExtension.getState (← getEnv)
    instanceParameters := mod.parameters.filterMap fun p =>
      if p.kind == .moduleTypeclass .userDefined || p.classValued then some p.name else none }
  let mut names := mod.parameters.map (·.name) ++ mod._declarations.toArray.map (·.1) ++
    mod.instanceNames.map (·.1)
  for command in mod.templateCommands do
    let priorName :=
      if command.isOfKind ``stateComponentDeclaration then command[2].getId
      else if command.isOfKind ``assertionDeclaration then command[1][0][1].getId
      else command[1].getId
    if !priorName.isAnonymous then names := names.push priorName
  let header :=
    if stored.isOfKind ``stateComponentDeclaration then stored[2].getId
    else if stored.isOfKind ``assertionDeclaration then stored[1][0][1].getId
    else stored[1].getId
  if !header.isAnonymous then names := names.push header
  for (name, _) in moduleTemplateExt.getState (← getEnv) do names := names.push name
  for ref in mod.moduleReferences do
    names := names.push ref.name
    if let some dependency ← getModuleTemplate? ref.moduleName then
      for command in dependency.templateCommands do
        if command.isOfKind ``stateComponentDeclaration then
          names := names.push (ref.name ++ command[2].getId)
  let identities := names.map fun name => (name, (mkIdent name : Term))
  let isInstanceField ← sourceFieldIsInstance mod stored
  let (captured, captureError) ← try
    if (Action.findOutsideQuotations? stored fun node =>
        if node.isQuot then some node else none).isSome then
      throwErrorAt stx "runtime syntax quotations are not supported in instantiated module templates"
    let captured ← specializeTemplateSyntax stored identities fun name => do
      let candidates := (← resolveGlobalName name).filterMap fun (candidate, fields) =>
        if fields.isEmpty then some candidate else none
      match candidates with
      | [candidate] => return some candidate
      | [] => return none
      | _ => throwErrorAt stx "ambiguous identifier {name} in the module's definition scope; use a qualified name"
    pure (captured, none)
  catch ex =>
    if ex.isInterrupt then throw ex
    pure (stored, some (← ex.toMessageData.toString))
  let mod := { mod with
    templateCommands := mod.templateCommands.push captured
    templateCommandScopes := mod.templateCommandScopes.push scope
    templateCaptureErrors := mod.templateCaptureErrors.push captureError
    templateInstanceFields := if isInstanceField then mod.templateInstanceFields.push stored[2].getId
      else mod.templateInstanceFields }
  localEnv.modifyModule (fun _ => mod)
  return mod

def Module.isReferenceTemplate (mod : Module) : Bool :=
  !mod.moduleReferences.isEmpty && !mod.replayingInstance

def Module.finishTemplateSpec (mod : Module) (stx : Syntax) : CommandElabM Bool := do
  unless mod.isReferenceTemplate do return false
  let mod := { mod with _specFinalizedAt := some stx }
  localEnv.modifyModule (fun _ => mod)
  saveModuleTemplate mod
  return true


private def instanceIdentifier (occurrence field : Name) (kind : String := "field") : Name :=
  .mkSimple s!"inst_{occurrence.toString.length}_{occurrence}__{kind}__{field}"

/-- Elaborate arguments at the instantiation site and retain canonical syntax
with explicit constants, types, and instances. A checked round trip pins the
caller's meaning without introducing extra state-type parameters. Template
binders are alpha-renamed before inserting these arguments. -/
private def pinArgument (mod : Module) (_occurrence : Name) (formal : Parameter) (actual expected : Term) :
    CommandElabM Term := do
  let rootParams := mod.parameters.filter fun p => match p.kind with
    | .sort _ | .userParameter | .moduleTypeclass .sortAssumption |
      .moduleTypeclass .userDefined => true
    | _ => false
  let binders ← rootParams.mapM (·.binder)
  let pinned ← liftTermElabMWithBinders binders fun variables => do
    let tp ← Term.withoutErrToSorry <| elabType expected
    let expr ← Term.withoutErrToSorry <| elabTermEnsuringType actual tp
    Term.synthesizeSyntheticMVarsNoPostponing
    let expr ← instantiateMVars expr
    if expr.hasMVar then
      throwErrorAt actual "module arguments must be closed over immutable module parameters"
    if (← Meta.whnf tp).isSort then
      if (← Meta.isClass? expr).isSome then
        throwErrorAt actual "module sorts must be data types, not typeclasses; declare class evidence with param or instantiate"
    else if !formal.classValued && (← Meta.isClass? (← Meta.inferType expr)).isSome then
      throwErrorAt actual "specialization would turn value parameter {formal.name} into an implicit instance; declare its class type explicitly"
    let stableFamily ← Meta.forallTelescopeReducing tp fun args resultType => do
      if args.isEmpty || !resultType.isSort then return true
      let result ← Meta.withTransparency .all <| Meta.whnf (mkAppN expr args)
      if (← Meta.isClass? result).isSome then return false
      match result.getAppFn with
      | .fvar id => return !args.any (·.fvarId! == id)
      | .sort _ => return true
      | .const name _ =>
        return match (← getEnv).find? name with
          | some (.inductInfo _) | some (.opaqueInfo _) | some (.axiomInfo _) => true
          | _ => false
      | _ => return false
    unless stableFamily do
      throwErrorAt actual "module type families must have a fixed non-class result type; declare class evidence explicitly"
    let free := (collectFVars {} expr).fvarIds
    for id in free do
      unless variables.any (·.fvarId! == id) do
        throwErrorAt actual "module arguments must be closed over immutable module parameters"
    for p in rootParams, argExpr in variables do
      if p.kind matches .moduleTypeclass _ then
        if free.contains argExpr.fvarId! then
          throwErrorAt actual "a module argument depends on typeclass parameter {p.name}; expose that value as an ordinary param so state types retain its binding"
    let pinned ← withOptions (fun options => options
        |>.setBool `pp.fullNames true |>.setBool `pp.notation false
        |>.setBool `pp.fieldNotation false) <| delabVeilExpr expr true
    let roundtrip ← Term.withoutErrToSorry <| elabTermEnsuringType pinned tp
    unless ← Meta.isDefEq expr roundtrip do
      throwErrorAt actual "could not preserve this module argument during specialization"
    return pinned
  let rootBindings := rootParams.map fun p => (p.name, (mkIdent p.name : Term))
  let pinned : Term := ⟨← specializeTemplateSyntax pinned rootBindings fun name => do
    return if (← getEnv).contains name then some name else none⟩
  -- Check again after lexical normalization and global-name pinning, in the
  -- same root scope in which the specialized declarations will be inserted.
  liftTermElabMWithBinders binders fun _ => do
    let tp ← Term.withoutErrToSorry <| elabType expected
    let original ← Term.withoutErrToSorry <| elabTermEnsuringType actual tp
    let replayed ← Term.withoutErrToSorry <| elabTermEnsuringType pinned tp
    Term.synthesizeSyntheticMVarsNoPostponing
    unless ← Meta.isDefEq original replayed do
      throwErrorAt actual "module argument changed meaning at its insertion site"
  return pinned

def Module.tryDeclareModuleReference (mod : Module) (id : Ident) (tp : Term)
    (stx : Syntax) : CommandElabM (Option Module) := do
  let (head, args) := match tp.isApp? with
    | some (head, args) => (head, args)
    | none => (⟨tp.raw⟩, #[])
  let some target ← resolveModuleTemplate? head.raw | return none
  mod.throwIfStateAlreadyDefined
  mod.throwIfAlreadyDeclared id.getId
  let targetParams := target.parameters.filter fun p =>
    match p.kind with | .sort _ | .userParameter => true | _ => false
  unless args.size ≤ targetParams.size do
    throwErrorAt tp "too many type/value arguments for module reference {head}"
  let mut schema : Array (Name × Term) := #[]
  let mut pinnedArgs : Array Term := #[]
  for argument in args, formal in targetParams do
    let expected : Term := ⟨← specializeTemplateSyntax formal.type schema⟩
    let pinned ← pinArgument mod id.getId formal argument expected
    schema := schema.push (formal.name, pinned)
    pinnedArgs := pinnedArgs.push pinned
  let ref : ModuleReference := {
    name := id.getId, moduleName := target.name, arguments := pinnedArgs, userSyntax := stx }
  return some { mod with
    moduleReferences := mod.moduleReferences.push ref
    _declarations := mod._declarations.insert id.getId .moduleParameter }


private def fieldNames (mod : Module) : Array Name :=
  mod.templateCommands.filterMap fun stx =>
    if stx.isOfKind ``stateComponentDeclaration then some stx[2].getId else none

private def declarationNames (mod : Module) : Array Name :=
  mod.templateCommands.filterMap fun stx =>
    if stx.isOfKind ``stateComponentDeclaration then some stx[2].getId
    else if stx.isOfKind ``instanceDeclaration ||
        stx.isOfKind ``procedureDefinition || stx.isOfKind ``procedureDefinitionWithSpec ||
        stx.isOfKind ``transitionDefinition then some stx[1].getId
    else if stx.isOfKind ``assertionDeclaration then
      let names := stx[1].getArgs
      if names.isEmpty then none else some names[0]![1].getId
    else none

/-- Keep invariant names apart from action names joined with VC suffixes.
For example, relay's VC for backed must not collide with relay_backed. -/
private def specializedIdentifier (mod : Module) (occurrence name : Name) : Name :=
  let isAssertion := mod.templateCommands.any fun stx =>
    stx.isOfKind ``assertionDeclaration && stx[1][0][1].getId == name
  let isProcedure := mod.templateCommands.any fun stx =>
    (stx.isOfKind ``procedureDefinition || stx.isOfKind ``procedureDefinitionWithSpec ||
      stx.isOfKind ``transitionDefinition) && stx[1].getId == name
  if isAssertion then instanceIdentifier occurrence name "invariant"
  else if isProcedure then instanceIdentifier occurrence name "procedure"
  else if mod.templateCommands.any (fun stx => stx.isOfKind ``instanceDeclaration && stx[1].getId == name) then
    instanceIdentifier occurrence name "instance"
  else instanceIdentifier occurrence name

private partial def rejectForeignWrites (stx : Syntax) (foreignFields : Array Name) :
    CommandElabM Unit := do
  if Action.childrenAreQuoted stx false then return
  let lhs? : Option Term := match stx with
    | `(doReassign| $lhs:term $[: $_]? := $_) => some lhs
    | `(doReassignArrow| $lhs:term $[: $_]? ← $_ $[| $_ $[$_]?]?) => some lhs
    | `(doElem| $lhs:term := *) => some lhs
    | _ => none
  if let some lhs := lhs? then
    let head := match lhs.isApp? with | some (head, _) => head.raw | none => lhs.raw
    if foreignFields.contains head.getId then
      throwErrorAt lhs "module reference fields are read-only; an instance can write only its own state"
  for arg in stx.getArgs do rejectForeignWrites arg foreignFields

def Module.resolveInstanceNames (mod : Module) (stx : Syntax) : CommandElabM Syntax := do
  if mod.instanceNames.isEmpty || mod.replayingInstance then return stx
  specializeTemplateSyntax stx (mod.instanceNames.map fun (original, replacement) => (original, mkIdent replacement))

private def specializeInDefinitionScope (stx : Syntax) (bindings : Array (Name × Term))
    (scope : TemplateCommandScope) (parameters : Array Name) : CommandElabM Syntax := do
  let previous ← getScope
  modifyScope fun s => { s with
    currNamespace := scope.namespaceName
    openDecls := scope.openDecls
    opts := scope.options }
  let resolve : TemplateGlobalResolver := fun name => do
    if parameters.contains name || isCapital name || name.toString.startsWith "__veil" ||
        stateName.isPrefixOf name || theoryName.isPrefixOf name ||
        fieldAbstractDispatcherName.isPrefixOf name ||
        #[`χ, `χ_rep, `χ_rep_lawful, `ρ, `σ, `σ_sub, `ρ_sub].contains name then
      return none
    throwErrorAt stx "unknown identifier {name} in the module's definition scope"

  try
    specializeTemplateSyntax stx bindings resolve
  finally
    modifyScope fun s => { s with
      currNamespace := previous.currNamespace
      openDecls := previous.openDecls
      opts := previous.opts }

@[command_elab isolateDeclaration]
def elabIsolateDeclaration : CommandElab := fun stx => do
  let mod ← getCurrentModule
  mod.throwIfStateAlreadyDefined
  mod.throwIfSpecAlreadyFinalized
  let `(command| isolate $id:ident : $target:ident $args:namedArgument* $[with $deps:ident,*]?) := stx
    | throwUnsupportedSyntax
  unless id.getId.isAtomic do
    throwErrorAt id "isolate names must be atomic; nested instance names are not supported"
  if mod.instances.any (·.name == id.getId) then
    throwErrorAt id "duplicate isolate name {id}"
  mod.throwIfAlreadyDeclared id.getId
  let some template ← resolveModuleTemplate? target.raw
    | throwErrorAt target "unknown or unfinished Veil module {target}; finish its definition with #gen_spec"
  if let some error := template.templateCaptureErrors.findSome? (fun entry => entry) then
    throwErrorAt target "this module uses unsupported template syntax: {error}"
  unless template.instances.isEmpty do
    throwErrorAt target "instantiating a composed module is not supported yet; instantiate its component modules explicitly"
  let formalNames := (template.parameters.filterMap fun p =>
    match p.kind with | .sort _ | .userParameter => some p.name | _ => none) ++
    template.moduleReferences.map (·.name)
  let mut bindings := #[]
  for arg in args do
    let `(namedArgument| ($name:ident := $value:term)) := arg | throwUnsupportedSyntax
    unless formalNames.contains name.getId do
      throwErrorAt name "unknown parameter {name} of module {target}"
    if bindings.any (·.1 == name.getId) then
      throwErrorAt name "duplicate binding for parameter {name}"
    bindings := bindings.push (name.getId, value)
  for name in formalNames do
    unless bindings.any (·.1 == name) do
      throwErrorAt stx "missing binding for module parameter {name}"
  for formal in template.parameters do
    match formal.kind with
    | .sort _ | .userParameter =>
      let actual := (bindings.find? (·.1 == formal.name)).get!.2
      let expected : Term := ⟨← specializeTemplateSyntax formal.type bindings⟩
      let pinned ← pinArgument mod id.getId formal actual expected
      bindings := bindings.map fun (name, value) =>
        (name, if name == formal.name then pinned else value)
    | _ => pure ()
  let support := (deps.map (·.getElems) |>.getD #[]).map (·.getId)
  for dep in support do
    unless mod.instances.any (·.name == dep) do
      throwErrorAt stx "unknown isolate dependency {dep}; dependencies must precede their users"
  for ref in template.moduleReferences do
    let actual := (bindings.find? (·.1 == ref.name)).get!.2
    unless actual.raw.isIdent do
      throwErrorAt actual "module reference {ref.name} must name an existing isolate"
    let some occurrence := mod.instances.find? (·.name == actual.raw.getId)
      | throwErrorAt actual "unknown module instance {actual}"
    unless occurrence.moduleName == ref.moduleName do
      throwErrorAt actual "module reference {ref.name} expects {ref.moduleName}, got {occurrence.moduleName}"
    unless support.contains occurrence.name do
      throwErrorAt stx "module reference {ref.name} requires existing isolate {occurrence.name} in the `with` list"
    let some referenced ← getModuleTemplate? ref.moduleName | unreachable!
    let expectedParams := referenced.parameters.filter fun p =>
      match p.kind with | .sort _ | .userParameter => true | _ => false
    for arg in ref.arguments, formal in expectedParams do
      let expected : Term := ⟨← specializeTemplateSyntax arg bindings⟩
      let actualArg := (occurrence.bindings.find? (·.1 == formal.name)).get!.2
      let same ← liftTermElabMWithBinders (← mod.uninterpretedParamBinders) fun _ => do
        let a ← elabTerm expected none
        let b ← elabTerm actualArg none
        Meta.isDefEq a b
      unless same do
        throwErrorAt actual "incompatible binding for {formal.name} in module reference {ref.name}"
  let occurrence : ModuleInstance := {
    name := id.getId, moduleName := template.name, bindings, support, userSyntax := stx }
  let names := declarationNames template |>.map fun name =>
    (id.getId ++ name, specializedIdentifier template id.getId name)
  let primed := fieldNames template |>.map fun name =>
    (id.getId ++ name.appendAfter "'", (instanceIdentifier id.getId name).appendAfter "'")
  localEnv.modifyModule fun _ => { mod with
    instances := mod.instances.push occurrence
    instanceNames := mod.instanceNames ++ names ++ primed
    _declarations := mod._declarations.insert id.getId .moduleParameter }

private structure SourceReplay where
  command : Syntax
  scope : TemplateCommandScope
  classes : Array Name
  arguments : Array Term
  instanceFields : Array Name

private def replayCommand (command : Syntax)
    (source? : Option SourceReplay := none) : CommandElabM Unit := do
  let previous ← getCurrentModule
  localEnv.modifyModule fun _ => { previous with
    sourceCommandScope? := source?.map (·.scope)
    sourceInstanceNames? := source?.map (·.classes)
    sourceInstanceArguments := source?.map (·.arguments) |>.getD #[]
    sourceInstanceFieldNames? := source?.map (·.instanceFields) }
  let errorsBefore := (← get).messages.toList.countP (·.severity == .error)
  try
    withScope (fun scope => { scope with opts := scope.opts.setBool `Elab.async false }) <|
      elabCommand command
    if (← get).messages.toList.countP (·.severity == .error) > errorsBefore then
      throwAbortCommand
  finally
    let current ← getCurrentModule
    localEnv.modifyModule fun _ => { current with
      sourceCommandScope? := previous.sourceCommandScope?
      sourceInstanceNames? := previous.sourceInstanceNames?
      sourceInstanceArguments := previous.sourceInstanceArguments
      sourceInstanceFieldNames? := previous.sourceInstanceFieldNames? }

/-- Calls retain every root class argument explicitly, even while caller-only
instances are absent from source instance search. Declaration labels are not
applications. Unique occurrence identifiers make this pass independent of
user-local names, which were already alpha-renamed. -/
private partial def pinCallableInstances (mod : Module) (callables : Array Name)
    (stx : Syntax) : CommandElabM Syntax := do
  if Action.childrenAreQuoted stx false then return stx
  if stx.isIdent then
    if callables.contains stx.getId then
      return (← mod.explicitClassCall stx.getId #[]).raw
    return stx
  if stx.isOfKind ``propertyName || stx.isOfKind ``instanceDeclaration then return stx
  let args ← stx.getArgs.mapIdxM fun i child => do
    if ((stx.isOfKind ``procedureDefinition || stx.isOfKind ``procedureDefinitionWithSpec ||
        stx.isOfKind ``transitionDefinition) && i == 1) then return child
    pinCallableInstances mod callables child
  return stx.setArgs args

/-- Instantiate all declarations before freezing the root state. Every
occurrence action remains in the concrete root transition system. -/
private def Module.materializeIsolatesCore (mod : Module) : CommandElabM Module := do
  if mod.instances.isEmpty || mod.instancesMaterialized then return mod
  localEnv.modifyModule fun _ => { mod with instancesMaterialized := true, replayingInstance := true }
  let mut requirements : Array SourceReplay := #[]
  let mut fields : Array SourceReplay := #[]
  let mut declarations : Array SourceReplay := #[]
  let mut initializers : Array (Name × SourceReplay) := #[]
  let mut invSets : Array InvSet := #[]
  let mut callables : Array Name := #[]
  for occurrence in mod.instances do
    let some template ← getModuleTemplate? occurrence.moduleName | unreachable!
    unless template.templateCommands.any (·.isOfKind ``initializerDefinition) do
      throwErrorAt occurrence.userSyntax
        "module instance {occurrence.name} has no after_init block; every instance must initialize its state"
    let classes := template.parameters.filterMap fun p =>
      if p.kind == .moduleTypeclass .userDefined then
        some (specializedIdentifier template occurrence.name p.name)
      else none
    let mut bindings := occurrence.bindings.filter fun (name, _) =>
      !template.moduleReferences.any (·.name == name)
    bindings := bindings ++ (declarationNames template |>.map fun name =>
      (name, (mkIdent (specializedIdentifier template occurrence.name name) : Term)))
    bindings := bindings ++ (fieldNames template |>.map fun name =>
      (name.appendAfter "'", (mkIdent ((instanceIdentifier occurrence.name name).appendAfter "'") : Term)))
    let mut foreignFields : Array Name := #[]
    for ref in template.moduleReferences do
      let actual := (occurrence.bindings.find? (·.1 == ref.name)).get!.2.raw.getId
      let some referenced ← getModuleTemplate? ref.moduleName | unreachable!
      for field in fieldNames referenced do
        let concrete := instanceIdentifier actual field
        bindings := bindings.push (ref.name ++ field, mkIdent concrete)
        bindings := bindings.push (ref.name ++ field.appendAfter "'", mkIdent (concrete.appendAfter "'"))
        foreignFields := foreignFields.push concrete
    for command in template.templateCommands, scope in template.templateCommandScopes do
      if command.isOfKind ``typeDeclaration || command.isOfKind ``parameterDeclaration then continue
      let specialized ← specializeInDefinitionScope command bindings scope (template.parameters.map (·.name))
      rejectForeignWrites specialized foreignFields
      let arguments := scope.instanceParameters.filterMap fun name =>
        match template.parameters.find? (·.name == name) with
        | some parameter =>
          if parameter.kind == .userParameter then
            (occurrence.bindings.find? (·.1 == name)).map (·.2)
          else if specialized.isOfKind ``stateComponentDeclaration then none
          else some (mkIdent (specializedIdentifier template occurrence.name name) : Term)
        | none => none
      let instanceFields := template.templateInstanceFields.map (instanceIdentifier occurrence.name ·)
      let replay : SourceReplay := { command := specialized, scope, classes, arguments, instanceFields }
      if specialized.isOfKind ``instanceDeclaration then
        requirements := requirements.push replay
      else if specialized.isOfKind ``stateComponentDeclaration then
        fields := fields.push replay
      else if specialized.isOfKind ``initializerDefinition then
        let `(command| after_init { $body:doSeq }) := specialized | throwUnsupportedSyntax
        if (Action.findOutsideQuotations? body.raw fun node =>
            if node.isOfKind ``Lean.Parser.Term.doReturn then some node else none).isSome then
          throwErrorAt command "returns in component initializers are not supported; every component initializer must run to completion"
        initializers := initializers.push (occurrence.name, replay)
      else if specialized.isOfKind ``assertionDeclaration || specialized.isOfKind ``procedureDefinition ||
          specialized.isOfKind ``procedureDefinitionWithSpec || specialized.isOfKind ``transitionDefinition then
        declarations := declarations.push replay
        let name := if specialized.isOfKind ``assertionDeclaration then specialized[1][0][1].getId
          else specialized[1].getId
        callables := callables.push name
      else
        throwErrorAt command "this declaration is not yet supported in an instantiated module"
    for (_, group) in template.invSets do
      let parents := group.parents.map fun parent =>
        if template.moduleReferences.any (·.name == parent) then
          (occurrence.bindings.find? (·.1 == parent)).get!.2.raw.getId
        else occurrence.name ++ parent
      invSets := invSets.push { group with
        name := occurrence.name ++ group.name
        parents
        targets := Std.HashSet.ofArray (group.targets.toArray.map (specializedIdentifier template occurrence.name)) }
  for replay in requirements ++ fields do
    replayCommand replay.command (some replay)
  for replay in declarations do
    let command ← pinCallableInstances (← getCurrentModule) callables replay.command
    replayCommand command (some replay)
  unless (← getCurrentModule).isStateDefined do
    replayCommand (← `(command| #gen_state))
  let mut items : Array (TSyntax ``Lean.Parser.Term.doSeqItem) := #[]
  for (owner, replay) in initializers do
    let command ← pinCallableInstances (← getCurrentModule) callables replay.command
    let `(command| after_init { $body:doSeq }) := command | throwUnsupportedSyntax
    let previous ← getCurrentModule
    localEnv.modifyModule fun _ => { previous with
      sourceCommandScope? := some replay.scope
      sourceInstanceNames? := some replay.classes
      sourceInstanceArguments := replay.arguments
      sourceInstanceFieldNames? := some replay.instanceFields }
    let mod ← (← getCurrentModule).defineInstanceInitializerFrame owner body
    let mod := { mod with sourceCommandScope? := none, sourceInstanceNames? := none, sourceInstanceArguments := #[], sourceInstanceFieldNames? := none }
    localEnv.modifyModule (fun _ => mod)
    let name := Name.mkSimple s!"inst_{owner.toString.length}_{owner}__initializer"
    let call ← mod.explicitClassCall name #[]
    items := items.push (← `(doSeqItem| $call:term))
  if initializers.isEmpty then throwError "instantiated modules require after_init blocks"
  let body ← `(doSeq| $items:doSeqItem*)
  replayCommand (← `(command| after_init { $body:doSeq }))
  let mod ← getCurrentModule
  let mod ← invSets.foldlM (fun mod group => mod.registerInvSet group) mod
  let mod := { mod with replayingInstance := false, sourceCommandScope? := none, sourceInstanceNames? := none, sourceInstanceArguments := #[], sourceInstanceFieldNames? := none }
  localEnv.modifyModule (fun _ => mod)
  return mod

/-- A failed specialization must not leave an incomplete action table or a
half-built state that a later check could mistake for the source program. -/
def Module.materializeIsolates (mod : Module) : CommandElabM Module := do
  if mod.instances.isEmpty || mod.instancesMaterialized then return mod
  let saved ← get
  try
    mod.materializeIsolatesCore
  catch ex =>
    let failed ← get
    set { saved with messages := failed.messages, traceState := failed.traceState }
    throw ex

end Veil
