import Lean
import Lean.Parser
import Veil.DSL.Base
import Veil.DSL.Internals.Attributes
import Veil.DSL.Internals.StateExtensions
import Veil.DSL.Action.Lang
import Veil.DSL.Tactic
import Veil.Tactic.Main
import Veil.Util.DSL


import Veil.DSL.Specification.Syntax
import Veil.DSL.Specification.SpecDef
import Veil.DSL.Specification.ActionDef

open Lean Elab Command Term Meta Lean.Parser

/-!
  # Specification Language Semantics

  This file defines the elaborators (i.e. semantics in terms of Lean
  definitions) for the specification language, which is used to declare Veil
  modules.

-/

def elabGenericState : CommandElabM Unit := do
  let genericState ← `(variable ($genericState : Type) [$genericSubStateIdent : IsSubStateOf $(← getStateTpStx) $genericState])
  trace[veil.debug] "genericState: {genericState}"
  elabCommand genericState

@[command_elab Veil.moduleDeclaration]
def elabModuleDeclaration : CommandElab := fun stx => do
  match stx with
  | `(veil module $i:ident) => do
    let cmd ← `(namespace $i:ident
      open Classical)
    elabCommand cmd
    let gctx := <- globalSpecCtx.get
    let name := i.getId
    if gctx.contains name then
      logInfo s!"Module {name} already exists. Importing it here."
      let ctx := gctx[name]!
      -- import the context
      localSpecCtx.modify (fun _ => ctx)
      -- re-declare the section variables
      elabCommand $ ← `(variable $(ctx.spec.generic.parameters)*)
      -- FIXME: handle this in a better way as part of `.parameters`
      elabGenericState
    else
      declareSpecName name
  | _ => throwUnsupportedSyntax

/-! ## State -/

@[command_elab Veil.typeDeclaration]
def elabTypeDeclaration : CommandElab := fun stx => do
  match stx with
  | `(type $id:ident) => do
    let dec_id := Lean.mkIdent (Name.mkSimple s!"{id.getId}_dec")
    let ne_id := Lean.mkIdent (Name.mkSimple s!"{id.getId}_ne")
    let deceq := Lean.mkIdent ``DecidableEq
    let nemp := Lean.mkIdent ``Nonempty
    let cmd ← `(variable ($id : Type) [$dec_id : $deceq $id] [$ne_id : $nemp $id])
    elabCommand cmd
  | _ => throwUnsupportedSyntax


@[command_elab Veil.enumDeclaration]
def elabEnumDeclaration : CommandElab := fun stx => do
  match stx with
  | `(enum $id:ident = { $[$elems:ident],* }) => do
    -- Declare the uninterpreted sort
    elabCommand $ ← `(type $id)
    -- Declare a class for the enum type
    let variants ← elems.mapM (fun elem => `(Command.structSimpleBinder|$elem:ident : $id))
    let (class_name, ax_distinct, ax_complete) := (mkIdent (Name.mkSimple s!"{id.getId}_Enum"), mkIdent $ Name.mkSimple s!"{id.getId}_distinct", mkIdent $ Name.mkSimple s!"{id.getId}_complete")
    let ax_distinct ← `(Command.structSimpleBinder|$ax_distinct:ident : distinct $[$elems]*)
    let x := mkIdent $ Name.mkSimple s!"{id.getId}_x"
    let ax_complete ← `(Command.structSimpleBinder|$ax_complete:ident : ∀ ($x : $id), $(← isEqualToOneOf x elems))
    let class_decl ← `(
      class $class_name ($id : outParam Type) where
        $[$variants]*
        $ax_distinct
        $ax_complete
    )
    elabCommand class_decl
    let instanceName := mkIdent $ Name.mkSimple s!"{id.getId}_isEnum"
    let instanceV ← `(command|instantiate $instanceName : @$class_name $id)
    elabCommand instanceV
    elabCommand $ ← `(open $class_name:ident)

  | _ => throwUnsupportedSyntax
where
isEqualToOneOf {m} [Monad m] [MonadQuotation m] (x : TSyntax `term) (xs : Array (TSyntax `term)) : m (TSyntax `term) := do
  let equalities ← xs.mapM (fun elem => `($x = $(elem)))
  repeatedOr equalities

/- We use a macro here rather than a command elaborator, since the
latter seems to trigger the unused variable linter. -/
macro_rules
  | `(command|instantiate $nm:ident : $tp:term) => `(variable [$nm : $tp])

private def defineStateComponent (mutab : Option (TSyntax `stateMutability)) (kindStx : TSyntax `stateComponentKind) (name : Name) (tp : StateComponentType) (moduleName : Option Name := none) := do
    liftCoreM errorIfStateAlreadyDefined
    let mutability := stxToMut mutab
    let kind := stxToKind kindStx
    if kind == StateComponentKind.module && moduleName.isNone then
      throwErrorAt kindStx "Module state components must specify the name of the module they are the state of"
    if moduleName.isSome && kind != StateComponentKind.module then
      throwErrorAt kindStx "Passed `moduleName` argument {moduleName} to `defineStateComponent` for a non-module state component"
    let comp := StateComponent.mk mutability kind name tp moduleName
    defineStateComponentImpl comp (validateTpFn kind) (failureMsgFn kind)

where
  defineStateComponentImpl (comp : StateComponent) (validateTp : Expr → CommandElabM Bool) (failureMsg : StateComponent → CoreM Unit) := do
    /- When you include module `M` in your current module, to get access to a
    field `F` of `M` you would write `M.F`. Hence non-atomic names (those with
    `.`) might lead to confusion, so we prohibit them. -/
    unless comp.name.isAtomic do throwError "Invalid name: {comp.name} must be atomic"
    let sig ← liftCoreM $ comp.getSimpleBinder
    let tp ← do match sig with
      /- e.g. `relation initial_msg : address → address → round → value → Prop` -/
    | `(Command.structSimpleBinder| $_:ident : $tp:term) =>
      runTermElabM fun _ => elabTerm tp none
    | _ => throwErrorAt sig "Unsupported syntax {sig}"
    if ← validateTp tp then
      liftTermElabM do localSpecCtx.modify (fun s => { s with spec := {s.spec with signature := s.spec.signature.push comp }})
    else
      liftCoreM $ failureMsg comp

  /-- Fields are `mutable` by default. -/
  stxToMut (m : Option (TSyntax `stateMutability)) : Mutability :=
    if let some stx := m then
      match stx with
      | `(stateMutability|immutable) => Mutability.immutable
      | `(stateMutability|mutable) => Mutability.mutable
      | `(stateMutability|passthrough) => Mutability.passthrough
      | _ => unreachable!
    else
      Mutability.mutable

  stxToKind (k : TSyntax `stateComponentKind) : StateComponentKind :=
    match k with
    | `(stateComponentKind|individual) => StateComponentKind.individual
    | `(stateComponentKind|relation) => StateComponentKind.relation
    | `(stateComponentKind|function) => StateComponentKind.function
    | `(stateComponentKind|module) => StateComponentKind.module
    | _ => unreachable!

  validateTpFn (kind : StateComponentKind) (tp : Expr) : CommandElabM Bool := do
    match kind with
    | .individual => return !tp.isArrow
    | .relation =>
      let returnsProp ← liftTermElabM $ forallTelescope tp (fun _ b => do return b.isProp)
      return returnsProp
    | .function => return tp.isArrow
    | .module =>
      -- `tp` must be a structure
      let constName := tp.getAppFn.constName?
      match constName with
      | .some constName => return (isStructure (←  getEnv) constName)
      | .none => return false

  failureMsgFn (kind : StateComponentKind) (comp : StateComponent) : CoreM Unit := do
    match kind with
    | .individual => throwErrorAt (← comp.stx) "Invalid type: individuals must not be arrow types"
    | .relation => throwErrorAt (← comp.stx) "Invalid type: relations must return Prop"
    | .function => throwErrorAt (← comp.stx) "Invalid type: functions must have arrow type"
    | .module => throwErrorAt (← comp.stx) "Invalid type: module state components must be structures"

@[command_elab Veil.declareStateComponent]
def elabStateComponentNamed : CommandElab := fun stx => do
  match stx with
  | `(command|$mutab:stateMutability ? $kind:stateComponentKind $name:ident $br:bracketedBinder* : $dom:term) => do
    defineIt mutab kind name br dom
  | `(command|$mutab:stateMutability ? relation $name:ident $br:bracketedBinder*) => do
    let kind ← `(stateComponentKind|relation)
    let dom ← `(Prop)
    defineIt mutab kind name br dom
  -- FIXME: show a better error message when user forgets to specify domain type
  | _ => throwUnsupportedSyntax
where
  defineIt (mutab : Option (TSyntax `stateMutability)) (kind : TSyntax `stateComponentKind) (name : Ident) (br : TSyntaxArray ``Term.bracketedBinder) (dom : TSyntax `term) := do
    if !br.isEmpty then
      defineStateComponent mutab kind name.getId (.complex br dom)
    else
      let sig ← `(Command.structSimpleBinder|$name:ident : $dom)
      defineStateComponent mutab kind name.getId (.simple sig)

@[command_elab Veil.declareDependency]
def elabDependency : CommandElab := fun stx => do
  match stx with
  | `(command|includes $nm:ident $ts:term* $ma:moduleAbbrev) => do
      let fullModuleName := nm.getId
      checkModuleExists fullModuleName
      liftCoreM $ checkCorrectInstantiation fullModuleName ts
      let modAlias := if let `(Veil.moduleAbbrev| as $al) := ma then al.getId else fullModuleName
      let modParams := (<- globalSpecCtx.get)[fullModuleName]!.spec.generic
      let modDep : ModuleDependency := {
        name := fullModuleName,
        generic := modParams,
        arguments := ts
      }
      let stateArgs ← Command.runTermElabM fun _ => modParams.applyGetStateArguments ts
      trace[veil.debug] "ts: {ts} => stateArgs: {stateArgs}"
      let sig ← `(Command.structSimpleBinder|$(mkIdent modAlias):ident : @$(mkIdent $ fullModuleName ++ `State) $stateArgs*)
      -- NOTE: set `mutab` to `passthrough` if you want to pass-through
      -- mutability annotations; by default, the state of the child module
      -- is immutable in the parent
      let mutab ← `(stateMutability|immutable)
      let kind ← `(stateComponentKind|module)
      defineStateComponent mutab kind modAlias (.simple sig) fullModuleName
      trace[veil.debug] "lifting state from module {fullModuleName} as {modAlias}:\n{stx}"
      localSpecCtx.modify (fun s => { s with spec.dependencies := s.spec.dependencies.push (modAlias, modDep) })
  | _ => throwUnsupportedSyntax

/-- Assembles all declared `relation` predicates into a single `State` type.
  Since our action definitions are parametric in the `State` type, this
  also creates `variable (σ : Type) [IsSubState [State] σ]` declaration.
-/
def assembleState : CommandElabM Unit := do
  let vd := (<- getScope).varDecls
  declareSpecParameters vd
  let binders' := getStateParametersBinders vd
  let args' ← bracketedBindersToTerms' binders'
  let binders := binders'.map (fun (_, b) => b)
  let args := args'.map (fun (_, arg) => arg)
  let name <- getCurrNamespace
  let (sdef, isHOInst, smtAttr) <- Command.runTermElabM fun _ => do
    -- set the name
    let components ← liftCommandElabM $ liftCoreM $ ((<- localSpecCtx.get).spec.signature).mapM StateComponent.getSimpleBinder
    -- record the state name
    localSpecCtx.modify (fun s => { s with stateBaseName := name })
    let stName := `State
    let sdef ←
    `(@[stateDef]
      structure $(mkIdent stName) $binders* where
        $(mkIdent `mk):ident :: $[$components]*
      deriving $(mkIdent ``Nonempty))
    let injEqLemma := (mkIdent $ stName ++ `mk ++ `injEq)
    let smtAttr ← `(attribute [smtSimp] $injEqLemma)
    let isHOInst ← `(instance (priority := default) $(mkIdent $ Name.mkSimple s!"{stName}_ho") $binders* : IsHigherOrder (@$(mkIdent stName) $args*) := ⟨⟩)
    trace[veil.debug] "{sdef}"
    trace[veil.debug] "{isHOInst}"
    -- Tag the `injEq` lemma as `smtSimp`
    return (sdef, isHOInst, smtAttr)
  -- `@[stateDef]` sets `spec.stateType` (the base constant `stName`)
  elabCommand sdef
  -- Tag `State` as a higher-order type
  elabCommand isHOInst
  -- Tag the `injEq` lemma as `smtSimp`
  elabCommand smtAttr
  -- Do not show unused variable warnings for field names
  generateIgnoreFn
  Command.runTermElabM fun _ => do
    -- IMPORTANT: here we set most of `ModuleParameters`
    let stateTpExpr := (<- localSpecCtx.get).spec.generic.stateType
    unless stateTpExpr != default do throwError "State has not been declared so far"
    let stateTypeTerm ← PrettyPrinter.delab stateTpExpr
    localSpecCtx.modify ({· with
      spec.generic.stateTypeTerm := stateTypeTerm,
      spec.generic.stateArgs := args',
      -- for $genericState and $genericSubStateIdent
      spec.generic.genericStateParam := vd.size,
      spec.generic.genericSubStateInstParam := vd.size + 1 })
  elabGenericState
  -- Do work necessary for module composition
  genStateExtInstances
  defineDepsProcedures
where
  /-- Instruct the linter to not mark state variables as unused in our
  `after_init` and `action` definitions. -/
  generateIgnoreFn : CommandElabM Unit := do
    let cmd ← Command.runTermElabM fun _ => do
      let fieldNames ← getFields
      let fnIdents ← fieldNames.mapM (fun n => `($(quote n)))
      let namesArrStx ← `(#[$[$fnIdents],*])
      let fnStx ← `(fun id stack _ => ($namesArrStx).contains id.getId /-&& isActionSyntax stack-/)
      let nm := mkIdent $ ← getPrefixedName `ignoreStateFields
      let ignoreFnStx ← `(@[unused_variables_ignore_fn] def $nm : Lean.Linter.IgnoreFunction := $fnStx)
      return ignoreFnStx
    elabCommand cmd
  /- We don't pass typeclass arguments (e.g. `[DecidableEq node]`) to the
  `State` type, since we want to use `deriving Nonempty` on the
  `structure` we create, and it seems it gets confused by them -/
  getStateParametersBinders (vd : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) : Array (Nat × TSyntax `Lean.Parser.Term.bracketedBinder) :=
    let pairs := Array.zip (List.range' 0 vd.size).toArray vd
    pairs.filter (fun (_, b) => !isTypeClassBinder b)
@[command_elab Veil.genState]
def elabGenState : CommandElab := fun _stx => do assembleState

/-! ## Ghost relations -/
@[command_elab Veil.ghostRelationDefinition]
def elabGhostRelationDefinition : CommandElab := fun stx => do
  match stx with
  | `(command|ghost relation $nm:ident $br:bracketedBinder* := $t:term) => do
  liftCoreM errorIfStateNotDefined
  let vd := (<- getScope).varDecls
  -- As we are going to call this predicate explicitly we want to make all
  -- section binders implicit
  let vd' <- vd.mapM (fun x => mkImplicitBinders x)
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- getStateTpStx
    let stx' <- funcasesM t
    elabBindersAndCapitals br vs stx' fun _ e => do
      let e <- delabWithMotives e
      let stx ← `(@[actSimp, invSimp, invSimpTopLevel] abbrev $nm $[$vd']* $br* ($(mkIdent `st) : $stateTp := by exact_state) : Prop := $e)
      trace[veil.debug] "{stx}"
      return stx
  | _ => throwUnsupportedSyntax

/-! ## Initializers -/

@[command_elab Veil.initialStatePredicate]
def elabInitialStatePredicate : CommandElab := fun stx => do
  match stx with
  | `(command|initial $ini) => do
    liftCoreM errorIfStateNotDefined
    let vd ← getAssertionParameters
    elabCommand <| <- Command.runTermElabM fun _ => do
      -- let ini ←  simplifyTerm ini
      let predName := initialStateName
      -- because of `initDef`, this sets `stsExt.init` with `lang := none`
      let stx ← `(@[initDef, initSimp] def $(mkIdent predName) $[$vd]* := $ini)
      trace[veil.info] "initial state predicate: {stx}"
      return stx
  | _ => throwUnsupportedSyntax

@[command_elab Veil.initialStateAction]
def elabInitialStateAction : CommandElab := fun stx => do
  match stx with
  | `(command|after_init { $l:doSeq }) => do
    liftCoreM errorIfStateNotDefined
    -- Our initializer should run all sub-module initializers in the
    -- order they are included in
    let subInitializers ← (← getSubInitializers).mapM (fun (nm, _) => `(Term.doSeqItem|$nm:term))
    let ourInitializer ← getItemsFromDoSeq l
    let init ← `(doSeq|do $subInitializers*; $(ourInitializer)*)
    -- define the initial action (on the generic state type)
    let initName := mkIdent initializerName
    let (genI, genE) ← defineProcedureGenerators initName none init
    defineInitialActionFromGenerators initName genI genE
    -- define initial state predicate (on the concrete state type)
    let (st, stₛ, st', stateSimpH) := (mkIdent `st, mkIdent `stₛ, mkIdent `st', mkIdent stateSimpHypName)
    let pred ← Command.runTermElabM fun vs => (do
      let stateTp <- getStateTpStx
      let extInit := mkIdent (toExtName initializerName)
      let args ← getSectionArgumentsStx vs
      `(fun ($st' : $genericState) => ∃ ($(toBinderIdent st) : $genericState) ($(toBinderIdent stₛ) : $stateTp) ($(toBinderIdent stateSimpH) : $(mkIdent ``Eq) ($(mkIdent ``getFrom) $st) $stₛ), Wp.toTwoState (@$extInit $args*) $st $st'))
    trace[veil.debug] "pred: {pred}"
    -- this sets `stsExt.init` with `lang := none`
    elabCommand $ ← `(initial $pred)
    -- we modify it to store the `lang`
    liftTermElabM do localSpecCtx.modify (fun s => { s with spec := {s.spec with init := {s.spec.init with lang := .some init}}})
    let sp ← liftTermElabM $ return (← localSpecCtx.get).spec.init
    trace[veil.debug] s!"{sp}"
  | _ => throwUnsupportedSyntax

/-! ## Transitions -/

/-- Show a warning if the given declaration has higher-order quantification -/
def warnIfNotFirstOrder (name : Name) : TermElabM Unit := do
  let modName <- getCurrNamespace
  let .some decl := (← getEnv).find? (modName ++ name) | throwError s!"{name} not found"
  let .some val := decl.value? | throwError s!"{name} has no value"
  let isFirstOrderUniv ← allHOQuantIsTopLevelForAll val
  if !isFirstOrderUniv then
    logWarning s!"{name} is not first-order (and cannot be sent to SMT)"

def elabNativeTransition (actT : Option (TSyntax `actionKind)) (nm : Ident) (br : Option (TSyntax ``Lean.explicitBinders)) (tr : TSyntax `term) : CommandElabM Unit := do
  liftCoreM (do errorIfStateNotDefined; errorIfSpecAlreadyDefined)
  let actT ← parseActionKindStx actT
  defineTransition actT nm br tr
  -- warn if this is not first-order
  Command.liftTermElabM $ warnIfNotFirstOrder nm.getId

@[command_elab Veil.transitionDefinition]
def elabTransition : CommandElab := fun stx => do
  match stx with
  | `(command|$actT:actionKind ? transition $nm:ident $br:explicitBinders ? = { $t:term }) => do
    let changedFn := (fun f => t.raw.find? (·.getId.toString == (mkPrimed f).toString) |>.isSome)
    let unchangedFields ← getUnchangedFields changedFn
    trace[veil.info] "Unchanged fields: {unchangedFields}"
    let changedFields ← getChangedFields changedFn
    for f in changedFields do
      liftTermElabM $ throwIfImmutable' f.getId (isTransition := true)
    let (st, st') := (mkIdent `st, mkIdent `st')
    let trStx ← `(fun ($st $st' : $genericState) => let ($st, $st') := (getFrom $st, getFrom $st')
      by
      unhygienic cases $st:ident
      with_rename "'" unhygienic cases $st':ident
      exact [unchanged|"'"| $unchangedFields*] ∧ ($t))
    elabNativeTransition actT nm br trStx
  | _ => throwUnsupportedSyntax

/-! ## Actions -/

def checkSpec (nm : Ident) (br : Option (TSyntax `Lean.explicitBinders))
  (pre post : Term) (ret : TSyntax `rcasesPat) : CommandElabM Unit := do
  try
    elabCommand $ ← Command.runTermElabM fun vs => do
      let st := mkIdent `st
      let thmName := mkIdent $ nm.getId ++ `spec_correct
      let br' <- (toBracketedBinderArray <$> br) |>.getD (pure #[])
      let br <- (explicitBindersIdents <$> br) |>.getD (pure #[])
      let actionArgs ← getSectionArgumentsStx vs
      let stx <- `(theorem $thmName $br' * : ∀ $st:ident,
          (fun s => funcases s $pre) $st ->
          @$nm $actionArgs* $br* $st (by rintro $ret; exact (funcases $post)) := by
          intro
          solve_clause)
      trace[veil.debug] "{stx}"
      return stx
    trace[veil.info] "{nm} specification is verified"
  catch e =>
    throwError s!"Error while checking the specification of {nm}:" ++ e.toMessageData

def elabAction (actT : Option (TSyntax `actionKind)) (nm : Ident) (br : Option (TSyntax ``Lean.explicitBinders))
  (spec : Option doSeq) (l : doSeq) : CommandElabM Unit := do
    liftCoreM (do errorIfStateNotDefined; errorIfSpecAlreadyDefined)
    let actT ← parseActionKindStx actT
    -- Create all the action-related declarations
    defineAction actT nm br l
    -- warn if this is not first-order
    Command.liftTermElabM <| warnIfNotFirstOrder nm.getId
    unless spec.isNone do
      registerProcedureSpec nm.getId spec
      let (pre, binder, post) <- getPrePost spec.get!
      trace[veil.debug] "Defining specification for {nm} with pre: {pre}"
      defineProcedure (nm.getId ++ `spec |> mkIdent) br spec.get!
      checkSpec nm br pre post binder

def elabProcedure (nm : Ident) (br : Option (TSyntax ``Lean.explicitBinders)) (spec : Option doSeq) (l : doSeq) : CommandElabM Unit := do
  liftCoreM (do errorIfStateNotDefined; errorIfSpecAlreadyDefined)
  defineProcedure nm br l
  Command.liftTermElabM <| warnIfNotFirstOrder nm.getId
  unless spec.isNone do
    registerProcedureSpec nm.getId spec
    let (pre, binder, post) <- getPrePost spec.get!
    defineProcedure (nm.getId ++ `spec |> mkIdent) br spec.get!
    checkSpec nm br pre post binder

elab_rules : command
  | `(command|$actT:actionKind ? action $nm:ident $br:explicitBinders ? = {$l:doSeq}) => do
  elabAction actT nm br none l
  | `(command|$actT:actionKind ? action $nm:ident $br:explicitBinders ? = $spec:doSeq {$l:doSeq}) =>
  elabAction actT nm br spec l
  | `(command|procedure $nm:ident $br:explicitBinders ? = {$l:doSeq}) =>
  elabProcedure nm br none l
  | `(command|procedure $nm:ident $br:explicitBinders ? = $spec:doSeq {$l:doSeq}) =>
  elabProcedure nm br spec l

/-! ## Isolates -/
elab_rules : command
  | `(command|open_isolate $is:ident $[with $iss:ident*]? ) => do
    let isStore := (<- localSpecCtx.getIsolates).isolateStore
    let mut invsFromIss : Std.HashSet Name := isStore[is.getId]?.getD ∅
    unless iss.isNone do
      for is in iss.get! do
        invsFromIss := invsFromIss.union <| isStore[is.getId]?.getD ∅
    localSpecCtx.modifyIsolates fun ⟨openIs, _⟩ =>
      ⟨is.getId :: openIs, isStore.insert is.getId invsFromIss⟩
  | `(command|close_isolate) => do
    let _ :: openIs := (<- localSpecCtx.get).isolates.openIsolates
      | throwError "No open isolates to close"
    localSpecCtx.modifyIsolates ({· with openIsolates := openIs})

def addInvariantToIsolate [Monad m] [MonadEnv m] (inv : Name) : m (List Name) := do
  let ⟨openIs, isStore⟩ := (<- localSpecCtx.getIsolates)
  for is in openIs do
    let invs := (isStore[is]?.getD ∅).insert inv
    localSpecCtx.modifyIsolates ({ · with isolateStore := isStore.insert is invs })
  return openIs
  -- localSpecCtx.modify fun s =>
  -- { s with spec.invariants :=
  --   s.spec.invariants.map (fun x => if x.name == inv then { x with isolates := openIs } else x) }


/-! ## Assertions -/

def _root_.Lean.TSyntax.getPropertyName (stx : TSyntax `propertyName) : Name :=
  match stx with
  | `(propertyName| [$id]) => id.getId
  | _ => unreachable!

def getPropertyNameD (stx : Option (TSyntax `propertyName)) (default : Name) :=
  match stx with
  | some stx => stx.getPropertyName
  | none => default

def defineAssertion (kind : StateAssertionKind) (name : Option (TSyntax `propertyName)) (t : TSyntax `term) : CommandElabM Unit := do
  liftCoreM (do errorIfStateNotDefined; errorIfSpecAlreadyDefined)
  let vd ← getAssertionParameters
  let (name, cmd) ← Command.runTermElabM fun vs => do
    -- Check that the assumption does not refer to mutable state components
    if kind == .assumption then
      throwIfRefersToMutable t
    let stx <- funcasesM t
    let defaultName ← match kind with
      | .safety | .invariant => pure $ Name.mkSimple s!"inv_{(<- localSpecCtx.get).spec.invariants.size}"
      | .assumption | .trustedInvariant => pure $ Name.mkSimple s!"axiom_{(<- localSpecCtx.get).spec.assumptions.size}"
    let name := getPropertyNameD name defaultName
    let cmd ← elabBindersAndCapitals #[] vs stx fun _ e => do
      let e <- delabWithMotives e
      -- The implicit binders + `exact_state` trick is to allow using
      -- clauses in actions, e.g. `assert clauseName`
      let vd ← vd.mapM mkImplicitBinders
      match kind with
      | .safety =>
        `(@[safeDef, safeSimp, invSimp] def $(mkIdent name) $[$vd]* ($(mkIdent `st) : $genericState := by exact_state) : Prop := $e: term)
      | .invariant =>
        `(@[invDef, invSimp] def $(mkIdent name) $[$vd]* ($(mkIdent `st) : $genericState := by exact_state) : Prop := $e: term)
      | .assumption | .trustedInvariant =>
        `(@[assumptionDef, invSimp] def $(mkIdent name) $[$vd]* ($(mkIdent `st) : $genericState := by exact_state) : Prop := $e: term)
    -- IMPORTANT: It is incorrect to do `liftCommandElabM $ elabCommand cmd` here
    -- (I think because of how `elabBindersAndCapitals` works)
    return (name, cmd)
  -- Do the elaboration to populate the `stsExt` state
  trace[veil.debug] s!"{cmd}"
  elabCommand cmd
  trace[veil.info] s!"invariant {name} is defined"
  let iss <- addInvariantToIsolate name
  let name <- resolveGlobalConstNoOverloadCore name
  Command.runTermElabM fun _vs => do
    -- Record the term syntax in the `stsExt` state
    localSpecCtx.modify (fun s => { s with spec :=
    (match kind with
    | .safety | .invariant => {s.spec with
        invariants := s.spec.invariants.map (fun x => if x.name == name then { x with term := t, isolates := iss } else x) }
    | .assumption | .trustedInvariant => {s.spec with
        assumptions := s.spec.assumptions.map (fun x => if x.name == name then { x with term := t } else x) })})

elab_rules : command
  | `(command|assumption $name:propertyName ? $prop:term) => do
    defineAssertion .assumption name prop
  | `(command|invariant $name:propertyName ? $prop:term) => do
    defineAssertion .invariant name prop
  | `(command|safety $name:propertyName ? $prop:term) => do
    defineAssertion .safety name prop
  | `(command|trusted invariant $name:propertyName ? $prop:term) => do
    defineAssertion .trustedInvariant name prop

/-! ## Specification Generation -/

/--
Instantiates the `RelationalTransitionSystem` type class with the declared actions, safety and invariant
-/
def instantiateSystem (name : Name) : CommandElabM Unit := do
  let vd ← getSystemParameters
  assembleNext
  assembleInvariant
  assembleSafeties
  assembleAssumptions

  let labelTpStx ← `(term|$(mkIdent `Label) $(← getStateTpArgsStx)*)
  assembleLabelType name

  let (rtsStx, ioAutomatonStx) <- Command.runTermElabM fun vs => do
    let systemArgs ← getSectionArgumentsStx vs
    let stepStx ← getIOStepStx genericState labelTpStx vs

    let [initialState?, Assumptions, Next, Safety, Invariant] :=
      [initialStateName, `Assumptions, `Next, `Safety, `Invariant].map Lean.mkIdent
      | unreachable!
    -- RelationalTransitionSystem instance
    let rtsStx ← `(instance (priority := low) $(mkIdent `System) $[$vd]* : $(mkIdent ``RelationalTransitionSystem) $genericState where
        init := @$initialState? $systemArgs*
        assumptions := @$Assumptions $systemArgs*
        next := @$Next $systemArgs*
        safe := @$Safety $systemArgs*
        inv  := @$Invariant $systemArgs*
        )
    -- IO Automaton instance
    let ioAutomatonStx ← `(instance (priority := low) $(mkIdent `IOA) $[$vd]* : $(mkIdent ``IOAutomaton) $genericState $labelTpStx where
      signature := $(← getIOSignatureStx)
      init := @$initialState? $systemArgs*
      step := $stepStx
    )
    pure (rtsStx, ioAutomatonStx)
  trace[veil.info] "{rtsStx}"
  elabCommand rtsStx
  trace[veil.info] "RelationalTransitionSystem instance instantiated"
  trace[veil.info] "{ioAutomatonStx}"
  elabCommand ioAutomatonStx
  trace[veil.info] "IO Automaton instance instantiated"

@[inherit_doc instantiateSystem]
def genSpec : CommandElabM Unit := do
  liftCoreM (do errorIfStateNotDefined; errorIfNoInitialStateDefined; warnIfNoInvariantsDefined; warnIfNoActionsDefined)
  let some name := (← localSpecCtx.get).stateBaseName
    | throwError "Command is run outside of a module declaration"
  trace[veil.info] "State, invariants and actions are defined"
  instantiateSystem name
  Command.runTermElabM fun _ => do
    -- set the name of the spec
    localSpecCtx.modify (fun s => { s with spec := {s.spec with name := name }})
    -- globally register the spec, so it can be composed with other modules
    registerModuleSpecification

elab_rules : command
  | `(command|#gen_spec) => genSpec
