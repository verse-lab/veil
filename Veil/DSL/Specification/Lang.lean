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

@[command_elab Veil.moduleDeclaration]
def elabModuleDeclaration : CommandElab := fun stx => do
  match stx with
  | `(veil module $i:ident) => do
    let cmd ← `(namespace $i:ident
      open Classical)
    elabCommand cmd
    declareSpecName i.getId
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

/- We use a macro here rather than a command elaborator, since the
latter seems to trigger the unused variable linter. -/
macro_rules
  | `(command|instantiate $nm:ident : $tp:term) => `(variable [$nm : $tp])

private def defineStateComponent (mutab : Option (TSyntax `stateMutability)) (kind : TSyntax `stateComponentKind) (name : Name) (tp : StateComponentType) :=
    let mutability := stxToMut mutab
    let kind := stxToKind kind
    let comp := StateComponent.mk mutability kind name tp .none
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
      | _ => unreachable!
    else
      Mutability.mutable

  stxToKind (k : TSyntax `stateComponentKind) : StateComponentKind :=
    match k with
    | `(stateComponentKind|individual) => StateComponentKind.individual
    | `(stateComponentKind|relation) => StateComponentKind.relation
    | `(stateComponentKind|function) => StateComponentKind.function
    | _ => unreachable!

  validateTpFn (kind : StateComponentKind) (tp : Expr) : CommandElabM Bool := do
    match kind with
    | .individual => return !tp.isArrow
    | .relation =>
      let returnsProp ← liftTermElabM $ forallTelescope tp (fun _ b => do return b.isProp)
      return returnsProp
    | .function => return tp.isArrow

  failureMsgFn (kind : StateComponentKind) (comp : StateComponent) : CoreM Unit := do
    match kind with
    | .individual => throwErrorAt (← comp.stx) "Invalid type: individuals must not be arrow types"
    | .relation => throwErrorAt (← comp.stx) "Invalid type: relations must return Prop"
    | .function => throwErrorAt (← comp.stx) "Invalid type: functions must have arrow type"

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
      let name := nm.getId
      checkModuleExists name
      checkCorrectInstantiation name ts
      let modAlias := if let `(Veil.moduleAbbrev| as $al) := ma then al.getId else name
      let modParams := (<- globalSpecCtx.get)[name]!.parameters
      let modDep : ModuleDependency := {
        name := name,
        parameters := modParams,
        arguments := ts
      }
      let stateArgs ← Command.runTermElabM fun _ => getStateArguments modParams ts
      let sig ← `(Command.structSimpleBinder|$(mkIdent modAlias):ident : @$(mkIdent $ name ++ `State) $stateArgs*)
      -- FIXME: we MUST respect the `mutable`/`immutable` attribute of the
      -- dependency's state components, but we currently don't!
      let mutab ← `(stateMutability|mutable)
      let kind ← `(stateComponentKind|individual)
      defineStateComponent mutab kind modAlias (.simple sig)
      trace[veil.debug] "lifting state from module {name} as {modAlias}:\n{stx}"
      localSpecCtx.modify (fun s => { s with spec.dependencies := s.spec.dependencies.push (modAlias, modDep) })
  | _ => throwUnsupportedSyntax

/-- Assembles all declared `relation` predicates into a single `State` type. -/
def assembleState : CommandElabM Unit := do
  let vd := (<- getScope).varDecls
  declareSpecParameters vd
  let name <- getCurrNamespace
  let (sdef, isHOInst, smtAttr) <- Command.runTermElabM fun vs => do
    -- set the name
    let components ← liftCommandElabM $ liftCoreM $ ((<- localSpecCtx.get).spec.signature).mapM StateComponent.getSimpleBinder
    -- record the state name
    localSpecCtx.modify (fun s => { s with stateBaseName := name })
    let stName := `State
    let sdef ←
    `(@[stateDef]
      structure $(mkIdent stName) $(getStateParametersBinders vd)* where
        $(mkIdent `mk):ident :: $[$components]*
      deriving $(mkIdent ``Nonempty))
    let injEqLemma := (mkIdent $ stName ++ `mk ++ `injEq)
    let smtAttr ← `(attribute [smtSimp] $injEqLemma)
    let isHOInst ← `(instance (priority := default) $(mkIdent $ Name.mkSimple s!"{stName}_ho") $(getStateParametersBinders vd)* : IsHigherOrder (@$(mkIdent stName) $(← getStateArgumentsStx vd vs)*) := ⟨⟩)
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
  Command.runTermElabM fun vs => do
    -- we set `stateStx` ourselves
    let stateTp ← mkStateTpStx vd vs
    localSpecCtx.modify ({· with spec.stateStx := stateTp })
  -- Do work necessary for module composition
  genStateExtInstances
  defineDepsActions
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
    let stx' <- funcasesM t (← getStateArguments vd vs)
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
      -- let stateTp ← getStateTpStx
      -- let expectedType ← `($stateTp → Prop)
      let ini ←  simplifyTerm ini
      let predName := `initialState?
      -- because of `initDef`, this sets `stsExt.init` with `lang := none`
      `(@[initDef, initSimp] def $(mkIdent predName) $[$vd]* := $ini)
  | _ => throwUnsupportedSyntax

@[command_elab Veil.initialStateAction]
def elabInitialStateAction : CommandElab := fun stx => do
  match stx with
  | `(command|after_init { $l:doSeq }) => do
    liftCoreM errorIfStateNotDefined
    let (ret, st, st', st_curr, post) := (mkIdent `ret, mkIdent `st, mkIdent `st', mkIdent `st_curr, mkIdent `post)
    let vd ← getAssertionParameters
    -- define initial state action (`Wp`)
    let act ← Command.runTermElabM fun _ => (do
      let stateTp ← getStateTpStx
      `(fun ($st : $stateTp) ($post : SProp $stateTp) => (do' .external in $l) $st (fun $ret ($st_curr : $stateTp) => $post $st_curr)))
    elabCommand $ ← Command.runTermElabM fun _ => do
      let actName := `init
      `(@[initSimp, actSimp] def $(mkIdent actName) $[$vd]* := $act)
    -- define initial state predicate
    let pred ← Command.runTermElabM fun _ => (do
      let stateTp ← getStateTpStx
      `(fun ($st' : $stateTp) => ∃ ($(toBinderIdent st) : $stateTp), Wp.toTwoState (do' .external in $l) $st $st'))
    -- this sets `stsExt.init` with `lang := none`
    elabCommand $ ← `(initial $pred)
    -- we modify it to store the `lang`
    liftTermElabM do localSpecCtx.modify (fun s => { s with spec := {s.spec with init := {s.spec.init with lang := .some l}}})
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

@[command_elab Veil.nativeTransitionDefinition]
def elabNativeTransition : CommandElab := fun stx => do
  match stx with
  | `(command|$actT:actionKind ? transition $nm:ident $br:explicitBinders ? = $tr) => do
    liftCoreM errorIfStateNotDefined
    let actT ← parseActionKindStx actT
    defineTransition actT nm br tr
    -- warn if this is not first-order
    Command.liftTermElabM $ warnIfNotFirstOrder nm.getId
  | _ => throwUnsupportedSyntax


@[command_elab Veil.transitionDefinition]
def elabTransition : CommandElab := fun stx => do
  match stx with
  | `(command|$actT:actionKind ? transition $nm:ident $br:explicitBinders ? = { $t:term }) => do
    let fields : Array Name ← getFields
    let mut unchangedFields := #[]
    for f in fields do
      unless t.raw.find? (·.getId.toString == f.toString ++ "'") |>.isSome do
        unchangedFields := unchangedFields.push $ mkIdent f
    let stx ← `($actT:actionKind ? transition $nm $br ? = by
      intros st st'
      unhygienic cases st
      with_rename "'" unhygienic cases st'
      exact [unchanged|"'"| $unchangedFields*] ∧ ($t))
    elabCommand stx
  | _ => throwUnsupportedSyntax

/-! ## Actions -/

def elabAction (actT : Option (TSyntax `actionKind)) (nm : Ident) (br : Option (TSyntax ``Lean.explicitBinders))
  (spec : Option doSeq) (l : doSeq) : CommandElabM Unit := do
    liftCoreM errorIfStateNotDefined
    let actT ← parseActionKindStx actT
    -- Create all the action-related declarations
    defineAction actT nm br l
    -- warn if this is not first-order
    Command.liftTermElabM <| warnIfNotFirstOrder nm.getId
    unless spec.isNone do
      registerActionSpec nm.getId spec
      let (pre, binder, post) <- getPrePost spec.get!
      defineAction actT (nm.getId ++ `spec |> mkIdent) br spec.get!
      checkSpec nm br pre post binder
where
  checkSpec (nm : Ident) (br : Option (TSyntax `Lean.explicitBinders))
  (pre post : Term) (ret : TSyntax `rcasesPat) : CommandElabM Unit := do
  try
    elabCommand $ ← Command.runTermElabM fun vs => do
      let st := mkIdent `st
      let thmName := mkIdent $ nm.getId ++ `spec_correct
      let br' <- (toBracketedBinderArray <$> br) |>.getD (pure #[])
      let br <- (explicitBindersIdents <$> br) |>.getD (pure #[])
      let stx <- `(theorem $thmName $br' * : ∀ $st:ident,
          (fun s => funcases s $pre) $st ->
          @$nm $(← getSectionArgumentsStx vs)* $br* $st (by rintro $ret; exact (funcases $post)) := by
          intro
          solve_clause)
      trace[veil.debug] "{stx}"
      return stx
    trace[veil.info] "{nm} specification is verified"
  catch e =>
    throwError s!"Error while checking the specification of {nm}:" ++ e.toMessageData

elab_rules : command
  | `(command|$actT:actionKind ? action $nm:ident $br:explicitBinders ? = {$l:doSeq}) => do
  elabAction actT nm br none l
  | `(command|$actT:actionKind ? action $nm:ident $br:explicitBinders ? = $spec:doSeq {$l:doSeq}) =>
  elabAction actT nm br spec l

/-! ## Isolates -/
elab_rules : command
  | `(command|open_isolate $is:ident $[with $iss:ident*]? ) => do
    let isStore := (<- localIsolates.get).isolateStore
    let mut invsFromIss : Std.HashSet Name := isStore[is.getId]?.getD ∅
    unless iss.isNone do
      for is in iss.get! do
        invsFromIss := invsFromIss.union <| isStore[is.getId]?.getD ∅
    localIsolates.modify fun ⟨openIs, _⟩ =>
      ⟨is.getId :: openIs, isStore.insert is.getId invsFromIss⟩
  | `(command|close_isolate) => do
    let _ :: openIs := (<- localIsolates.get).openIsolates
      | throwError "No open isolates to close"
    localIsolates.modify ({· with openIsolates := openIs})

def addInvariantToIsolate [Monad m] [MonadEnv m] (inv : Name) : m (List Name) := do
  let ⟨openIs, isStore⟩ := (<- localIsolates.get)
  for is in openIs do
    let invs := (isStore[is]?.getD ∅).insert inv
    localIsolates.modify ({ · with isolateStore := isStore.insert is invs })
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
  liftCoreM errorIfStateNotDefined
  let vd ← getAssertionParameters
  let (name, cmd) ← Command.runTermElabM fun vs => do
    let stateTp <- getStateTpStx
    -- Check that the assumption does not refer to mutable state components
    if kind == .assumption then
      throwIfRefersToMutable t
    let stx <- funcasesM t (← getStateArguments vd vs)
    let defaultName ← match kind with
      | .safety | .invariant => pure $ Name.mkSimple s!"inv_{(<- localSpecCtx.get).spec.invariants.size}"
      | .assumption | .trustedInvariant => pure $ Name.mkSimple s!"axiom_{(<- localSpecCtx.get).spec.assumptions.size}"
    let name := getPropertyNameD name defaultName
    let cmd ← elabBindersAndCapitals #[] vs stx fun _ e => do
      let e <- delabWithMotives e
      match kind with
      | .safety =>
        `(@[safeDef, safeSimp, invSimp] def $(mkIdent name) $[$vd]*: $stateTp -> Prop := fun $(mkIdent `st) => $e: term)
      | .invariant =>
        `(@[invDef, invSimp] def $(mkIdent name) $[$vd]* : $stateTp -> Prop := fun $(mkIdent `st) => $e: term)
      | .assumption | .trustedInvariant =>
        `(@[assumptionDef, invSimp, invSimpTopLevel] def $(mkIdent name) $[$vd]* : $stateTp -> Prop := fun $(mkIdent `st) => $e: term)
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
  let vd := (<- getScope).varDecls
  assembleNext
  assembleInvariant
  assembleSafeties
  assembleAssumptions
  assembleLabelType name
  let rtsStx <- Command.runTermElabM fun vs => do
    let sectionArgs ← getSectionArgumentsStx vs
    let stateTpStx <- getStateTpStx
    let [initialState?, Assumptions, Next, Safety, Invariant] :=
      [`initialState?, `Assumptions, `Next, `Safety, `Invariant].map Lean.mkIdent
      | unreachable!
    `(instance (priority := low) $(mkIdent `System) $[$vd]* : $(mkIdent ``RelationalTransitionSystem) $stateTpStx where
        init := @$initialState? $sectionArgs*
        assumptions := @$Assumptions $sectionArgs*
        next := @$Next $sectionArgs*
        safe := @$Safety $sectionArgs*
        inv  := @$Invariant $sectionArgs*
        )
  trace[veil.info] "{rtsStx}"
  elabCommand rtsStx
  trace[veil.info] "RelationalTransitionSystem instance instantiated"

@[inherit_doc instantiateSystem]
def genSpec : CommandElabM Unit := do
  liftCoreM (do errorIfStateNotDefined; warnIfNoInvariantsDefined; warnIfNoActionsDefined)
  let some name := (← localSpecCtx.get).stateBaseName
    | throwError "Command is run outside of a module declaration"
  trace[veil.info] "State, invariants and actions are defined"
  instantiateSystem name
  Command.runTermElabM fun _ => do
    -- set the name of the spec
    localSpecCtx.modify (fun s => { s with spec := {s.spec with name := name }})
    -- globally register the spec, so it can be composed with other modules
    registerModuleSpecification (← localSpecCtx.get).spec

elab_rules : command
  | `(command|#gen_spec) => genSpec
