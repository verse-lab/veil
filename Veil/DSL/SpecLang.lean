import Lean
import Lean.Parser
import Veil.DSL.Base
import Veil.DSL.Attributes
import Veil.DSL.StateExtensions
import Veil.DSL.ActionLang
import Veil.DSL.Tactic
import Veil.Tactic.Main
import Veil.DSL.Util

open Lean Elab Command Term Meta Lean.Parser

/-!
  # Specification Language

  This file defines the syntax and elaborators (i.e. semantics in terms
  of Lean definitions) for the specification language.
-/

/-! ## State -/

/-! ### Semantics -/

/-- Defines a `constant`, `relation`, or `function`, validating its type
before adding it. -/
def defineStateComponent
  (comp : StateComponent)
  (validateTp : Expr → CommandElabM Bool := fun _ => pure true)
  (failureMsg : StateComponent → CoreM Unit := fun _ => do throwErrorAt (← comp.stx) s!"{comp} is not of the expected type")
   : CommandElabM Unit := do
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

/-- Define a `relation`. -/
def defineRelation (comp : StateComponent) : CommandElabM Unit :=
  defineStateComponent comp
     (fun (tp : Expr) => do
      let returnsProp ← liftTermElabM $ forallTelescope tp (fun _ b => do return b.isProp)
      return returnsProp)
    (fun comp => do throwErrorAt (← comp.stx) "Invalid type: relations must return Prop")

/-- Define a `function`. -/
def defineFunction (comp : StateComponent) : CommandElabM Unit :=
  defineStateComponent comp
    (fun (tp : Expr) => do return tp.isArrow)
    (fun comp => do throwErrorAt (← comp.stx) "Invalid type: functions must have arrow type")

/-- Assembles all declared `relation` predicates into a single `State` type. -/
def assembleState (name : Name) : CommandElabM Unit := do
  let vd := (<- getScope).varDecls
  Command.runTermElabM fun vs => do
  -- set the name
    let components ← liftCommandElabM $ liftCoreM $ ((<- localSpecCtx.get).spec.signature).mapM StateComponent.getSimpleBinder
    -- record the state name
    localSpecCtx.modify (fun s => { s with stateBaseName := name })
    let stName ← getPrefixedName `State
    let sdef ← `(@[stateDef] structure $(mkIdent stName) $(getStateParametersBinders vd)* where $(mkIdent `mk):ident :: $[$components]* deriving $(mkIdent ``Nonempty))
    let injEqLemma := (mkIdent $ stName ++ `mk ++ `injEq)
    let smtAttr ← `(attribute [smtSimp] $injEqLemma)
    trace[dsl.debug] "{sdef}"
    -- `@[stateDef]` sets `spec.stateType` (the base constant `stName`)
    liftCommandElabM $ elabCommand $ sdef
    -- we set `stateStx` ourselves
    let stateTp ← mkStateTpStx vd vs
    localSpecCtx.modify ({· with spec.stateStx := stateTp})
    -- Tag the `injEq` lemma as `smtSimp`
    liftCommandElabM $ elabCommand $ smtAttr

/-! ### Syntax -/

declare_syntax_cat state_mutability
syntax (name := immutable) "immutable" : state_mutability
syntax (name := mutable) "mutable" : state_mutability

/-- Fields are `mutable` by default. -/
private def stxToMut (m : Option (TSyntax `state_mutability)) : Mutability :=
  if let some stx := m then
    match stx with
    | `(state_mutability|immutable) => Mutability.immutable
    | `(state_mutability|mutable) => Mutability.mutable
    | _ => unreachable!
  else
    Mutability.mutable

/-- Declare an `individual` state component. -/
elab m:(state_mutability)? "individual" sig:Command.structSimpleBinder : command => do
  let comp := StateComponent.mk (stxToMut m) .individual (← liftCoreM $ getSimpleBinderName sig) (.simple sig)
  defineStateComponent comp
    (fun (tp : Expr) => return !tp.isArrow)
    (fun comp => do throwErrorAt (← comp.stx) "Invalid type: constants must not be arrow types")

/-- Declare a relation, giving only the type, e.g.
  ```lean
  relation R : address → round → Prop
  ```
-/
elab m:(state_mutability)? "relation" sig:Command.structSimpleBinder : command => do
  let rel := StateComponent.mk (stxToMut m) .relation (← liftCoreM $ getSimpleBinderName sig) (.simple sig)
  defineRelation rel

/-- Declare a relation, giving names to the arguments, e.g.:
  ```lean
  relation sent (n : address) (r : round)
  ```
-/
elab m:(state_mutability)? "relation" nm:ident br:(bracketedBinder)* (":" "Prop")? : command => do
  let rel := StateComponent.mk (stxToMut m) .relation nm.getId (.complex br (← `(Prop)))
  defineRelation rel

/-- `function` command saves a State structure field declaration -/
elab m:(state_mutability)? "function" sig:Command.structSimpleBinder : command => do
  let func := StateComponent.mk (stxToMut m) .function (← liftCoreM $ getSimpleBinderName sig) (.simple sig)
  defineFunction func

/-- Declare a function, giving names to the arguments. Example:
  ```lean
  function currentRound (n : address) : round
  ```
-/
elab m:(state_mutability)? "function" nm:ident br:(bracketedBinder)* ":" dom:term: command => do
  let func := StateComponent.mk (stxToMut m) .relation nm.getId (.complex br dom)
  defineFunction func

/-- Declare a ghost relation, i.e. a predicate over state. Example:
  ```lean
  relation R (r : round) (v : value) := [definition]
  ```
-/
elab "ghost" "relation" nm:ident br:(bracketedBinder)* ":=" t:term : command => do
  liftCoreM errorIfStateNotDefined
  let vd := (<- getScope).varDecls
  -- As we are going to call this predicate explicitly we want to make all
  -- section binders implicit
  let vd' <- vd.mapM (fun x => mkImplicitBinders x)
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- getStateTpStx
    let stx' <- funcasesM t vs
    elabBindersAndCapitals br vs stx' fun _ e => do
      let e <- delabWithMotives e
      `(@[actSimp, invSimp] abbrev $nm $[$vd']* $br* ($(mkIdent `st) : $stateTp := by exact_state) : Prop := $e)

@[inherit_doc assembleState]
elab "#gen_state" name:ident : command => assembleState name.getId

/-! ## Initializers -/

/-- Declare the initial state predicate. -/
elab "initial" ini:term : command => do
  liftCoreM errorIfStateNotDefined
  let vd ← getAssertionParameters
  elabCommand <| <- Command.runTermElabM fun _ => do
    -- let stateTp ← getStateTpStx
    -- let expectedType ← `($stateTp → Prop)
    let ini ←  simplifyTerm ini
    let predName ← getPrefixedName `initialState?
    -- because of `initDef`, this sets `stsExt.init` with `lang := none`
    `(@[initDef, initSimp] def $(mkIdent predName) $[$vd]* := $ini)

/-- Declare the initial state predicate as an imperative program in
`ActionLang`. -/
elab "after_init" "{" l:doSeqVeil "}" : command => do
    liftCoreM errorIfStateNotDefined
    let (ret, st, st', st_curr, post) := (mkIdent `ret, mkIdent `st, mkIdent `st', mkIdent `st_curr, mkIdent `post)
    let vd ← getAssertionParameters
    -- define initial state action (`Wlp`)
    let act ← Command.runTermElabM fun _ => (do
      let stateTp ← getStateTpStx
      `(fun ($st : $stateTp) ($post : sprop $stateTp) => (do' $l) $st (fun $ret ($st_curr : $stateTp) => $post $st_curr)))
    elabCommand $ ← Command.runTermElabM fun _ => do
      let actName ← getPrefixedName `init
      `(@[initSimp, actSimp] def $(mkIdent actName) $[$vd]* := $act)
    -- define initial state predicate
    let pred ← Command.runTermElabM fun _ => (do
      let stateTp ← getStateTpStx
      `(fun ($st' : $stateTp) => ∃ ($(toBinderIdent st) : $stateTp), Wlp.toActProp (do' $l) $st $st'))
    -- this sets `stsExt.init` with `lang := none`
    elabCommand $ ← `(initial $pred)
    -- we modify it to store the `lang`
    liftTermElabM do localSpecCtx.modify (fun s => { s with spec := {s.spec with init := {s.spec.init with lang := .some l}}})
    let sp ← liftTermElabM $ return (← localSpecCtx.get).spec.init
    trace[dsl.debug] s!"{sp}"

/-! ## Actions -/

declare_syntax_cat actionType
syntax (name := inputAction) "input" : actionType
syntax (name := internalAction) "internal" : actionType
syntax (name := outputAction) "output" : actionType

def toActionType (stx : TSyntax `actionType) : IOAutomata.ActionType :=
  match stx with
  | `(actionType|input) => IOAutomata.ActionType.input
  | `(actionType|internal) => IOAutomata.ActionType.internal
  | `(actionType|output) => IOAutomata.ActionType.output
  | _ => unreachable!

def toActionTypeIdent (stx : TSyntax `actionType) : Ident :=
  mkIdent $ match stx with
  | `(actionType|input) => ``IOAutomata.ActionType.input
  | `(actionType|internal) => ``IOAutomata.ActionType.internal
  | `(actionType|output) => ``IOAutomata.ActionType.output
  | _ => unreachable!

/-- `action foo` means `internal action foo` -/
def parseActionTypeStx (stx : Option (TSyntax `actionType)) : CommandElabM (TSyntax `actionType) := do
  return stx.getD $ ← `(actionType|internal)

open Command Term in
/-- Record the action type and signature of this action in the `localSpecificationCtx`.  -/
def registerIOActionDecl (actT : TSyntax `actionType) (nm : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)): CommandElabM Unit := do
  Command.runTermElabM fun _ => do
    let name := nm.getId
    let labelTypeName := mkIdent $ ← getPrefixedName `Label
    let br ← match br with
    | some br => toBracketedBinderArray br
    | none => pure $ TSyntaxArray.mk #[]
    let ctor ← `(ctor| | $nm:ident $br* : $labelTypeName)
    let actdecl : IOAutomata.ActionDeclaration := {
      type := toActionType actT,
      name := name,
      ctor := ctor
    }
    /- Find the appropriate transition and add the `ActionDeclaration`
    to it Note that this DOES NOT add the `lang` representing the DSL
    code We do that by a further modification in the relevant elaborator
    (see [add_action_lang]) -/
    localSpecCtx.modify (fun s => { s with spec := {s.spec with
      actions := s.spec.actions.map (fun t => if t.name == name then { t with decl := actdecl } else t) }})

/-- Defines `act` : `Wlp σ ρ` monad computation, parametrised over `br`. -/
def elabCallableFn (actT : TSyntax `actionType) (nm : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (l : TSyntax `doSeqVeil) : CommandElabM Unit := do
    let tr <- `(do' $l)
    let vd ← getImplicitActionParameters
    let (unsimplifiedDef, fnDef, trDef) ← Command.runTermElabM fun vs => do
      -- Create binders and arguments
      let sectionArgs ← getSectionArgumentsStx vs
      let (univBinders, args) ← match br with
      | some br => pure (← toBracketedBinderArray br, ← existentialIdents br)
      | none => pure (#[], #[])
      -- Create types
      -- The actual command (not term) elaboration happens here
      let (uName, fnName, trName) := (toUnsimplifiedIdent nm, nm, toTrIdent nm)
      let unsimplifiedDef ← `(@[actSimp] def $uName $[$vd]* $univBinders* := $(← unfoldWlp tr))
      trace[dsl.debug] "{unsimplifiedDef}"
      let attr ← toActionAttribute (toActionType actT)
      let fnDef ← `(@[$attr, actSimp] def $fnName $[$vd]* $univBinders* := $(← simplifyTerm $ ← `(@$uName $sectionArgs* $args*)))
      trace[dsl.debug] "{fnDef}"
      -- version with `forall` quantified arguments
      let trDef ← do
        let (st, st') := (mkIdent `st, mkIdent `st')
        let stateTpT ← getStateTpStx
        let rhs ← match br with
        | some br => `(fun ($st $st' : $stateTpT) => ∃ $br, Wlp.toActProp (@$fnName $sectionArgs* $args*) $st $st')
        | none => `(fun ($st $st' : $stateTpT) => Wlp.toActProp (@$fnName $sectionArgs* $args*) $st $st')
        `(@[actSimp] def $trName $[$vd]*  := $(← simplifyTerm rhs))
      trace[dsl.debug] "{tr}"
      return (unsimplifiedDef, fnDef, trDef)
    -- Declare `nm.unsimplified` and `nm`
    elabCommand unsimplifiedDef
    elabCommand fnDef
    elabCommand trDef

/-- Transition defined via a two-state relation. -/
syntax (actionType)? "transition" ident (explicitBinders)? "=" term : command

/-- Transition defined as an imperative program in `ActionLang`. We call
these "actions". All capital letters in `require` and in assignments are
implicitly quantified. -/
syntax (actionType)? "action" ident (explicitBinders)? "=" "{" doSeqVeil "}" : command

/-- Show a warning if the given declaration -/
def warnIfNotFirstOrder (name : Name) : MetaM Unit := do
  let .some decl := (← getEnv).find? name | throwError s!"{name} not found"
  let .some val := decl.value? | throwError s!"{name} has no value"
  let hasExists ← hasStateHOExist val
  let hasInnerForall ← hasStateHOInnerForall val
  let reason ← match hasExists, hasInnerForall with
  | true, false => pure $ some s!"it existentially quantifies over {← getStateName}"
  | false, true =>  pure $ some s!"it has non top-level ∀ quantification over the {← getStateName} type"
  | true, true => pure $ some s!"it has both existential and non top-level ∀ quantification over the {← getStateName} type"
  | _, _ => pure none
  if reason.isSome then
    logWarning s!"{name} is not first-order (and cannot be sent to SMT): {reason.get!}"

macro "exists?" br:explicitBinders ? "," t:term : term =>
  match br with
  | some br => `(exists $br, $t)
  | none => `($t)

syntax (actionType)? "action" ident (explicitBinders)? "=" doSeqVeil "{" doSeqVeil "}" : command
-- syntax (actionType)? "action" ident (explicitBinders)? "=" "{" doSeqVeil "}" : command

def checkSpec (nm : Ident) (br : Option (TSyntax `Lean.explicitBinders))
  (pre post : Term) (ret : TSyntax `rcasesPat) : CommandElabM Unit := do
  try
    elabCommand $ ← Command.runTermElabM fun vs => do
      let st := mkIdent `st
      let thmName := mkIdent $ nm.getId ++ `spec_correct
      let br' <- (toBracketedBinderArray <$> br) |>.getD (pure #[])
      let br <- (existentialIdents <$> br) |>.getD (pure #[])
      let stx <- `(theorem $thmName $br' * : ∀ $st:ident,
          (fun s => funcases s $pre) $st ->
          @$nm $(← getSectionArgumentsStx vs)* $br* $st (by rintro $ret; exact (funcases $post)) := by
          intro
          solve_clause)
      trace[dsl.debug] "{stx}"
      return stx
  catch e =>
    throwError s!"Error while checking the specification of {nm}:" ++ e.toMessageData


def elabAction (actT : Option (TSyntax `actionType)) (nm : Ident) (br : Option (TSyntax ``Lean.explicitBinders))
  (spec : Option (TSyntax `doSeqVeil)) (l : TSyntax `doSeqVeil) : CommandElabM Unit := do
    liftCoreM errorIfStateNotDefined
    let actT ← parseActionTypeStx actT
    -- Elab the action
    elabCallableFn actT nm br l
    -- warn if this is not first-order
    Command.liftTermElabM $ warnIfNotFirstOrder nm.getId
    -- add constructor for label type
    registerIOActionDecl actT nm br
    Command.runTermElabM fun _ => do
      -- [add_action_lang] find the appropriate transition and add the `lang` declaration to it
      localSpecCtx.modify fun s => { s with spec := { s.spec with
        actions := s.spec.actions.map fun t =>
          if t.name == nm.getId then
            { t with lang := l, hasSpec := spec.isSome }
          else t }}
    unless spec.isNone do
      let (pre, binder, post) <- getPrePost spec.get!
      elabCallableFn actT (nm.getId ++ `spec |> mkIdent) br spec.get!
      checkSpec nm br pre post binder

/--
```lean
transition name binders* = tr
```
This command defines lifts a two-state formula into a `Wlp σ Unit`
-/
elab_rules : command
  | `(command|$actT:actionType transition $nm:ident $br:explicitBinders ? = $tr) => do
  elabAction actT nm br none (<- `(doSeqVeil| ($tr).toWlp))


elab_rules : command
  | `(command|$actT:actionType ? action $nm:ident $br:explicitBinders ? = {$l:doSeqVeil}) =>
  elabAction actT nm br none l
  | `(command|$actT:actionType ? action $nm:ident $br:explicitBinders ? = $spec:doSeqVeil {$l:doSeqVeil}) =>
  elabAction actT nm br spec l

/-! ## Assertions -/

declare_syntax_cat propertyName
syntax "[" ident "]": propertyName

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
      | .assumption => pure $ Name.mkSimple s!"axiom_{(<- localSpecCtx.get).spec.assumptions.size}"
    let name := getPropertyNameD name defaultName
    let cmd ← elabBindersAndCapitals #[] vs stx fun _ e => do
      let e <- delabWithMotives e
      match kind with
      | .safety =>
        `(@[safeDef, safeSimp, invSimp] def $(mkIdent name) $[$vd]*: $stateTp -> Prop := fun $(mkIdent `st) => $e: term)
      | .invariant =>
        `(@[invDef, invSimp] def $(mkIdent name) $[$vd]* : $stateTp -> Prop := fun $(mkIdent `st) => $e: term)
      | .assumption =>
        `(@[assumptionDef, invSimp] def $(mkIdent name) $[$vd]* : $stateTp -> Prop := fun $(mkIdent `st) => $e: term)
    -- IMPORTANT: It is incorrect to do `liftCommandElabM $ elabCommand cmd` here
    -- (I think because of how `elabBindersAndCapitals` works)
    return (name, cmd)
  -- Do the elaboration to populate the `stsExt` state
  trace[dsl.debug] s!"{cmd}"
  elabCommand cmd
  Command.runTermElabM fun _vs => do
    -- Record the term syntax in the `stsExt` state
    localSpecCtx.modify (fun s => { s with spec :=
    (match kind with
    | .safety | .invariant => {s.spec with
        invariants := s.spec.invariants.map (fun x => if x.name == name then { x with term := t } else x) }
    | .assumption => {s.spec with
        assumptions := s.spec.assumptions.map (fun x => if x.name == name then { x with term := t } else x) })})


/-- Axiom. All state components referred to must be `immutable`. All
capital variables are implicitly quantified. -/
elab "assumption" name:(propertyName)? prop:term : command => defineAssertion (kind := .assumption) name prop

/-- Safety property. All capital variables are implicitly quantified -/
elab "safety" name:(propertyName)? safe:term : command => defineAssertion (kind := .safety) name safe

/-- Invariant of the transition system. All capital variables are implicitly quantified -/
elab "invariant" name:(propertyName)? inv:term : command => defineAssertion (kind := .invariant) name inv


/-! ## Specification Generation -/

/-- Generates a repeated-`op` of all expressions in `exps`, each applied
to `vs`. For instance, when called with `Or` and the list of actions,
this gives us the `Next` transition.-/
def combineLemmas (op : Name) (exps: List Expr) (vs : Array Expr) (name : String) : MetaM Expr := do
    let exp0 :: exprs := exps
      | throwError ("There are no " ++ name ++ " defined")
    let exp0 <- etaExpand exp0
    let exps <- lambdaTelescope exp0 fun args exp0 => do
      let mut exps := exp0
      for exp in exprs do
        let exp := mkAppN exp args
        exps <- mkAppM op #[exp, exps]
      mkLambdaFVars args exps
    instantiateLambda exps vs

/--Assembles all declared transitions into a `Next` transition relation. -/
def assembleNext : CommandElabM Unit := do
  let vd ← getActionParameters
  elabCommand $ ← Command.runTermElabM fun vs => do
    let stateTp ← getStateTpStx
    let sectionArgs ← getSectionArgumentsStx vs
    let (st, st') := (mkIdent `st, mkIdent `st')
    let trs ← (<- localSpecCtx.get).spec.actions.mapM (fun s => do
      let nm := mkIdent $ toTrName s.name
      `(@$nm $sectionArgs* $st $st'))
    -- let _ ← (← localSpecCtx.get).spec.actions.mapM (fun t => do trace[dsl.debug] s!"{t}")
    let next ← if trs.isEmpty then `(fun ($st $st' : $stateTp) => $st = $st') else
              `(fun ($st $st' : $stateTp) => $(← repeatedOr trs))
    trace[dsl.debug] "[assembleActions] {next}"
    `(@[actSimp] def $(mkIdent $ ← getPrefixedName `Next) $[$vd]* := $next)

def assembleLabelType (name : Name) : CommandElabM Unit := do
  elabCommand $ ← Command.runTermElabM fun _ => do
    let labelTypeName := mkIdent $ ← getPrefixedName `Label
    let ctors ← (<- localSpecCtx.get).spec.actions.mapM (fun s => do match s.decl.ctor with
      | none => throwError "DSL: missing label constructor for action {s.name}"
      | some ctor => pure ctor)
    trace[dsl] "storing constructors for {name}"
    `(inductive $labelTypeName where $[$ctors]*)

/-- Assembles the IOAutomata `ActionMap` for this specification. This is
a bit strange, since it constructs a term (syntax) to build a value. -/
def assembleActionMap : CommandElabM Unit := do
  elabCommand $ ← Command.runTermElabM fun vs => do
    let ioStx ← (← localSpecCtx.get).spec.actions.mapM fun decl => do
      let ioActName := toIOActionDeclName decl.label.name
      let act ← PrettyPrinter.delab $ ← mkAppOptM ioActName (vs.map Option.some)
      `(($(quote decl.label.name), $act))
    let actMapStx ← `(IOAutomata.ActionMap.ofList [$[$ioStx],*])
    let actMapStx ← `(def $(mkIdent $ ← getPrefixedName `actionMap) := $actMapStx)
    trace[dsl] "{actMapStx}"
    return actMapStx

/-- Assembles all declared invariants (including safety properties) into
a single `Invariant` predicate -/
def assembleInvariant : CommandElabM Unit := do
  let vd ← getAssertionParameters
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- getStateTpStx
    let allClauses := (<- localSpecCtx.get).spec.invariants
    let exprs := allClauses.toList.map (fun p => p.expr)
    let _ ← allClauses.mapM (fun t => do trace[dsl.debug] s!"{t}")
    let invs ← if allClauses.isEmpty then `(fun _ => True) else PrettyPrinter.delab $ ← combineLemmas ``And exprs vs "invariants"
    `(@[invSimp] def $(mkIdent $ ← getPrefixedName `Invariant) $[$vd]* : $stateTp -> Prop := $invs)

/-- Assembles all declared safety properties into a single `Safety`
predicate -/
def assembleSafeties : CommandElabM Unit := do
  let vd ← getAssertionParameters
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- getStateTpStx
    let exprs := (<- localSpecCtx.get).spec.invariants.toList.filterMap (fun p => if p.kind == .safety then p.expr else none)
    let safeties ← if exprs.isEmpty then `(fun _ => True) else PrettyPrinter.delab $ ← combineLemmas ``And exprs vs "invariants"
    `(@[invSimp] def $(mkIdent $ ← getPrefixedName `Safety) $[$vd]* : $stateTp -> Prop := $safeties)

/-- Assembles all declared `assumption`s into a single `Assumptions`
predicate -/
def assembleAssumptions : CommandElabM Unit := do
  let vd ← getAssertionParameters
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- getStateTpStx
    let exprs := (<- localSpecCtx.get).spec.assumptions.toList.map (fun p => p.expr)
    let assumptions ← if exprs.isEmpty then `(fun _ => True) else PrettyPrinter.delab $ ← combineLemmas ``And exprs vs "assumptions"
    `(@[invSimp] def $(mkIdent $ ← getPrefixedName `Assumptions) $[$vd]* : $stateTp -> Prop := $assumptions)

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
  Command.runTermElabM fun vs => do
    let stateTpStx <- getStateTpStx
    let initSt    := mkAppN (<- mkConst $ ← getPrefixedName `initialState?) vs
    let initStx    <- PrettyPrinter.delab initSt
    let nextTrans := mkAppN (<- mkConst $ ← getPrefixedName `Next) vs
    let nextTransStx <- PrettyPrinter.delab nextTrans
    let safe      := mkAppN (<- mkConst $ ← getPrefixedName `Safety) vs
    let safeStx      <- PrettyPrinter.delab safe
    let inv       := mkAppN (<- mkConst $ ← getPrefixedName `Invariant) vs
    let invStx       <- PrettyPrinter.delab inv
    let axioms    := mkAppN (<- mkConst $ ← getPrefixedName `Assumptions) vs
    let axiomsStx    <- PrettyPrinter.delab axioms
    let rtsStx       <-
      `(instance (priority := low) $(mkIdent name) $[$vd]* : $(mkIdent ``RelationalTransitionSystem) $stateTpStx where
          init := $initStx
          assumptions := $axiomsStx
          next := $nextTransStx
          safe := $safeStx
          inv  := $invStx
          )
    trace[dsl] "{rtsStx}"
    liftCommandElabM $ elabCommand $ rtsStx

@[inherit_doc instantiateSystem]
elab "#gen_spec" name:ident : command => do
  liftCoreM errorIfStateNotDefined
  instantiateSystem name.getId
  Command.runTermElabM fun _ => do
    -- set the name of the spec
    localSpecCtx.modify (fun s => { s with spec := {s.spec with name := name.getId }})
    -- globally register the spec, so it can be composed with other modules
    registerModuleSpecification (← localSpecCtx.get).spec

/-! ## Section Variables -/

/- FIXME: This is a bit stupid, but we place these here so they don't
interfere with the definitions above. For instance, we need to define a
`structure` with a field named `type` and that gets broken.
Unfortunately, this means we're breaking all the DSL clients. -/
macro "type" id:ident : command => do
  let dec_id := Lean.mkIdent (Name.mkSimple s!"{id.getId}_dec")
  let ne_id := Lean.mkIdent (Name.mkSimple s!"{id.getId}_ne")
  `(variable ($id : Type) [$dec_id : DecidableEq $id] [$ne_id : Nonempty $id])
-- macro "instantiate" t:term : command => `(variable [$t])
macro "instantiate" nm:ident " : " t:term : command => `(variable [$nm : $t])
