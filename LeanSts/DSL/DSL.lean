import Lean
import Lean.Parser
import Lean.Meta.Tactic.TryThis

import LeanSts.TransitionSystem
import LeanSts.IOAutomata
import LeanSts.Tactic
import LeanSts.DSL.Util
import LeanSts.DSL.Lang
import LeanSts.DSL.Tactic
import LeanSts.DSL.Trace
import LeanSts.SMT.Preparation

open Lean Elab Command Term Meta Lean.Parser Tactic.TryThis RelationalTransitionSystem

-- Modelled after the Ivy language
-- https://github.com/kenmcmil/ivy/blob/master/doc/language.md

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

/-- Defines a constant, relation, or function, validating its type before adding it. -/
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
    liftTermElabM do stsExt.modify (fun s => { s with sig := s.sig.push comp })
  else
    liftCoreM $ failureMsg comp

def defineRelation (comp : StateComponent) : CommandElabM Unit :=
  defineStateComponent comp
     (fun (tp : Expr) => do
      let returnsProp ← liftTermElabM $ forallTelescope tp (fun _ b => do return b.isProp)
      return tp.isArrow && returnsProp)
    (fun comp => do throwErrorAt (← comp.stx) "Invalid type: relations must return Prop")

/-- Declare a relation, giving only the type. Example:
  ```lean
  relation R : address → round → Prop
  ```
-/
elab "relation" sig:Command.structSimpleBinder : command => do
  let rel := StateComponent.mk .relation (getSimpleBinderName sig) (.simple sig)
  defineRelation rel

/-- Declare a relation, giving names to the arguments. Example:
  ```lean
  relation sent (n : address) (r : round)
  ```
-/
elab "relation" nm:ident br:(bracketedBinder)* (":" "Prop")? : command => do
  let rel := StateComponent.mk .relation nm.getId (.complex br (← `(Prop)))
  defineRelation rel

/-- `individual` command saves a State structure field declaration -/
elab "individual" sig:Command.structSimpleBinder : command => do
  let comp := StateComponent.mk .individual (getSimpleBinderName sig) (.simple sig)
  defineStateComponent comp
    (fun (tp : Expr) => return !tp.isArrow)
    (fun comp => do throwErrorAt (← comp.stx) "Invalid type: constants must not be arrow types")

def defineFunction (comp : StateComponent) : CommandElabM Unit :=
  defineStateComponent comp
    (fun (tp : Expr) => do return tp.isArrow)
    (fun comp => do throwErrorAt (← comp.stx) "Invalid type: functions must have arrow type")

/-- `function` command saves a State structure field declaration -/
elab "function" sig:Command.structSimpleBinder : command => do
  let func := StateComponent.mk .function (getSimpleBinderName sig) (.simple sig)
  defineFunction func

/-- Declare a function, giving names to the arguments. Example:
  ```lean
  function currentRound (n : address) : round
  ```
-/
elab "function" nm:ident br:(bracketedBinder)* ":" dom:term: command => do
  let func := StateComponent.mk .relation nm.getId (.complex br dom)
  defineFunction func

/-- Declare a ghost relation, i.e. a predicate over state. Example:
  ```lean
  relation R : <Type> := [definition]
  ```
-/
elab "relation" nm:ident br:(bracketedBinder)* ":=" t:term : command => do
  let vd := (<- getScope).varDecls
  -- As we are going to call this predicate explicitly we want to make all
  -- section binders implicit
  let vd' <- vd.mapM (fun x => mkImplicitBinders x)
  elabCommand $ <-  Command.runTermElabM fun vs => do
    let stateTp <- stateTp vs
    let stateTp <- PrettyPrinter.delab stateTp
    let stx' <- funcasesM t vs
    elabBindersAndCapitals br vs stx' fun _ e => do
      let e <- my_delab e
      `(@[actSimp, invSimp] abbrev $nm $[$vd']* $br* ($(mkIdent `st) : $stateTp := by exact_state) : Prop := $e)

/--
assembles all declared `relation` predicates into a single State -/
def assembleState (name : Name) : CommandElabM Unit := do
  let vd := (<- getScope).varDecls
  Command.runTermElabM fun vs => do
  -- set the name
    let components ← liftCommandElabM $ liftCoreM $ ((<- stsExt.get).sig).mapM StateComponent.getSimpleBinder
    -- record the state name
    stsExt.modify (fun s => { s with stateBaseName := name })
    let stName ← getPrefixedName `State
    let sdef ← `(@[stateDef] structure $(mkIdent stName) $[$vd]* where $(mkIdent `mk):ident :: $[$components]*)
    let injEqLemma := (mkIdent $ stName ++ `mk ++ `injEq)
    let smtAttr ← `(attribute [smtSimp] $injEqLemma)
    liftCommandElabM $ elabCommand $ sdef
    liftCommandElabM $ elabCommand $ smtAttr

@[inherit_doc assembleState]
elab "#gen_state" name:ident : command => assembleState name.getId

open Tactic in
elab tk:"conv! " conv:conv " => " e:term : term => do
  let e ← Elab.Term.elabTermAndSynthesize e none
  let (rhs, g) ← Conv.mkConvGoalFor e
  _ ← Tactic.run g.mvarId! (do
    evalTactic conv
    for mvarId in (← getGoals) do
      liftM <| mvarId.refl <|> mvarId.inferInstance <|> pure ()
    pruneSolvedGoals
    let e' ← instantiateMVars rhs
    trace[dsl] "{e'}"
  )
  return rhs

/-- We use this to evaluate `wlp` inside function bodies at definition time.
  Otherwise it has to be evaluated in the kernel during proofs, which is very slow.
  `conv!` applies a tactic to a term. -/
def simplifyTerm (t : TSyntax `term) : TermElabM (TSyntax `term) := do
  let (actSimp, smtSimp) := (mkIdent `actSimp, mkIdent `smtSimp)
  -- Reduce the body of the function
  let t' ← `(term| by
    -- Try simplifying first, but this might fail if there's no `wlp` in the
    -- definition, e.g. for transitions that are not actions.
    -- If that fails, we try to evaluate the term as is.
    -- We do `simp only [and_assoc]` at the end to normalize conjunctions.
    first | (let t := conv! (dsimp only [$actSimp:ident]; simp only [$smtSimp:ident]; simp only [and_assoc]; repeat (pushEqLeft; simp only [quantifierElim])) => $t; exact t) | exact $t)
  return t'

/-- Declaring the initial state predicate -/
elab "initial" ini:term : command => do
  elabCommand <| <- Command.runTermElabM fun vs => do
    let stateTp ← PrettyPrinter.delab $ ← stateTp vs
    let expectedType ← `($stateTp → Prop)
    let ini ←  simplifyTerm ini
    let name ← getPrefixedName `initialState?
    `(@[initDef, initSimp] def $(mkIdent name) : $expectedType := $ini)

/-- Declaring the initial state predicate in the form of a code -/
elab "after_init" "{" l:lang "}" : command => do
   -- Here we want to compute `WP[l]{st, st' = st} : State -> Prop`
   -- where `st'` is a final state. We expand `l` using `[lang1| l]`
   -- where `lang1` syntax will make sure that `WP` doesn't depend
   -- on the prestate state. As  `WP[l]{st, st' = st} : State -> Prop`
   -- doesn't depend on a prestate we can reduce it into `fun _ => Ini(st')`
   -- To get `Ini(st')` we should apply `fun _ => Ini(st')`  to any
   -- state, so we use `st'` as it is the only state we have in the context.
    let (ret, st, st', wlp) := (mkIdent `ret, mkIdent `st, mkIdent `st', mkIdent ``wlp)
    let act ← Command.runTermElabM fun vs => (do
      let stateTp ← PrettyPrinter.delab $ ← stateTp vs
      `(fun ($st' : $stateTp) => @$wlp _ _ (fun $ret $st => $st' = $st) [lang1| $l ] $st')
    )
    elabCommand $ ← `(initial $act)

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

open Command in
def addIOActionDecl (actT : TSyntax `actionType) (nm : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)): CommandElabM Unit := do
  Command.runTermElabM fun vs => do
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
    -- Find the appropriate transition and add the ActionDecl to it
    stsExt.modify (fun s => { s with
      transitions := s.transitions.map (fun ((label, decl), act) => if label.name == name && decl.isNone then ((label, actdecl), act) else ((label, decl), act)) })

/-- `action foo` means `internal action foo` -/
def parseActionTypeStx (stx : Option (TSyntax `actionType)) : CommandElabM (TSyntax `actionType) := do
  return stx.getD $ ← `(actionType|internal)

/--
Transition defined via a two-state relation.
-/
syntax (actionType)? "transition" ident (explicitBinders)? "=" term : command

/--
Transition defined as an imperative program. We call these "actions".
All capital letters in `require` and in assignments are implicitly quantified.
-/
syntax (actionType)? "action" ident (explicitBinders)? "=" "{" lang "}" : command


def getSectionArgumentsStx (vs : Array Expr) : TermElabM (Array (TSyntax `term)) := do
  let args ← vs.mapM (fun v => do
    let t ← PrettyPrinter.delab v
    let isHygienicName := (extractMacroScopes t.raw.getId).scopes.length > 0
    if isHygienicName then return ← `(term|_) else return t
  )
  return args

/-- `act.fn` : a function that returns a transition relation with return
  value (type `σ → (σ × ρ) → Prop`), universally quantified over `binders`. -/
def elabCallableFn (nm : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (l : TSyntax `lang) : CommandElabM Unit := do
  let (originalName, nm) := (nm, toFnIdent nm)
  elabCommand $ ← Command.runTermElabM fun vs => do
    let (ret, st, stret, wlp) := (mkIdent `ret', mkIdent `st, mkIdent `stret, mkIdent ``wlp)
    let stateTp ← PrettyPrinter.delab $ ← stateTp vs
    -- `σ → (σ × ρ) → Prop`, with binders universally quantified
    -- $stret = ($st', $ret')
    let act <- `(fun ($st : $stateTp) $stret =>
      @$wlp _ _ (fun $ret ($st : $stateTp) => (Prod.fst $stret) = $st ∧ $ret = (Prod.snd $stret)) [lang| $l ] $st)
    -- let tp ← `(term|$stateTp -> ($stateTp × $retTp) -> Prop)
    let (st, st') := (mkIdent `st, mkIdent `st')
    match br with
    | some br =>
      let br ← toBracketedBinderArray br
      -- $(← simplifyTerm $ ← `(fun $st $st' => exists $br, $tr $st $st'))
      `(@[actSimp] def $nm $br* := $(← simplifyTerm $ ← `(fun $st $st' => $act $st $st')))
    | _ => do
      `(@[actSimp] def $nm:ident := $(← simplifyTerm act))
  -- Introduce notation to automatically provide the section arguments
  elabCommand $ ← Command.runTermElabM fun vs => do
    let args ← getSectionArgumentsStx vs
    let strName ← `(Lean.Parser.Command.notationItem|$(Lean.quote ("!" ++ originalName.getId.toString)):str)
    `(local notation (priority := default) $strName => @$nm $args*)

/--
Desugaring an imperative code action into a two-state transition. Here we compute
the weakest precondition of the program and then define the transition relation.

Note: Unlike `after_init` we expand `l` using `[lang| l]` as we want the transition
to refer to both pre-state and post-state.
-/
-- elab_rules : command
-- | `(command|$actT:actionType  action $nm:ident $br:explicitBinders ? = { $l:lang }) => do
elab actT:(actionType)? "action" nm:ident br:(explicitBinders)? "=" "{" l:lang "}" : command => do
    let actT ← parseActionTypeStx actT
    let (ret, st, st', wlp) := (mkIdent `ret, mkIdent `st, mkIdent `st', mkIdent ``wlp)
    -- `σ → σ → Prop`, with binders existentially qunatified
    let tr ← Command.runTermElabM fun vs => (do
      let stateTp ← PrettyPrinter.delab $ ← stateTp vs
      `(fun ($st $st' : $stateTp) => @$wlp _ _ (fun $ret ($st : $stateTp) => $st' = $st) [lang| $l ] $st)
    )
    elabCommand $ ← `($actT:actionType transition $(toTrIdent nm) $br ? = $tr)
    elabCallableFn nm br l

/--
```lean
transition name binders* = tr
```
This command defines:
- `act.tr` : a transition relation `σ → σ → Prop`, existentially quantified over the `binders`.
- `act.tr.fn` : a function that returns the transition relation for given
  arguments. Unlike `act.fn` defined by `elabCallableFn`, this does not
  have a return value
-/
elab_rules : command
  | `(command|$actT:actionType transition $nm:ident $br:explicitBinders ? = $tr) => do
  -- Elab the transition
  let (trfn, tr) ← Command.runTermElabM fun vs => do
    let stateTp <- stateTp vs
    let (st, st') := (mkIdent `st, mkIdent `st')
    let expectedType ← mkArrow stateTp (← mkArrow stateTp prop)
    let stateTpT <- PrettyPrinter.delab stateTp
    -- IMPORTANT: we elaborate the term here so we get an error if it doesn't type check
    match br with
    | some br =>
      let _ <- elabTerm (<-`(term| fun ($st $st' : $stateTpT) => exists $br, $tr $st $st')) expectedType
    | none =>
      let _ <- elabTerm tr expectedType
    -- The actual command (not term) elaboration happens here
    let expectedType <- `($stateTpT -> $stateTpT -> Prop)
    let attr ← toActionAttribute (toActionType actT)
    let trfnName := toFnIdent nm
    let (trfn, simplifiedTr) ← match br with
    | some br =>
      pure (← `(@[actSimp] def $trfnName $(← toBracketedBinderArray br)* := $(← simplifyTerm $ ← `(fun ($st $st' : $stateTpT) => $tr $st $st'))), ← `(term|True))
    | _ => do
      let simplifiedTr ← simplifyTerm tr
      pure (← `(@[actSimp] def $trfnName : $expectedType := $simplifiedTr), simplifiedTr)
    let tr ← match br with
    | some br =>
      -- TODO: add macro for a beta reduction here
      `(@[$attr, actSimp] def $nm : $expectedType := $(← simplifyTerm $ ← `(fun ($st $st' : $stateTpT) => exists $br, @$trfnName $(← getSectionArgumentsStx vs)* $(← existentialIdents br)* $st $st')))
    | _ => do
      `(@[$attr, actSimp] def $nm:ident : $expectedType := $simplifiedTr)
    return (trfn, tr)
  -- Declare `.tr.fn` and `.tr`
  elabCommand trfn
  elabCommand tr
  -- Declare the transition as an IO action `.iodecl`
  addIOActionDecl actT nm br

/-- Safety property. All capital variables are implicitly quantified -/
elab "safety" name:(propertyName)? safe:term : command => do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- stateTp vs
    -- let safe <- liftMacroM $ closeCapitals safe
    let stateTp <- PrettyPrinter.delab stateTp
    let stx <- funcasesM safe vs
    let defaultName := Name.mkSimple $ s!"safety_{(<- stsExt.get).safeties.length}"
    let name := getPropertyNameD name defaultName
    elabBindersAndCapitals #[] vs stx fun _ e => do
      let e <- my_delab e
      `(@[safeDef, safeSimp, invSimp] def $(mkIdent name) : $stateTp -> Prop := fun $(mkIdent `st) => $e: term)

/-- Invariant of the transition system.
    All capital variables are implicitly quantified -/
elab "invariant" name:(propertyName)? inv:term : command => do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- stateTp vs
    -- let inv <- liftMacroM $ closeCapitals inv
    let stx <- funcasesM inv vs
    let _ <- elabByTactic stx (<- mkArrow stateTp prop)
    let stateTp <- PrettyPrinter.delab stateTp
    let defaultName := Name.mkSimple $ s!"inv_{(<- stsExt.get).invariants.length}"
    let name := getPropertyNameD name defaultName
    elabBindersAndCapitals #[] vs stx fun _ e => do
      let e <- my_delab e
      `(@[invDef, invSimp] def $(mkIdent name) : $stateTp -> Prop := fun $(mkIdent `st) => $e: term)

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

/--
Assembles all declared actions into a `Next` transition relation.
-/
def assembleActions : CommandElabM Unit := do
  elabCommand $ ← Command.runTermElabM fun vs => do
    let stateTp <- PrettyPrinter.delab (<- stateTp vs)
    let acts := (<- stsExt.get).transitions.map Prod.snd
    let next <- combineLemmas ``Or acts vs "transitions"
    let next <- PrettyPrinter.delab next
    `(@[actSimp] def $(mkIdent $ ← getPrefixedName `Next) : $stateTp -> $stateTp -> Prop := $next)


def assembleLabelType (name : Name) : CommandElabM Unit := do
  elabCommand $ ← Command.runTermElabM fun _ => do
    let labelTypeName := mkIdent $ ← getPrefixedName `Label
    let ctors ← (← stsExt.get).transitions.toArray.mapM fun ((label, actDecl), _) => do match actDecl with
      | none => throwError "DSL: missing IOAutomata.ActionDeclaration for action {label.name}"
      | some actDecl => pure actDecl.ctor
    trace[dsl] "storing constructors for {name}"
    stsStateGlobalExt.modify (fun s => s.insert name ctors)
    `(inductive $labelTypeName where $[$ctors]*)

def mergeLabelType (n m nm : Name) : CommandElabM Unit := do
  elabCommand $ ← Command.runTermElabM fun _ => do
    let stss <- stsStateGlobalExt.get
    trace[dsl] "{stss.toList}"
    let .some nctrs := stss.find? n | throwError "DSL: missing type {n}"
    let .some mctrs := stss.find? m | throwError "DSL: missing type {m}"
    let ctors := (nctrs ++ mctrs).toList.eraseDups.toArray
    `(inductive $(mkIdent nm) where $[$ctors]*)

elab "#merge_labels" n:ident m:ident "into" nm:ident : command => do
  mergeLabelType n.getId m.getId nm.getId

/-- Assembles the IOAutomata `ActionMap` for this specification. This is
a bit strange, since it constructs a term (syntax) to build a value. -/
def assembleActionMap : CommandElabM Unit := do
  elabCommand $ ← Command.runTermElabM fun vs => do
    let ioStx ← (← stsExt.get).transitions.toArray.mapM fun ((label, _actDecl), _act) => do
      let ioActName := toIOActionDeclName label.name
      let act ← PrettyPrinter.delab $ ← mkAppOptM ioActName (vs.map Option.some)
      `(($(quote label.name), $act))
    let actMapStx ← `(IOAutomata.ActionMap.ofList [$[$ioStx],*])
    let actMapStx ← `(def $(mkIdent $ ← getPrefixedName `actionMap) := $actMapStx)
    trace[dsl] "{actMapStx}"
    return actMapStx

/-- Assembles all declared invariants (including safety properties) into a single `Invariant` predicate -/
def assembleInvariant : CommandElabM Unit := do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- PrettyPrinter.delab (<- stateTp vs)
    let invs <- combineLemmas ``And ((<- stsExt.get).invariants ++ (<- stsExt.get).safeties) vs "invariants"
    let invs <- PrettyPrinter.delab invs
    `(@[invSimp] def $(mkIdent $ ← getPrefixedName `Invariant) : $stateTp -> Prop := $invs)

/-- Assembles all declared safety properties into a single `Safety` predicate -/
def assembleSafeties : CommandElabM Unit := do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- PrettyPrinter.delab (<- stateTp vs)
    let safeties <- combineLemmas ``And (<- stsExt.get).safeties vs "safeties"
    let safeties <- PrettyPrinter.delab safeties
    `(@[invSimp] def $(mkIdent $ ← getPrefixedName `Safety) : $stateTp -> Prop := $safeties)

/--
Instantiates the `RelationalTransitionSystem` type class with the declared actions, safety and invariant
-/
def instantiateSystem (name : Name) : CommandElabM Unit := do
  let vd := (<- getScope).varDecls
  assembleActions
  assembleInvariant
  assembleSafeties
  assembleLabelType name
  Command.runTermElabM fun vs => do
    -- set the name
    stsExt.modify (fun s => { s with specName := name })
    let stateTp   := mkAppN (<- stsExt.get).typ vs
    let stateTpStx   <- PrettyPrinter.delab stateTp
    let initSt    := mkAppN (<- mkConst $ ← getPrefixedName `initialState?) vs
    let initStx    <- PrettyPrinter.delab initSt
    let nextTrans := mkAppN (<- mkConst $ ← getPrefixedName `Next) vs
    let nextTransStx <- PrettyPrinter.delab nextTrans
    let safe      := mkAppN (<- mkConst $ ← getPrefixedName `Safety) vs
    let safeStx      <- PrettyPrinter.delab safe
    let inv       := mkAppN (<- mkConst $ ← getPrefixedName `Invariant) vs
    let invStx       <- PrettyPrinter.delab inv
    let rtsStx       <-
      `(instance (priority := low) $(mkIdent name) $[$vd]* : $(mkIdent ``RelationalTransitionSystem) $stateTpStx where
          init := $initStx
          next := $nextTransStx
          safe := $safeStx
          inv  := $invStx
          )
    trace[dsl] "{rtsStx}"
    liftCommandElabM $ elabCommand $ rtsStx
    -- let am ← mkAppOptM (← getPrefixedName `actionMap) (vs.map Option.some)
    -- let amStx ← PrettyPrinter.delab am
    -- let ioStx ← `(instance (priority := low) $(mkIdent $ name ++ `IO) $[$vd]* : $(mkIdent ``IOAutomaton) $stateTpStx $(mkIdent ``Name) where
    --   init := $initStx
    --   acts := $amStx
    -- )
    -- trace[dsl] "{ioStx}"
    -- liftCommandElabM $ elabCommand $ ioStx

def setOptionPrintModel : CommandElabM Unit := do
  elabCommand (← `(command|set_option $(mkIdent "trace.sauto.model".toName) true))

@[inherit_doc instantiateSystem]
elab "#gen_spec" name:ident : command => do
  instantiateSystem name.getId

def checkTheorem (theoremName : Name) (cmd : TSyntax `command): CommandElabM Bool := do
  withTraceNode `dsl.perf.checkInvariants (fun _ => return m!"elab {theoremName} definition") do
  let env ← getEnv
  -- FIXME: I think we want to run `elabCommand` without `withLogging`
  elabCommand cmd
  -- Check the `Expr` for the given theorem
  let th ← getConstInfo theoremName
  let isProven ← match th with
    | ConstantInfo.thmInfo attempt => pure <| !attempt.value.hasSyntheticSorry
    | _ => throwError s!"checkTheorem: expected {theoremName} to be a theorem"
  -- We only add the theorem to the environment if it successfully type-checks
  -- i.e. we restore the original environment if the theorem is not proven
  if !isProven then
    setEnv env
  return isProven

def getSystemTpStx (vs : Array Expr) : TermElabM Term := do
  let systemTp ← PrettyPrinter.delab $ mkAppN (mkConst (← stsExt.get).specName) vs
  return systemTp

def getStateTpStx (vs : Array Expr) : TermElabM Term := do
  let stateTp ← PrettyPrinter.delab (← stateTp vs)
  return stateTp

inductive CheckType
  | init
  | action (actName : Name)
deriving BEq

/-- `(invName, theoremName, checkTheorem, failedTheorem)` -/
abbrev SingleCheckT   := (Name × Name × TSyntax `command × TSyntax `command)
abbrev InitChecksT    := Array SingleCheckT
abbrev ActionChecksT  := InitChecksT
abbrev ActionsChecksT := Array (Name × ActionChecksT)

/-- Generate the check theorem for the given invariant an `CheckType` (either `init` or `action`) -/
def getCheckFor (invName : Name) (ct : CheckType) (vs : Array Expr) : TermElabM SingleCheckT := do
  let env ← getEnv
  let .some _ := env.find? invName
    | throwError s!"Invariant {invName} not found"
  let inv ← Term.mkConst invName

  let (systemTp, stateTp, st, st') := (← getSystemTpStx vs, ← getStateTpStx vs, mkIdent `st, mkIdent `st')
  let property ← PrettyPrinter.delab $ mkAppN inv vs

  let (tpStx, thName, proofScript) ← match ct with
  | .init => do
      let initTpStx ← `(∀ ($st : $stateTp), ($systemTp).$(mkIdent `init)  $st → $property $st)
      let initThmName := s!"init_{invName}".toName
      let proofScript ← `(by unhygienic intros; solve_clause [$(mkIdent `initSimp)])
      pure (initTpStx, initThmName, proofScript)
  | .action actName => do
      let .some _ := (← getEnv).find? actName
        | throwError s!"action {actName} not found"
      let act ← Term.mkConst actName
      let actStx ← PrettyPrinter.delab $ mkAppN act vs
      let actTpStx ← `(∀ ($st $st' : $stateTp), ($systemTp).$(mkIdent `inv) $st → $actStx $st $st' → $property $st')
      let actThName := s!"{actName}_{invName}".toName
      let actId := Lean.mkIdent actName
      let proofScript ← `(by unhygienic intros; solve_clause [$actId])
      pure (actTpStx, actThName, proofScript)
  let checkTheorem ← `(@[invProof] theorem $(mkIdent thName) : $tpStx := $proofScript)
  let failedTheorem ← `(@[invProof] theorem $(mkIdent thName) : $tpStx := sorry)
  return (invName, (thName, checkTheorem, failedTheorem))

/--  Generate theorems to check in the initial state and after each action -/
def getAllChecks : CommandElabM (InitChecksT × ActionsChecksT) := do
  let (initChecks, actChecks) ← Command.runTermElabM fun vs => do
    let invNames := ((← stsExt.get).invariants ++ (← stsExt.get).safeties).map Expr.constName!
    let actNames := ((<- stsExt.get).transitions).map (Expr.constName! ∘ Prod.snd)
    let mut initChecks := #[]
    let mut actChecks := #[]
    -- (1) Collect checks that invariants hold in the initial state
    for invName in invNames do
      initChecks := initChecks.push (← getCheckFor invName CheckType.init vs)
    -- (2) Collect checks that invariants hold after each action
    for actName in actNames do
        let mut checks := #[]
        for invName in invNames do
          checks := checks.push (← getCheckFor invName (CheckType.action actName) vs)
        actChecks := actChecks.push (actName, checks)
    pure (initChecks, actChecks)
  return (initChecks, actChecks)

/-- Generate theorems to check the given invariant clause in the initial
state and after each action. -/
def getChecksForInvariant (invName : Name) : CommandElabM (InitChecksT × ActionsChecksT) := do
  let (initChecks, actChecks) ← Command.runTermElabM fun vs => do
    let actNames := ((<- stsExt.get).transitions).toArray.map (Expr.constName! ∘ Prod.snd)
    let initChecks := #[← getCheckFor invName CheckType.init vs]
    let actChecks ← actNames.mapM fun actName => do
      let checks := #[← getCheckFor invName (CheckType.action actName) vs]
      return (actName, checks)
    pure (initChecks, actChecks)
  return (initChecks, actChecks)

/-- Generate therems to check all invariants after the given action. -/
def getChecksForAction (actName : Name) : CommandElabM (InitChecksT × ActionsChecksT) := do
  let (initChecks, actChecks) ← Command.runTermElabM fun vs => do
    let invNames := ((<- stsExt.get).invariants ++ (<- stsExt.get).safeties).toArray.map Expr.constName!
    let invChecks ← invNames.mapM (fun invName => do return (← getCheckFor invName (CheckType.action actName) vs))
    pure (#[], #[(actName, invChecks)])
  return (initChecks, actChecks)

inductive CheckInvariantsBehaviour
  /-- `#check_invariants` -/
  | checkTheorems
  /-- `#check_invariants?` -/
  | printTheorems
  /-- `#check_invariants!` -/
  | printAndCheckTheorems

def checkTheorems (stx : Syntax) (initChecks : ActionChecksT) (actChecks : ActionsChecksT) (behaviour : CheckInvariantsBehaviour := .checkTheorems) : CommandElabM Unit := do
  let mut theorems := #[] -- collect Lean expression to report for `#check_invariants?` and `#check_invariants!`
  match behaviour with
  | .printTheorems =>
    let actInvChecks := Array.flatten $ actChecks.map (fun (_, actChecks) => actChecks)
    for (_, (_, thCmd, _)) in (initChecks ++ actInvChecks) do
      theorems := theorems.push thCmd
    displaySuggestion stx theorems
  | .checkTheorems | .printAndCheckTheorems =>
    let mut msgs := #[]
    if !initChecks.isEmpty then
      msgs := msgs.push "Initialization must establish the invariant:"
    for (invName, (thName, thCmd, sorryThm)) in initChecks do
      let success ← checkTheorem thName thCmd
      msgs := msgs.push s!"  {invName} ... {if success then "✅" else "❌"}"
      let thm := if success then thCmd else sorryThm
      theorems := theorems.push thm
    if !actChecks.isEmpty then
      msgs := msgs.push "The following set of actions must preserve the invariant:"
    for (actName, invChecks) in actChecks do
      msgs := msgs.push s!"  {actName}"
      for (invName, (thName, thCmd, sorryThm)) in invChecks do
        let success ← checkTheorem thName thCmd
        msgs := msgs.push s!"    {invName} ... {if success then "✅" else "❌"}"
        let thm := if success then thCmd else sorryThm
        theorems := theorems.push thm
    let msg := (String.intercalate "\n" msgs.toList) ++ "\n"
    match behaviour with
    | .checkTheorems => dbg_trace msg
    | .printAndCheckTheorems => displaySuggestion stx theorems (preMsg := msg)
    | _ => unreachable!
  where displaySuggestion (stx : Syntax) (theorems : Array (TSyntax `command)) (preMsg : Option String := none) := do
    Command.liftTermElabM do
    let cmd ← constructCommands theorems
    let suggestion : Suggestion := {
      suggestion := cmd
      preInfo? := preMsg
      toCodeActionTitle? := .some (fun _ => "Replace with explicit proofs.")
    }
    addSuggestion stx suggestion (header := "")

/- ## `#check_invariants` -/
/-- Check all invariants and print result of each check. -/
syntax "#check_invariants" : command
/-- Suggest theorems to check all invariants. -/
syntax "#check_invariants?" : command
/-- Check all invariants, print the result of each check, and suggest
theorems corresponding to the result of these checks. Theorems that
could not be proven have their proofs replaced with `sorry`. -/
syntax "#check_invariants!" : command

/-- Prints output similar to that of Ivy's `ivy_check` command. -/
def checkInvariants (stx : Syntax) (behaviour : CheckInvariantsBehaviour := .checkTheorems) : CommandElabM Unit := do
  let (initChecks, actChecks) ← getAllChecks
  checkTheorems stx initChecks actChecks behaviour

elab_rules : command
  | `(command| #check_invariants%$tk) => checkInvariants tk (behaviour := .checkTheorems)
  | `(command| #check_invariants?%$tk) => checkInvariants tk (behaviour := .printTheorems)
  | `(command| #check_invariants!%$tk) => checkInvariants tk (behaviour := .printAndCheckTheorems)


/- ## `#check_invariant` -/
syntax "#check_invariant" ident : command
syntax "#check_invariant?" ident : command
syntax "#check_invariant!" ident : command

/-- Prints output similar to that of Ivy's `ivy_check` command limited to a single invariant. -/
def checkInvariant (stx : Syntax) (invName : TSyntax `ident) (behaviour : CheckInvariantsBehaviour := .checkTheorems) : CommandElabM Unit := do
  let (initChecks, actChecks) ← getChecksForInvariant invName.getId
  checkTheorems stx initChecks actChecks behaviour

elab_rules : command
  | `(command| #check_invariant%$tk $invName) => checkInvariant tk invName (behaviour := .checkTheorems)
  | `(command| #check_invariant?%$tk $invName) => checkInvariant tk invName (behaviour := .printTheorems)
  | `(command| #check_invariant!%$tk $invName) => checkInvariant tk invName (behaviour := .printAndCheckTheorems)

/- ## `#check_action` -/
syntax "#check_action" ident : command
syntax "#check_action?" ident : command
syntax "#check_action!" ident : command

/-- Prints output similar to that of Ivy's `ivy_check` command limited to a single action. -/
def checkAction (stx : Syntax) (actName : TSyntax `ident) (behaviour : CheckInvariantsBehaviour := .checkTheorems) : CommandElabM Unit := do
  let (initChecks, actChecks) ← getChecksForAction (toTrIdent actName).getId
  checkTheorems stx initChecks actChecks behaviour

elab_rules : command
  | `(command| #check_action%$tk $actName) => checkAction tk actName (behaviour := .checkTheorems)
  | `(command| #check_action?%$tk $actName) => checkAction tk actName (behaviour := .printTheorems)
  | `(command| #check_action!%$tk $actName) => checkAction tk actName (behaviour := .printAndCheckTheorems)

open Tactic in
/-- Try to solve the goal using one of the already proven invariant clauses,
    i.e. one of those marked with `@[invProof]` (via `#check_invariants`). -/
elab "already_proven" : tactic => withMainContext do
  let clauses := (← stsExt.get).establishedClauses.toArray
  let tacs ← clauses.mapM (fun cl => `(tactic|(try apply $(mkIdent cl) <;> assumption)))
  let attempt ← `(tactic| solve $[| $tacs:tactic]*)
  evalTactic attempt

elab "prove_inv_init" proof:term : command => do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- PrettyPrinter.delab (<- stateTp vs)
    `(theorem $(mkIdent `inv_init) : invInit (σ := $stateTp) :=
       by unfold invInit
          -- simp only [initSimp, invSimp]
          intros $(mkIdent `st)
          exact $proof)

elab "prove_inv_safe" proof:term : command => do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp   <- PrettyPrinter.delab (<- stateTp vs)
    `(theorem $(mkIdent `safety_init) : invSafe (σ := $stateTp) :=
       by unfold invSafe;
          -- simp only [initSimp, safeSimp]
          intros $(mkIdent `st);
          exact $proof)

elab "prove_inv_inductive" proof:term : command => do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp   <- PrettyPrinter.delab (<- stateTp vs)
    `(theorem $(mkIdent `inv_inductive) : invInductive (σ := $stateTp) :=
      by unfold invInductive invInit invConsecution;
        --  intros $(mkIdent `st) $(mkIdent `st')
        --  simp only [actSimp, invSimp, safeSimp]
         exact $proof)

/- This is a bit stupid, but we place these here so `type` doesn't interfere with
  the `Declaration` definition in `checkTheorem` above. -/
macro "type" id:ident : command => `(variable ($id : Type) [DecidableEq $id])
macro "instantiate" t:term : command => `(variable [$t])
macro "instantiate" nm:ident " : " t:term : command => `(variable [$nm : $t])

attribute [initSimp] RelationalTransitionSystem.init
attribute [invSimp] RelationalTransitionSystem.inv
attribute [invSimp] RelationalTransitionSystem.safe
attribute [safeSimp] RelationalTransitionSystem.safe
attribute [actSimp] RelationalTransitionSystem.next
