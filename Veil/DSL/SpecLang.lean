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
  Command.runTermElabM fun _ => do
  -- set the name
    let components ← liftCommandElabM $ liftCoreM $ ((<- localSpecCtx.get).spec.signature).mapM StateComponent.getSimpleBinder
    -- record the state name
    localSpecCtx.modify (fun s => { s with stateBaseName := name })
    let stName ← getPrefixedName `State
    let sdef ← `(@[stateDef] structure $(mkIdent stName) $[$vd]* where $(mkIdent `mk):ident :: $[$components]*)
    let injEqLemma := (mkIdent $ stName ++ `mk ++ `injEq)
    let smtAttr ← `(attribute [smtSimp] $injEqLemma)
    liftCommandElabM $ elabCommand $ sdef
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
  let comp := StateComponent.mk (stxToMut m) .individual (getSimpleBinderName sig) (.simple sig)
  defineStateComponent comp
    (fun (tp : Expr) => return !tp.isArrow)
    (fun comp => do throwErrorAt (← comp.stx) "Invalid type: constants must not be arrow types")

/-- Declare a relation, giving only the type, e.g.
  ```lean
  relation R : address → round → Prop
  ```
-/
elab m:(state_mutability)? "relation" sig:Command.structSimpleBinder : command => do
  let rel := StateComponent.mk (stxToMut m) .relation (getSimpleBinderName sig) (.simple sig)
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
  let func := StateComponent.mk (stxToMut m) .function (getSimpleBinderName sig) (.simple sig)
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
  let vd := (<- getScope).varDecls
  -- As we are going to call this predicate explicitly we want to make all
  -- section binders implicit
  let vd' <- vd.mapM (fun x => mkImplicitBinders x)
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- stateTp vs
    let stateTp <- PrettyPrinter.delab stateTp
    let stx' <- funcasesM t vs
    elabBindersAndCapitals br vs stx' fun _ e => do
      let e <- elabWithMotives e
      `(@[actSimp, invSimp] abbrev $nm $[$vd']* $br* ($(mkIdent `st) : $stateTp := by exact_state) : Prop := $e)

@[inherit_doc assembleState]
elab "#gen_state" name:ident : command => assembleState name.getId

/-! ## Initializers -/

/-- Declare the initial state predicate. -/
elab "initial" ini:term : command => do
  elabCommand <| <- Command.runTermElabM fun vs => do
    let stateTp ← PrettyPrinter.delab $ ← stateTp vs
    let expectedType ← `($stateTp → Prop)
    let ini ←  simplifyTerm ini
    let name ← getPrefixedName `initialState?
    -- because of `initDef`, this sets `stsExt.init` with `lang := none`
    `(@[initDef, initSimp] def $(mkIdent name) : $expectedType := $ini)

/-- Declare the initial state predicate as an imperative program in
`ActionLang`. -/
elab "after_init" "{" l:langSeq "}" : command => do
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
      localSpecCtx.modify ({· with spec.stateStx := stateTp})
      `(fun ($st' : $stateTp) => ∃ ($(toBinderIdent st) : $stateTp), @$wlp _ _ (fun $ret $st => $st' = $st) [langSeq| $l ] $st))
    -- this sets `stsExt.init` with `lang := none`
    elabCommand $ ← `(initial $act)
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
      transitions := s.spec.transitions.map (fun t => if t.name == name then { t with decl := actdecl } else t) }})

/-- Defines `act.fn` : a function that returns a transition relation with return
  value (type `σ → (σ × ρ) → Prop`), universally quantified over `binders`. -/

def elabCallableFn (nm : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (l : TSyntax `langSeq) (nmt : Ident -> Ident := toFnIdent) : CommandElabM Unit := do
  let (originalName, nm) := (nm, nmt nm)
  elabCommand $ ← Command.runTermElabM fun vs => do
    let (ret, st, stret, wlp) := (mkIdent `ret', mkIdent `st, mkIdent `stret, mkIdent ``wlp)
    let stateTp ← PrettyPrinter.delab $ ← stateTp vs
    localSpecCtx.modify ({· with spec.stateStx := stateTp})
    -- `σ → (σ × ρ) → Prop`, with binders universally quantified
    -- $stret = ($st', $ret')
    let act <- `(fun ($st : $stateTp) $stret =>
      @$wlp _ _ (fun $ret ($st : $stateTp) => (Prod.fst $stret) = $st ∧ $ret = (Prod.snd $stret)) [langSeq| $l ] $st)
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

/-- Transition defined via a two-state relation. -/
syntax (actionType)? "transition" ident (explicitBinders)? "=" term : command

/-- Transition defined as an imperative program in `ActionLang`. We call
these "actions". All capital letters in `require` and in assignments are
implicitly quantified. -/
syntax (actionType)? "action" ident (explicitBinders)? "=" "{" lang "}" : command

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
    let expectedType ← mkArrow stateTp (← mkArrow stateTp mkProp)
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
  -- add constructor for label type
  registerIOActionDecl actT nm br

/-- Desugar an imperative `action` in `ActionLang` into a two-state
`transition` relation (as a Lean term). Here we compute the weakest
precondition of the program and then define the transition relation.

Note: Unlike `after_init` we expand `l` using `[lang| l]` (as opposed to
`[lang1| l]`) as we want the transition to refer to both pre-state and
post-state.-/

syntax (actionType)? "action" ident (explicitBinders)? "=" langSeq "{" langSeq "}" : command
syntax (actionType)? "action" ident (explicitBinders)? "=" "{" langSeq "}" : command

def checkSpec (nm : Ident) (nmImpl nmSpec : Ident) (br : Option (TSyntax `Lean.explicitBinders)) : CommandElabM Unit := do
  elabCommand $ ← Command.runTermElabM fun vs => do
    let (st, st') := (mkIdent `st, mkIdent `st')
    let thmName := mkIdent $ nm.getId ++ `spec_correct
    match br with
    | some br =>
      let br' <- toBracketedBinderArray br
      `(theorem $thmName :
        ∀ $br'*, ∀ $st:ident $st':ident,
          @$nmImpl $(← getSectionArgumentsStx vs)* $(← existentialIdents br)* $st $st' ->
          @$nmSpec $(← getSectionArgumentsStx vs)* $(← existentialIdents br)* $st $st' := by
          solve_clause)
    | none =>
      `(theorem $thmName :
        ∀ $st:ident $st':ident,
          @$nmImpl $(← getSectionArgumentsStx vs)* $st $st' ->
          @$nmSpec $(← getSectionArgumentsStx vs)* $st $st' := by solve_clause)


def elabAction (actT : Option (TSyntax `actionType)) (nm : Ident) (br : Option (TSyntax `Lean.explicitBinders))
  (spec : Option (TSyntax `langSeq)) (l : TSyntax `langSeq) : CommandElabM Unit := do
    let actT ← parseActionTypeStx actT
    let (ret, st, st', wlp) := (mkIdent `ret, mkIdent `st, mkIdent `st', mkIdent ``wlp)
    -- `σ → σ → Prop`, with binders existentially quantified
    let tr ← Command.runTermElabM fun vs => (do
      let stateTp ← PrettyPrinter.delab $ ← stateTp vs
      localSpecCtx.modify ({· with spec.stateStx := stateTp})
      `(fun ($st $st' : $stateTp) => @$wlp _ _ (fun $ret ($st : $stateTp) => $st' = $st) [langSeq| $l ] $st)
    )
    let trIdent := toTrIdent nm
    let spec' := if spec.isSome then spec else l
    elabCommand $ ← `($actT:actionType transition $trIdent $br ? = $tr)
    Command.runTermElabM fun _ => do
      -- [add_action_lang] find the appropriate transition and add the `lang` declaration to it
      localSpecCtx.modify (fun s => { s with spec := {s.spec with
        transitions := s.spec.transitions.map (fun t => if t.name == trIdent.getId then { t with lang := l, spec := spec' } else t)}})
    elabCallableFn nm br l
    unless spec.isNone do
      elabCallableFn nm br l (nmt := toSpecIdent)
      checkSpec nm (toFnIdent nm) (toSpecIdent nm) br

elab_rules : command
  | `(command|$actT:actionType ? action $nm:ident $br:explicitBinders ? = {$l:langSeq}) => elabAction actT nm br none l
  | `(command|$actT:actionType ? action $nm:ident $br:explicitBinders ? = $spec {$l:langSeq}) => elabAction actT nm br (some spec) l

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
  let (name, cmd) ← Command.runTermElabM fun vs => do
    let stateTp <- stateTp vs
    let stateTp <- PrettyPrinter.delab stateTp
    -- Check that the assumption does not refer to mutable state components
    if kind == .assumption then
      throwIfRefersToMutable t
    let stx <- funcasesM t vs
    let defaultName ← match kind with
      | .safety | .invariant => pure $ Name.mkSimple s!"inv_{(<- localSpecCtx.get).spec.invariants.size}"
      | .assumption => pure $ Name.mkSimple s!"axiom_{(<- localSpecCtx.get).spec.assumptions.size}"
    let name := getPropertyNameD name defaultName
    let cmd ← elabBindersAndCapitals #[] vs stx fun _ e => do
      let e <- elabWithMotives e
      match kind with
      | .safety =>
        `(@[safeDef, safeSimp, invSimp] def $(mkIdent name) : $stateTp -> Prop := fun $(mkIdent `st) => $e: term)
      | .invariant =>
        `(@[invDef, invSimp] def $(mkIdent name) : $stateTp -> Prop := fun $(mkIdent `st) => $e: term)
      | .assumption =>
        `(@[assumptionDef, invSimp] def $(mkIdent name) : $stateTp -> Prop := fun $(mkIdent `st) => $e: term)
    -- IMPORTANT: It is incorrect to do `liftCommandElabM $ elabCommand cmd` here
    -- (I think because of how `elabBindersAndCapitals` works)
    return (name, cmd)
  -- Do the elaboration to populate the `stsExt` state
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

/--Assembles all declared actions into a `Next` transition relation. -/
def assembleActions : CommandElabM Unit := do
  elabCommand $ ← Command.runTermElabM fun vs => do
    let stateTp <- PrettyPrinter.delab (<- stateTp vs)
    let acts := (<- localSpecCtx.get).spec.transitions.map (fun s => s.expr)
    let _ ← (← localSpecCtx.get).spec.transitions.mapM (fun t => do trace[dsl.debug] s!"{t}")
    let next ← if acts.isEmpty then `(fun s s' => s = s') else PrettyPrinter.delab $ ← combineLemmas ``Or acts.toList vs "transitions"
    `(@[actSimp] def $(mkIdent $ ← getPrefixedName `Next) : $stateTp -> $stateTp -> Prop := $next)

def assembleLabelType (name : Name) : CommandElabM Unit := do
  elabCommand $ ← Command.runTermElabM fun _ => do
    let labelTypeName := mkIdent $ ← getPrefixedName `Label
    let ctors ← (<- localSpecCtx.get).spec.transitions.mapM (fun s => do match s.decl.ctor with
      | none => throwError "DSL: missing label constructor for action {s.name}"
      | some ctor => pure ctor)
    trace[dsl] "storing constructors for {name}"
    `(inductive $labelTypeName where $[$ctors]*)

/-- Assembles the IOAutomata `ActionMap` for this specification. This is
a bit strange, since it constructs a term (syntax) to build a value. -/
def assembleActionMap : CommandElabM Unit := do
  elabCommand $ ← Command.runTermElabM fun vs => do
    let ioStx ← (← localSpecCtx.get).spec.transitions.mapM fun decl => do
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
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- PrettyPrinter.delab (<- stateTp vs)
    let allClauses := (<- localSpecCtx.get).spec.invariants
    let exprs := allClauses.toList.map (fun p => p.expr)
    let _ ← allClauses.mapM (fun t => do trace[dsl.debug] s!"{t}")
    let invs ← if allClauses.isEmpty then `(fun _ => True) else PrettyPrinter.delab $ ← combineLemmas ``And exprs vs "invariants"
    `(@[invSimp] def $(mkIdent $ ← getPrefixedName `Invariant) : $stateTp -> Prop := $invs)

/-- Assembles all declared safety properties into a single `Safety`
predicate -/
def assembleSafeties : CommandElabM Unit := do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- PrettyPrinter.delab (<- stateTp vs)
    let exprs := (<- localSpecCtx.get).spec.invariants.toList.filterMap (fun p => if p.kind == .safety then p.expr else none)
    let safeties ← if exprs.isEmpty then `(fun _ => True) else PrettyPrinter.delab $ ← combineLemmas ``And exprs vs "invariants"
    `(@[invSimp] def $(mkIdent $ ← getPrefixedName `Safety) : $stateTp -> Prop := $safeties)

/-- Assembles all declared `assumption`s into a single `Assumptions`
predicate -/
def assembleAssumptions : CommandElabM Unit := do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- PrettyPrinter.delab (<- stateTp vs)
    let exprs := (<- localSpecCtx.get).spec.assumptions.toList.map (fun p => p.expr)
    let assumptions ← if exprs.isEmpty then `(fun _ => True) else PrettyPrinter.delab $ ← combineLemmas ``And exprs vs "assumptions"
    `(@[invSimp] def $(mkIdent $ ← getPrefixedName `Assumptions) : $stateTp -> Prop := $assumptions)

/--
Instantiates the `RelationalTransitionSystem` type class with the declared actions, safety and invariant
-/
def instantiateSystem (name : Name) : CommandElabM Unit := do
  let vd := (<- getScope).varDecls
  assembleActions
  assembleInvariant
  assembleSafeties
  assembleAssumptions
  assembleLabelType name
  Command.runTermElabM fun vs => do
    -- set the name
    localSpecCtx.modify (fun s => { s with spec := {s.spec with name := name }})
    let stateTp   := mkAppN (<- localSpecCtx.get).spec.stateType vs
    let stateTpStx   <- PrettyPrinter.delab stateTp
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
  instantiateSystem name.getId
  Command.runTermElabM fun _ => do registerModuleSpecification (← localSpecCtx.get).spec

/-! ## Section Variables -/

/- FIXME: This is a bit stupid, but we place these here so they don't
interfere with the definitions above. For instance, we need to define a
`structure` with a field named `type` and that gets broken.
Unfortunately, this means we're breaking all the DSL clients. -/
macro "type" id:ident : command => `(variable ($id : Type) [DecidableEq $id])
macro "instantiate" t:term : command => `(variable [$t])
macro "instantiate" nm:ident " : " t:term : command => `(variable [$nm : $t])
