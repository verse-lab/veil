import Lean
import Lean.Parser
import Veil.DSL.Base
import Veil.DSL.Internals.Attributes
import Veil.DSL.Internals.StateExtensions
import Veil.DSL.Action.Lang
import Veil.DSL.Tactic
import Veil.Tactic.Main
import Veil.Util.DSL

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
  /- When you include module `M` in your current module, to get access to a field `F` of `M`
    you would write `M.F`. That is why non-atomic names (those with `.`) might lead to
    confusion -/
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

/-- Define a `relation`. -/
def defineRelation (comp : StateComponent) : CommandElabM Unit :=
  defineStateComponent comp
     (fun (tp : Expr) => do
      let returnSProp ← liftTermElabM $ forallTelescope tp (fun _ b => do return b.isProp)
      return returnSProp)
    (fun comp => do throwErrorAt (← comp.stx) "Invalid type: relations must return Prop")

/-- Define a `function`. -/
def defineFunction (comp : StateComponent) : CommandElabM Unit :=
  defineStateComponent comp
    (fun (tp : Expr) => do return tp.isArrow)
    (fun comp => do throwErrorAt (← comp.stx) "Invalid type: functions must have arrow type")

def isActionSyntax (stack : Syntax.Stack) : Bool :=
  stack.any (fun (s, _) => s.isOfKind `VeilInit || s.isOfKind `VeilAction)

/-- Instruct the linter to not mark state variables as unused in our
`after_init` and `action` definitions. -/
def generateIgnoreFn : CommandElabM Unit := do
  let cmd ← Command.runTermElabM fun _ => do
    let fieldNames ← getFields
    let fnIdents ← fieldNames.mapM (fun n => `($(quote n)))
    let namesArrStx ← `(#[$[$fnIdents],*])
    let fnStx ← `(fun id stack _ => ($namesArrStx).contains id.getId /-&& isActionSyntax stack-/)
    let nm := mkIdent $ ← getPrefixedName `ignoreStateFields
    let ignoreFnStx ← `(@[unused_variables_ignore_fn] def $nm : Lean.Linter.IgnoreFunction := $fnStx)
    return ignoreFnStx
  elabCommand cmd

def genStateExtInstances : CommandElabM Unit := do
  let currName <- getCurrNamespace
  let vd := (<- getScope).varDecls
  let insts <- Command.runTermElabM fun vs => do
    let mut insts := #[]
    for (name, ts, alia) in (<- localSpecCtx.get).spec.dependencies do
      let currTs <- getStateArgumentsStx vd vs
      let alia := mkIdent alia
      let inst <-
        `(@[actSimp]
          instance :
           IsStateExtension
             (@$(mkIdent $ name ++ `State) $ts*)
             (@$(mkIdent $ currName ++ `State) $currTs*) where
            extendWith := fun s s' => { s' with $alia:ident := s }
            restrictTo := fun s' => s'.$alia)
      insts := insts.push inst
    return insts
  for inst in insts do
    trace[veil.debug] "Generating state extension instance {inst}"
    elabCommand inst
    trace[veil.info] "State extension instance is defined"

declare_syntax_cat actionType
syntax (name := inputAction) "input" : actionType
syntax (name := internalAction) "internal" : actionType
syntax (name := outputAction) "output" : actionType

/-- Transition defined via a two-state relation. -/
syntax (actionType)? "transition" ident (explicitBinders)? "=" term : command

-- /-- Transition defined via a two-state relation. -/
-- syntax (priority := high) (actionType)? "transition" ident (explicitBinders)? "=" "{" term "}" : command

elab actT:(actionType)? "transition" nm:ident br:explicitBinders ? "=" "{" t:term "}" : command => do
  let fields : Array Name <- getFields
  let mut unchangedFields := #[]
  for f in fields do
    unless t.raw.find? (·.getId.toString == f.toString ++ "'") |>.isSome do
      unchangedFields := unchangedFields.push $ mkIdent f
  elabCommand $ <- `($actT:actionType ? transition $nm $br ? = by
    intros st st'
    unhygienic cases st
    with_rename "'" unhygienic cases st'
    exact [unchanged|"'"| $unchangedFields*] ∧ ($t))


/-- Transition defined as an imperative program in `ActionLang`. We call
these "actions". All capital letters in `require` and in assignments are
implicitly quantified. -/
syntax (actionType)? "action" ident (explicitBinders)? "=" "{" doSeq "}" : command

def defineDepsActions : CommandElabM Unit := do
  for (name, ts, al) in (<- localSpecCtx.get).spec.dependencies do
    let globalCtx <- globalSpecCtx.get
    let some ctx := globalCtx[name]? | throwError "Module {name} is not declared"
    for act in ctx.actions do
      let actName := if act.hasSpec then name ++ act.decl.name ++ `spec else name ++ act.decl.name
      let currName := mkIdent <| al ++ actName.componentsRev[0]!
      let actArgs <- liftTermElabM do match act.br with
        | some br => existentialIdents br
        | _ => return #[]
      let typeClassInsts := List.replicate ctx.typeClassNum (<- `(_)) |>.toArray
      let actArgs := typeClassInsts.append actArgs
      let stx <- `(action $currName:ident $(act.br)? = { monadLift <| @$(mkIdent $ actName) $ts* $actArgs* })
      trace[veil.debug] stx
      elabCommand stx

/-- Assembles all declared `relation` predicates into a single `State` type. -/
def assembleState : CommandElabM Unit := do
  let vd := (<- getScope).varDecls
  let typeClassNum := vd.filter isTypeClassBinder |>.size
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
    localSpecCtx.modify ({· with spec.stateStx := stateTp, spec.typeClassNum := typeClassNum })
  genStateExtInstances
  defineDepsActions


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

syntax optModule := ("(" ident")")

/-- Declare an `individual` state component. -/
elab m:(state_mutability)? "individual" mod:optModule ? sig:Command.structSimpleBinder : command => do
  let name := match mod with
    | some mod => match mod with
      | `(optModule|($id:ident)) => some id.getId
      | _ => none
    | none => none
  let comp := StateComponent.mk (stxToMut m) .individual (← liftCoreM $ getSimpleBinderName sig) (.simple sig) name
  defineStateComponent comp
    (fun (tp : Expr) => return !tp.isArrow)
    (fun comp => do throwErrorAt (← comp.stx) "Invalid type: constants must not be arrow types")

/-- Declare a relation, giving only the type, e.g.
  ```lean
  relation R : address → round → Prop
  ```
-/
elab m:(state_mutability)? "relation" sig:Command.structSimpleBinder : command => do
  let rel := StateComponent.mk (stxToMut m) .relation (← liftCoreM $ getSimpleBinderName sig) (.simple sig) none
  defineRelation rel

/-- Declare a relation, giving names to the arguments, e.g.:
  ```lean
  relation sent (n : address) (r : round)
  ```
-/
elab m:(state_mutability)? "relation" nm:ident br:(bracketedBinder)* (":" "Prop")? : command => do
  let rel := StateComponent.mk (stxToMut m) .relation nm.getId (.complex br (← `(Prop))) none
  defineRelation rel

/-- `function` command saves a State structure field declaration -/
elab m:(state_mutability)? "function" sig:Command.structSimpleBinder : command => do
  let func := StateComponent.mk (stxToMut m) .function (← liftCoreM $ getSimpleBinderName sig) (.simple sig) none
  defineFunction func

/-- Declare a function, giving names to the arguments. Example:
  ```lean
  function currentRound (n : address) : round
  ```
-/
elab m:(state_mutability)? "function" nm:ident br:(bracketedBinder)* ":" dom:term: command => do
  let func := StateComponent.mk (stxToMut m) .relation nm.getId (.complex br dom) none
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
    let stx' <- funcasesM t (← getStateArguments vd vs)
    elabBindersAndCapitals br vs stx' fun _ e => do
      let e <- delabWithMotives e
      let stx ← `(@[actSimp, invSimp, invSimpTopLevel] abbrev $nm $[$vd']* $br* ($(mkIdent `st) : $stateTp := by exact_state) : Prop := $e)
      trace[veil.debug] "{stx}"
      return stx

syntax moduleAbbrev := ("as" ident)?

def checkModuleExists (id : Name) [Monad m] [MonadEnv m] [MonadError m] : m Unit := do
  let modules := (<- globalSpecCtx.get)
  unless modules.contains id do
    throwError s!"Module {id} does not exist"

elab "includes" nm:ident ts:term:max * ma:moduleAbbrev : command => do
  let name := nm.getId
  checkModuleExists name
  let mut alia := name
  if let `(moduleAbbrev| as $al) := ma then alia := al.getId
  elabCommand $ <- `(individual ($nm) $(mkIdent alia):ident : @$(mkIdent $ name ++ `State) $ts*)
  localSpecCtx.modify (fun s => { s with spec.dependencies := s.spec.dependencies.push (name, ts, alia) })

@[inherit_doc assembleState]
elab "#gen_state" : command => assembleState

/-! ## Initializers -/

/-- Declare the initial state predicate. -/
elab "initial" ini:term : command => do
  liftCoreM errorIfStateNotDefined
  let vd ← getAssertionParameters
  elabCommand <| <- Command.runTermElabM fun _ => do
    -- let stateTp ← getStateTpStx
    -- let expectedType ← `($stateTp → Prop)
    let ini ←  simplifyTerm ini
    let predName := `initialState?
    -- because of `initDef`, this sets `stsExt.init` with `lang := none`
    `(@[initDef, initSimp] def $(mkIdent predName) $[$vd]* := $ini)

/-- Declare the initial state predicate as an imperative program in
`ActionLang`. -/
elab (name := VeilInit) "after_init" "{" l:doSeq "}" : command => do
    liftCoreM errorIfStateNotDefined
    let (ret, st, st', st_curr, post) := (mkIdent `ret, mkIdent `st, mkIdent `st', mkIdent `st_curr, mkIdent `post)
    let vd ← getAssertionParameters
    -- define initial state action (`Wlp`)
    let act ← Command.runTermElabM fun _ => (do
      let stateTp ← getStateTpStx
      `(fun ($st : $stateTp) ($post : SProp $stateTp) => (do' .external in $l) $st (fun $ret ($st_curr : $stateTp) => $post $st_curr)))
    elabCommand $ ← Command.runTermElabM fun _ => do
      let actName := `init
      `(@[initSimp, actSimp] def $(mkIdent actName) $[$vd]* := $act)
    -- define initial state predicate
    let pred ← Command.runTermElabM fun _ => (do
      let stateTp ← getStateTpStx
      `(fun ($st' : $stateTp) => ∃ ($(toBinderIdent st) : $stateTp), Wlp.toActProp (do' .external in $l) $st $st'))
    -- this sets `stsExt.init` with `lang := none`
    elabCommand $ ← `(initial $pred)
    -- we modify it to store the `lang`
    liftTermElabM do localSpecCtx.modify (fun s => { s with spec := {s.spec with init := {s.spec.init with lang := .some l}}})
    let sp ← liftTermElabM $ return (← localSpecCtx.get).spec.init
    trace[veil.debug] s!"{sp}"

/-! ## Actions -/

def toActionType (stx : TSyntax `actionType) : ActionType :=
  match stx with
  | `(actionType|input) => ActionType.input
  | `(actionType|internal) => ActionType.internal
  | `(actionType|output) => ActionType.output
  | _ => unreachable!

def toActionTypeIdent (stx : TSyntax `actionType) : Ident :=
  mkIdent $ match stx with
  | `(actionType|input) => ``ActionType.input
  | `(actionType|internal) => ``ActionType.internal
  | `(actionType|output) => ``ActionType.output
  | _ => unreachable!

/-- `action foo` means `internal action foo` -/
def parseActionTypeStx (stx : Option (TSyntax `actionType)) : CommandElabM (TSyntax `actionType) := do
  return stx.getD $ ← `(actionType|internal)

open Command Term in
/-- Record the action type and signature of this action in the `localSpecificationCtx`.  -/
def registerIOActionDecl (actT : TSyntax `actionType) (nm : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)): CommandElabM Unit := do
  trace[veil.debug] s!"registering action {actT} {nm}"
  let moduleName <- getCurrNamespace
  Command.runTermElabM fun _ => do
    let name := nm.getId
    let labelTypeName := mkIdent `Label
    let br ← match br with
    | some br => toBracketedBinderArray br
    | none => pure $ TSyntaxArray.mk #[]
    let ctor ← `(ctor| | $nm:ident $br* : $labelTypeName)
    let actdecl : ActionDeclaration := {
      type := toActionType actT,
      name := name,
      ctor := ctor
    }
    /- Find the appropriate transition and add the `ActionDeclaration`
    to it Note that this DOES NOT add the `lang` representing the DSL
    code We do that by a further modification in the relevant elaborator
    (see [add_action_lang]) -/
    localSpecCtx.modify (fun s =>
      { s with spec.actions :=
        s.spec.actions.map fun t =>
          if t.name == moduleName ++ name then
            { t with decl := actdecl }
          else t})

def wlpUnfold := [``Wlp.bind, ``Wlp.pure, ``Wlp.get, ``Wlp.set, ``Wlp.modifyGet,
  ``Wlp.assert, ``Wlp.assume, ``Wlp.require, ``Wlp.spec, ``Wlp.lift, ``Wlp.toActProp]

def simpleAddDefn (n : Name) (e : Expr)
  (red := Lean.ReducibilityHints.regular 0)
  (attr : Array Attribute := #[])
  (type : Option Expr := none) : TermElabM Unit := do
  addDecl <|
    Declaration.defnDecl <|
      mkDefinitionValEx n [] (type.getD <| ← inferType e) e red
      (DefinitionSafety.safe) []
  applyAttributes n attr

def mkLambdaFVarsImplicit (vs : Array Expr) (e : Expr) : TermElabM Expr := do
  let e <- mkLambdaFVars vs e
  return go vs.size e
  where go (cnt : Nat) (e : Expr) : Expr :=
    match cnt, e with
    | 0, _ => e
    | _, Expr.lam n d b .default =>
      let b := go (cnt-1) b
      Expr.lam n d b .implicit
    | _, Expr.lam n d b bi =>
      let b := go (cnt-1) b
      Expr.lam n d b bi
    | _, _ => e

/-- Defines `act` : `Wlp m σ ρ` monad computation, parametrised over `br`.
  More specifically it defines 4 things
  - `act.unsimplified : ∀ m, Wlp m σ ρ`: unsimplified version of `act`, which
    incorporates  -/
def elabCallableFn (actT : TSyntax `actionType) (nm : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (l : doSeq) : CommandElabM Unit := do
    let vd ← getImplicitActionParameters
    Command.runTermElabM fun vs => do
      -- Create binders and arguments
      let sectionArgs ← getSectionArgumentsStx vs
      -- let stateTpT ← getStateTpStx
      let (univBinders, args, funNinders) ← match br with
      | some br => pure (← toBracketedBinderArray br, ← existentialIdents br, <- toFunBinderArray br)
      | none => pure (#[], #[], #[])
      -- Create types
      let moduleName <- getCurrNamespace
      let genEName := moduleName ++ nm.getId ++ `genE
      let genIName := moduleName ++ nm.getId ++ `genI
      -- The actual command (not term) elaboration happens here
      let genlI <- `(fun $funNinders* => do' .internal in $l)
      let genlE <- `(fun $funNinders* => do' .external in $l)

      let genExpI <- withDeclName genIName do elabTermAndSynthesize genlI none
      let genExpE <- withDeclName genEName do elabTermAndSynthesize genlE none
      let wlpSimp := mkIdent `wlpSimp
      let ⟨genExpE, _, _⟩ <- genExpE.runSimp `(tactic| simp only [$wlpSimp:ident])
      let ⟨genExpI, _, _⟩ <- genExpI.runSimp `(tactic| simp only [$wlpSimp:ident])
      let genExpE <- instantiateMVars <| <- mkLambdaFVarsImplicit vs genExpE
      let genExpI <- instantiateMVars <| <- mkLambdaFVarsImplicit vs genExpI
      simpleAddDefn genEName genExpE (attr := #[{name := `actSimp}, {name := `reducible}])
      simpleAddDefn genIName genExpI (attr := #[{name := `actSimp}, {name := `reducible}])

      let actE <- Lean.mkConst genEName |>.runUnfold (genEName :: wlpUnfold)
      let actI <- Lean.mkConst genIName |>.runUnfold (genIName :: wlpUnfold)
      let ⟨actE, actEPf, _⟩ <- actE.runSimp `(tactic| simp only [actSimp, logicSimp, smtSimp, quantifierSimp])
      let ⟨actI, actIPf, _⟩ <- actI.runSimp `(tactic| simp only [actSimp, logicSimp, smtSimp, quantifierSimp])
      let actEName := moduleName ++ nm.getId ++ `ext
      let actIName := moduleName ++ nm.getId
      let attr := toActionAttribute' (toActionType actT)
      simpleAddDefn actEName actE (attr := #[{name := `actSimp}]) (type := <- inferType genExpE)
      simpleAddDefn actIName actI (attr := #[{name := `actSimp}, attr]) (type := <- inferType genExpI)


      let actTrStx <- `(fun st st' => exists? $br ?, (@$(mkIdent actEName) $sectionArgs* $args*).toActProp st st')
      let actTr <- elabTermAndSynthesize actTrStx none
      let actTr <- mkLambdaFVarsImplicit vs actTr
      let ⟨actTr, actTrPf, _⟩ <- actTr.runSimp `(tactic| simp only [actSimp, logicSimp, smtSimp, quantifierSimp])
      let actTr <- instantiateMVars actTr
      let actTrName := moduleName ++ nm.getId ++ `tr
      simpleAddDefn actTrName actTr (attr := #[{name := `actSimp}])

      if veil.gen_sound.get <| <- getOptions then
        let trActThmStatement ← `(forall? $[$vd]* , ($actTrStx) = (@$(mkIdent actTrName) $sectionArgs*))
        let trActThm ← elabTermAndSynthesize trActThmStatement (.some <| .sort .zero)
        let actTrPf := actTrPf.get!
        let tytemp ← inferType actTrPf
        -- the type of `actTrPf` is `fun xs ys => ... = fun xs ys' => ...`
        -- need to transform it into `forall xs, fun ys ... => ... = fun ys' ... => ...`
        if let .some (ty, lhs, rhs) := tytemp.eq? then
          -- here the proof term is hardcoded
          let proof ← lambdaBoundedTelescope lhs vs.size fun xs _ => do
            let rhsApplied := mkAppN rhs xs
            let eq1 ← withLocalDeclD `_a ty fun va => do
              let vaApplied := mkAppN va xs
              let eq1 ← mkEq vaApplied rhsApplied
              mkLambdaFVars #[va] eq1
            let congrArgUse ← mkAppM ``congrArg #[eq1, actTrPf]
            let eq2 ← mkEqRefl rhsApplied
            let proofBody ← mkAppM ``Eq.mpr #[congrArgUse, eq2]
            mkLambdaFVars xs proofBody
          addDecl <| Declaration.thmDecl <| mkTheoremValEx (moduleName ++ nm.getId ++ `act_tr_eq) [] trActThm proof []

        let instETp <- `(forall? $[$vd]* $univBinders*, Sound (@$(mkIdent genEName):ident $sectionArgs* $args*))
        let instETp <- elabTermAndSynthesize instETp none
        let instITp <- `(forall? $[$vd]* $univBinders*, Sound (@$(mkIdent genIName):ident $sectionArgs* $args*))
        let instITp <- elabTermAndSynthesize instITp none

        simpleAddThm (moduleName ++ nm.getId ++ `genEInst) instETp `(tacticSeq| intros; infer_instance) (attr := #[{name := `instance}])
        simpleAddThm (moduleName ++ nm.getId ++ `genIInst) instITp `(tacticSeq| intros; infer_instance) (attr := #[{name := `instance}])
        let eqETp <- `(@$(mkIdent genEName) = @$(mkIdent actEName))
        let eqITp <- `(@$(mkIdent genIName) = @$(mkIdent actIName))
        let eqETp <- elabTermAndSynthesize eqETp none
        let eqITp <- elabTermAndSynthesize eqITp none
        let eqE <- ensureHasType eqETp <| actEPf.getD <| <- mkAppM ``Eq.refl #[mkConst actEName]
        let eqI <- ensureHasType eqITp <| actIPf.getD <| <- mkAppM ``Eq.refl #[mkConst actIName]
        let eqE <- Term.exprToSyntax eqE
        let eqI <- Term.exprToSyntax eqI

        let instETp <- `(forall? $[$vd]* $univBinders*, Sound (m := .external) (@$(mkIdent actEName):ident $sectionArgs* $args*))
        let instETp <- elabTermAndSynthesize instETp none
        let instITp <- `(forall? $[$vd]* $univBinders*, Sound (m := .internal) (@$(mkIdent actIName):ident $sectionArgs* $args*))
        let instITp <- elabTermAndSynthesize instITp none

        simpleAddThm (moduleName ++ nm.getId ++ `instExt) instETp
          `(tacticSeq|
            have h : @$(mkIdent genEName) = @$(mkIdent actEName) := $eqE
            rw [<-h]; intros; infer_instance) (attr := #[{name := `instance}])
        simpleAddThm (moduleName ++ nm.getId ++ `inst) instITp
          `(tacticSeq|
            have h : @$(mkIdent genIName) = @$(mkIdent actIName) := $eqI
            rw [<-h]; intros; infer_instance) (attr := #[{name := `instance}])


/-- Elaborates a two-state transition. FIXME: get rid of code duplication with `elabCallableFn`. -/
def elabCallableTr (actT : TSyntax `actionType) (nm : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (tr : Term) : CommandElabM Unit := do
    let vd ← getImplicitActionParameters
    -- `nm.unsimplified`
    let (uName, fnName, extName, trName) := (toUnsimplifiedIdent nm, nm, toExtIdent nm, toTrIdent nm)
    let (unsimplifiedDef, trDef, extDef, fnDef) ← Command.runTermElabM fun vs => do
      let stateTpT ← getStateTpStx
      let trType <- `($stateTpT -> $stateTpT -> Prop)
      -- Create binders and arguments
      let sectionArgs ← getSectionArgumentsStx vs
      let (univBinders, args) ← match br with
      | some br => pure (← toBracketedBinderArray br, ← existentialIdents br)
      | none => pure (#[], #[])
      let unsimplifiedDef ← `(@[actSimp] def $uName $[$vd]* $univBinders* : $trType := $tr)
      trace[veil.debug] "{unsimplifiedDef}"
      -- `nm.tr`, with existentially quantified arguments
      let trDef ← do
        let (st, st') := (mkIdent `st, mkIdent `st')
        let rhs ← match br with
        | some br => `(fun ($st $st' : $stateTpT) => ∃ $br, @$uName $sectionArgs* $args* $st $st')
        | none => `(fun ($st $st' : $stateTpT) => @$uName $sectionArgs* $args* $st $st')
        `(@[actSimp] def $trName $[$vd]* : $trType := $(← unfoldWlp rhs))
      let attr ← toActionAttribute (toActionType actT)
      let fnDef ← `(@[$attr, actSimp] def $fnName $[$vd]* $univBinders* := $(← unfoldWlp $ ← `((@$uName $sectionArgs* $args*).toWlp .internal)))
      let extTerm ← `(fun (st : $stateTpT) post => forall? $univBinders*, (@$uName $sectionArgs* $args*).toWlp .external st post)
      let extDef ← `(@[$attr, actSimp] def $extName $[$vd]* :=  $(<- unfoldWlp extTerm) )
      trace[veil.debug] "{fnDef}"
      return (unsimplifiedDef, trDef, extDef, fnDef)
    -- Declare `nm.unsimplified` and `nm`
    elabCommand unsimplifiedDef
    trace[veil.info] "{uName} is defined"
    elabCommand trDef
    trace[veil.info] "{fnName} is defined"
    elabCommand fnDef
    trace[veil.info] "{trName} is defined"
    elabCommand extDef
    trace[veil.info] "{extName} is defined"


/-- Show a warning if the given declaration has higher-order quantification -/
def warnIfNotFirstOrder (name : Name) : TermElabM Unit := do
  let module <- getCurrNamespace
  let .some decl := (← getEnv).find? (module ++ name) | throwError s!"{name} not found"
  let .some val := decl.value? | throwError s!"{name} has no value"
  let isFirstOrderUniv ← allHOQuantIsTopLevelForAll val
  if !isFirstOrderUniv then
    logWarning s!"{name} is not first-order (and cannot be sent to SMT)"

syntax (actionType)? "action" ident (explicitBinders)? "=" doSeq "{" doSeq "}" : command
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
      trace[veil.debug] "{stx}"
      return stx
    trace[veil.info] "{nm} specification is verified"
  catch e =>
    throwError s!"Error while checking the specification of {nm}:" ++ e.toMessageData


def elabAction (actT : Option (TSyntax `actionType)) (nm : Ident) (br : Option (TSyntax ``Lean.explicitBinders))
  (spec : Option doSeq) (l : doSeq) : CommandElabM Unit := do
    liftCoreM errorIfStateNotDefined
    let actT ← parseActionTypeStx actT
    -- Elab the action
    elabCallableFn actT nm br l
    -- warn if this is not first-order
    Command.liftTermElabM <| warnIfNotFirstOrder nm.getId
    trace[veil.info] s!"{nm} has no higher-order quantification"
    -- add constructor for label type
    registerIOActionDecl actT nm br
    Command.runTermElabM fun _ => do
      -- [add_action_lang] find the appropriate transition and add the `lang` declaration to it
      localSpecCtx.modify fun s =>
        { s with spec.actions := s.spec.actions.map fun t =>
          if t.name == nm.getId then
            { t with
              lang := l,
              hasSpec := spec.isSome,
              br   := br }
          else t }
    unless spec.isNone do
      let (pre, binder, post) <- getPrePost spec.get!
      elabCallableFn actT (nm.getId ++ `spec |> mkIdent) br spec.get!
      checkSpec nm br pre post binder

def elabTransition (actT : TSyntax `actionType) (nm : Ident) (br : Option (TSyntax ``Lean.explicitBinders)) (tr : Term) : CommandElabM Unit := do
    liftCoreM errorIfStateNotDefined
    elabCallableTr actT nm br tr
    -- warn if this is not first-order
    Command.liftTermElabM $ warnIfNotFirstOrder nm.getId
    -- add constructor for label type
    registerIOActionDecl actT nm br

/--
```lean
transition name binders* = tr
```
This command defines lifts a two-state formula into a `Wlp .internal σ Unit`
-/
elab_rules : command
  | `(command|$actT:actionType transition $nm:ident $br:explicitBinders ? = $tr) => do
  elabTransition actT nm br tr

elab_rules : command
  | `(command|$actT:actionType ? action $nm:ident $br:explicitBinders ? = {$l:doSeq}) => do
  elabAction actT nm br none l
  | `(command|$actT:actionType ? action $nm:ident $br:explicitBinders ? = $spec:doSeq {$l:doSeq}) =>
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

syntax "open_isolate" ident ("with" ident+)? : command
syntax "close_isolate" : command

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


/-- Axiom. All state components referred to must be `immutable`. All
capital variables are implicitly quantified. -/
elab "assumption" name:(propertyName)? prop:term : command => defineAssertion (kind := .assumption) name prop

/-- Invariant that is assumed. State components referred to can be `mutable`. All
capital variables are implicitly quantified. -/
elab "trusted" "invariant" name:(propertyName)? prop:term : command => defineAssertion (kind := .trustedInvariant) name prop

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
    -- let _ ← (← localSpecCtx.get).spec.actions.mapM (fun t => do trace[veil.debug] s!"{t}")
    let next ← if trs.isEmpty then `(fun ($st $st' : $stateTp) => $st = $st') else
              `(fun ($st $st' : $stateTp) => $(← repeatedOr trs))
    trace[veil.debug] "[assembleActions] {next}"
    `(@[actSimp] def $(mkIdent $ `Next) $[$vd]* := $next)
  trace[veil.info] "Next transition assembled"

def assembleLabelType (name : Name) : CommandElabM Unit := do
  let labelTypeName := mkIdent `Label
  elabCommand $ ← Command.runTermElabM fun _ => do
    let ctors ← (<- localSpecCtx.get).spec.actions.mapM (fun s => do match s.decl.ctor with
      | none => throwError "DSL: missing label constructor for action {s.name}"
      | some ctor => pure ctor)
    trace[veil] "storing constructors for {name}"
    `(inductive $labelTypeName where $[$ctors]*)
  trace[veil.info] "Label {labelTypeName} type is defined"

/-- Assembles the IOAutomata `ActionMap` for this specification. This is
a bit strange, since it constructs a term (syntax) to build a value. -/
def assembleActionMap : CommandElabM Unit := do
  elabCommand $ ← Command.runTermElabM fun vs => do
    let ioStx ← (← localSpecCtx.get).spec.actions.mapM fun decl => do
      let ioActName := toIOActionDeclName decl.label.name
      let act ← PrettyPrinter.delab $ ← mkAppOptM ioActName (vs.map Option.some)
      `(($(quote decl.label.name), $act))
    let actMapStx ← `(IOAutomata.ActionMap.ofList [$[$ioStx],*])
    let actMapStx ← `(def $(mkIdent `actionMap) := $actMapStx)
    trace[veil] "{actMapStx}"
    return actMapStx

/-- Assembles all declared invariants (including safety properties) into
a single `Invariant` predicate -/
def assembleInvariant : CommandElabM Unit := do
  let vd ← getAssertionParameters
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- getStateTpStx
    let allClauses := (<- localSpecCtx.get).spec.invariants
    let exprs := allClauses.toList.map (fun p => p.expr)
    let _ ← allClauses.mapM (fun t => do trace[veil.debug] s!"{t}")
    let invs ← if allClauses.isEmpty then `(fun _ => True) else PrettyPrinter.delab $ ← combineLemmas ``And exprs vs "invariants"
    `(@[invSimp, invSimpTopLevel] def $(mkIdent `Invariant) $[$vd]* : $stateTp -> Prop := $invs)
  trace[veil.info] "Invariant assembled"

/-- Assembles all declared safety properties into a single `Safety`
predicate -/
def assembleSafeties : CommandElabM Unit := do
  let vd ← getAssertionParameters
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- getStateTpStx
    let exprs := (<- localSpecCtx.get).spec.invariants.toList.filterMap (fun p => if p.kind == .safety then p.expr else none)
    let safeties ← if exprs.isEmpty then `(fun _ => True) else PrettyPrinter.delab $ ← combineLemmas ``And exprs vs "invariants"
    `(@[invSimp, invSimpTopLevel] def $(mkIdent `Safety) $[$vd]* : $stateTp -> Prop := $safeties)
  trace[veil.info] "Safety assembled"

/-- Assembles all declared `assumption`s into a single `Assumptions`
predicate -/
def assembleAssumptions : CommandElabM Unit := do
  let vd ← getAssertionParameters
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- getStateTpStx
    let exprs := (<- localSpecCtx.get).spec.assumptions.toList.map (fun p => p.expr)
    let assumptions ← if exprs.isEmpty then `(fun _ => True) else PrettyPrinter.delab $ ← combineLemmas ``And exprs vs "assumptions"
    `(@[invSimp, invSimpTopLevel] def $(mkIdent `Assumptions) $[$vd]* : $stateTp -> Prop := $assumptions)
  trace[veil.info] "Assumptions assembled"

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
  trace[veil] "{rtsStx}"
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

elab "#gen_spec" : command => do
  genSpec

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

/-- Declaring a Veil module -/
macro atomic("veil" "module") i:ident : command => do
  `(namespace $i:ident
    open Classical)
