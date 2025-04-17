import Lean

import Veil.DSL.Action.Lang
import Veil.DSL.Tactic
import Veil.DSL.Specification.Syntax
import Veil.DSL.Specification.SpecDef

open Lean Elab Command Term Meta Lean.Parser

def wpUnfold := [``Wp.bind, ``Wp.pure, ``Wp.get, ``Wp.set, ``Wp.modifyGet,
  ``Wp.assert, ``Wp.assume, ``Wp.require, ``Wp.spec, ``Wp.lift, ``Wp.toTwoState]

def toActionKind (stx : TSyntax `actionKind) : ActionKind :=
  match stx with
  | `(actionKind|input) => ActionKind.input
  | `(actionKind|internal) => ActionKind.internal
  | `(actionKind|output) => ActionKind.output
  | _ => unreachable!

def toActionKindIdent (stx : TSyntax `actionKind) : Ident :=
  mkIdent $ match stx with
  | `(actionKind|input) => ``ActionKind.input
  | `(actionKind|internal) => ``ActionKind.internal
  | `(actionKind|output) => ``ActionKind.output
  | _ => unreachable!

def ActionKind.stx [Monad m] [MonadQuotation m] : ActionKind → m (TSyntax `actionKind)
  | .input => `(actionKind|input)
  | .internal => `(actionKind|internal)
  | .output => `(actionKind|output)

def Mode.stx [Monad m] [MonadQuotation m] : Mode → m (TSyntax `term)
  | .internal => `(term|$(mkIdent ``Mode.internal))
  | .external => `(term|$(mkIdent ``Mode.external))

/-- `action foo` means `internal action foo` -/
def parseActionKindStx (stx : Option (TSyntax `actionKind)) : CommandElabM (TSyntax `actionKind) := do
  return stx.getD $ ← `(actionKind|internal)

def assertProcedureDeclared [Monad m] [MonadEnv m] [MonadResolveName m] [MonadError m] (nm : Name) (op : String) : m Unit := do
  let procedureExists := (← localSpecCtx.get).spec.procedures.any fun t => t.name == nm
  if !procedureExists then
    throwError "Procedure {nm} has not been declared (trying to {op})"

open Command Term in
/-- Record the action type and signature of this action in the `localSpecificationCtx`.  -/
def registerIOActionDecl (actT : TSyntax `actionKind) (nm : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)): CommandElabM Unit := do
  assertActionDeclared nm.getId "registerIOActionDecl"
  Command.runTermElabM fun _ => do
    let name := nm.getId
    let labelTypeName := mkIdent `Label
    let br ← match br with
    | some br => toBracketedBinderArray br
    | none => pure $ TSyntaxArray.mk #[]
    let ctor ← `(ctor| | $nm:ident $br* : $labelTypeName)
    let actdecl : ActionDeclaration := {
      kind := toActionKind actT,
      name := name,
      ctor := ctor
    }
    /- Find the appropriate transition and add the `ActionDeclaration`
    to it Note that this DOES NOT add the `lang` representing the DSL
    code We do that by a further modification in the relevant elaborator
    (see [add_action_lang]) -/
    localSpecCtx.modify (fun s =>
      { s with spec.procedures :=
        s.spec.actions.map fun t =>
          if t.name == nm.getId then
            { t with kind := .action actdecl }
          else t})
where assertActionDeclared (nm : Name) (op : String) := do
  let actionExists := (← localSpecCtx.get).spec.actions.any fun t => t.name == nm
  if !actionExists then
    throwError "Action {nm} has not been declared (trying to {op})"

def registerProcedureBinders [Monad m] [MonadEnv m] [MonadResolveName m] [MonadError m] (nm : Name) (br : Option (TSyntax `Lean.explicitBinders)) : m Unit := do
  assertProcedureDeclared nm "registerProcedureBinders"
  localSpecCtx.modify fun s =>
    { s with spec.procedures := s.spec.procedures.map fun t =>
      if t.name == nm then
        { t with br := br }
      else t }

def registerProcedureSyntax [Monad m] [MonadEnv m] [MonadResolveName m] [MonadError m] (nm : Name) (lang : TSyntax `Lean.Parser.Term.doSeq) : m Unit := do
  assertProcedureDeclared nm "registerProcedureSyntax"
  localSpecCtx.modify fun s =>
    { s with spec.procedures := s.spec.procedures.map fun t =>
      if t.name == nm then
        { t with lang := lang }
      else t }

def registerProcedureSpec [Monad m] [MonadEnv m] [MonadResolveName m] [MonadError m] (nm : Name) (spec : Option (TSyntax `Lean.Parser.Term.doSeq)) : m Unit := do
  assertProcedureDeclared nm "registerProcedureSpec"
  localSpecCtx.modify fun s =>
    { s with spec.procedures := s.spec.procedures.map fun t =>
      if t.name == nm then
        { t with spec := spec }
      else t }

/-- Given `l` : `Wp m σ ρ` (parametrised over `br`), this defines:
  - `act.genI` : internal action interpretation of the action, unsimplified
  - `act.genE` : external action interpretation of the action, unsimplified
-/
def defineProcedureGenerators (act : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (l : doSeq) : CommandElabM (Name × Name) := do
  Command.runTermElabM fun vs => do
    let funBinders ← match br with
    | some br => toFunBinderArray br
    | none => pure #[]
    let baseName := (← getCurrNamespace) ++ act.getId
    let (genIName, _genExpI) ← genGenerator vs funBinders baseName .internal l
    let (genEName, _genExpE) ← genGenerator vs funBinders baseName .external l
    return (genIName, genEName)
where
  /-- This creates a generator for the action, which takes as input the `mode`
  in which to interpret the action and returns an _unsimplified_ interpretation
  of the action under that mode. -/
  genGenerator (vs : Array Expr) (funBinders : TSyntaxArray `Lean.Parser.Term.funBinder) (baseName : Name) (mode : Mode) (l : doSeq) := do
    let genName := toGenName baseName mode
    let genl ← match mode with
    | Mode.internal => do `(fun $funBinders* => do' .internal in $l)
    | Mode.external => do `(fun $funBinders* => do' .external in $l)
    let genExp <- withDeclName genName do elabTermAndSynthesize genl none
    let wpSimp := mkIdent `wpSimp
    let ⟨genExp, _, _⟩ <- genExp.runSimp `(tactic| simp only [$wpSimp:ident])
    let genExp <- instantiateMVars <| <- mkLambdaFVarsImplicit vs genExp
    simpleAddDefn genName genExp (attr := #[{name := `generatorSimp}, {name := `actSimp}, {name := `reducible}])
    return (genName, genExp)

def defineInitialActionFromGenerators (act : TSyntax `ident) (genIName genEName : Name) : CommandElabM Unit := do
    Command.runTermElabM fun _ => do
      -- Create binders and arguments
      let baseName := (← getCurrNamespace) ++ act.getId
      let _actIName ← genInitialAction baseName .internal genIName
      let _actEName ← genInitialAction baseName .external genEName
where
  /-- This generates the 'simplified' (fully unfolded) action interpretation,
  assuming the generator for this `mode` has already been defined and can be
  found in the environment with name `genName`. -/
  genInitialAction (baseName : Name) (mode : Mode) (genName : Name) := do
    let actName := match mode with
    | Mode.internal => baseName
    | Mode.external => toExtName baseName
    let genExp := Lean.mkConst genName
    let act ← genExp |>.runUnfold (genName :: wpUnfold)
    let ⟨act, _actPf, _⟩ <- act.runSimp `(tactic| simp only [actSimp, logicSimp, smtSimp, quantifierSimp])
    let mut attr : Array Attribute := #[{name := `initSimp}, {name := `actSimp}]
    simpleAddDefn actName act (attr := attr) («type» := ← inferType genExp)
    return actName

/-- Defines `act` : `Wp m σ ρ` monad computation, parametrised over `br`. This
assumes that `act.genE` and `act.genI` have already been defined. Specifically
it defines:
  - `act.ext` : external action interpretation of the action, simplified
  - `act` : internal action interpretation (for procedure calls) of the action, simplified
  - `act.tr` : (external) transition of the action, with existentially quantified arguments
-/
def defineActionFromGenerators (actT : TSyntax `actionKind) (act : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (genIName genEName : Name) (generateTransition : Bool := true): CommandElabM Unit := do
    let vd ← getImplicitProcedureParameters
    declareProcedure (toActionKind actT) act.getId
    registerIOActionDecl actT act br
    registerProcedureBinders act.getId br
    Command.runTermElabM fun vs => do
      -- Create binders and arguments
      let sectionArgs ← getSectionArgumentsStx vs
      let baseName := (← getCurrNamespace) ++ act.getId
      let (_actIName, actIPf) ← genAction baseName .internal genIName
      let (_actEName, actEPf) ← genAction baseName .external genEName
      if generateTransition then
        genTransition vs sectionArgs baseName
        if veil.gen_sound.get <| <- getOptions then
          genSoundness vd vs br baseName actIPf actEPf
where
  /-- This generates the 'simplified' (fully unfolded) action interpretation,
  assuming the generator for this `mode` has already been defined and can be
  found in the environment with name `genName`. -/
  genAction (baseName : Name) (mode : Mode) (genName : Name) := do
    let actName := match mode with
    | Mode.internal => baseName
    | Mode.external => toExtName baseName
    let genExp := Lean.mkConst genName
    -- Here, to account for the case when the action is generated from a transition,
    -- we also unfold `Function.toWp` and the original definition of the transition.
    let origName := toOriginalName baseName
    let act ← genExp |>.runUnfold (genName :: wpUnfold)
    let act ← act |>.runUnfold [``Function.toWp, origName]
    let ⟨act, actPf, _⟩ <- act.runSimp `(tactic| simp only [actSimp, logicSimp, smtSimp, quantifierSimp])
    let mut attr : Array Attribute := #[{name := `actSimp}]
    simpleAddDefn actName act (attr := attr) («type» := ← inferType genExp)
    return (actName, actPf)

  /-- This generates a two-state transition from the action, with existentially
  quantified arguments. -/
  genTransition (vs : Array Expr) (sectionArgs : Array (TSyntax `term)) (baseName : Name) := do
    let args  ← match br with
      | some br => explicitBindersIdents br
      | none => pure #[]
    let (genName, actTrName) := (toGenName baseName .external, toTrName baseName)
    let actTrStx <- `(fun st st' => exists? $br ?, (@$(mkIdent genName) $sectionArgs* $args*).toTwoState st st')
    let actTr <- elabTermAndSynthesize actTrStx none
    -- For transitions that are lifted from a dependency (i.e. run through
    -- `.toWp.lift.toTwoState`), simplifying the definitions leads to a
    -- transition that existentially quantifies over the state of the
    -- dependency, which is bad. Instead, we apply the `lift_transition`
    -- theorem, giving us a nicer lifted transition.
    let ⟨actTr, _, _⟩ <- actTr.runSimp `(tactic| simp only [$(mkIdent `generatorSimp):ident, setIn, getFrom, lift_transition])
    -- After (potentially) `lift_transition` theorem, we simplify as usual
    let ⟨actTr, _, _⟩ <- actTr.runSimp `(tactic| simp only [actSimp, logicSimp, smtSimp, quantifierSimp])
    let actTr <- mkLambdaFVarsImplicit vs actTr
    let actTr <- instantiateMVars actTr
    simpleAddDefn actTrName actTr (attr := #[{name := `actSimp}])

  /-- This generates type class instances that are required to prove the
  _soundness_ of the translation of the imperative action into the two-state
  transition. This can be expensive, so it is off by default. -/
  genSoundness (vd : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) (vs : Array Expr) (br : Option (TSyntax `Lean.explicitBinders)) (baseName : Name) (actIPf actEPf : Option Expr) := do
    let (actTrName, genEName, genIName, actEName, actIName) := (toTrName baseName, toGenName baseName .external, toGenName baseName .internal, toExtName baseName, baseName)
    let sectionArgs ← getSectionArgumentsStx vs
    let (univBinders, args) ← match br with
      | some br => pure (← toBracketedBinderArray br, ← explicitBindersIdents br)
      | none => pure (#[], #[])

    let actTrStx <- `(fun st st' => exists? $br ?, (@$(mkIdent actEName) $sectionArgs* $args*).toTwoState st st')
    let trActThmStatement ← `(forall? $[$vd]* , ($actTrStx) = (@$(mkIdent actTrName) $sectionArgs*))
    let trActThm ← elabTermAndSynthesize trActThmStatement mkProp
    let ⟨afterSimp, thmPf, _⟩ <- trActThm.runSimp `(tactic| simp only [actSimp, logicSimp, smtSimp, quantifierSimp])
    if !afterSimp.isTrue then
      throwError "[genSoundness] {trActThmStatement} could not be proven by `simp`"
    let proof ← match thmPf with
    | some thmPf => mkAppM ``of_eq_true #[thmPf]
    | none => mkEqRefl trActThm -- `simp` returns no proof if the statement is true by reflexivity

    addDecl <| Declaration.thmDecl <| mkTheoremValEx (toActTrEqName baseName) [] trActThm proof []

    let genSoundnessInstance (mode : Mode) (genName actName : Name) (vd : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) (univBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) (sectionArgs args : Array (TSyntax `term)) (actPf : Option Expr) := do
      let instTp <- `(forall? $[$vd]* $univBinders*, LawfulAction (@$(mkIdent genName):ident $sectionArgs* $args*))
      let instTp <- elabTermAndSynthesize instTp none
      simpleAddThm (toGenInstName baseName mode) instTp `(tacticSeq| intros; infer_instance) (attr := #[{name := `instance}])

      let eqTp <- `(@$(mkIdent genName) = @$(mkIdent actName))
      let eqTp <- elabTermAndSynthesize eqTp none
      let eq <- ensureHasType eqTp <| actPf.getD <| <- mkAppM ``Eq.refl #[mkConst actName]
      let eq <- Term.exprToSyntax eq

      let instTp <- `(forall? $[$vd]* $univBinders*, LawfulAction (m := $(← mode.stx)) (@$(mkIdent actName):ident $sectionArgs* $args*))
      let instTp <- elabTermAndSynthesize instTp none
      simpleAddThm (toInstName baseName mode) instTp
        `(tacticSeq|
          have h : @$(mkIdent genName) = @$(mkIdent actName) := $eq
          rw [<-h]; intros; infer_instance) (attr := #[{name := `instance}])

    genSoundnessInstance .external genEName actEName vd univBinders sectionArgs args actEPf
    genSoundnessInstance .internal genIName actIName vd univBinders sectionArgs args actIPf

def defineProcedureFromGenerator (proc : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (genIName : Name) : CommandElabM Unit := do
    declareProcedure .none proc.getId
    registerProcedureBinders proc.getId br
    Command.runTermElabM fun _ => do
      let baseName := (← getCurrNamespace) ++ proc.getId
      let _ ← genProcedure baseName genIName
where
  /-- This generates the 'simplified' (fully unfolded) action interpretation,
  assuming the internal generator has already been defined and can be
  found in the environment with name `genName`. -/
  genProcedure (baseName : Name) (genIName : Name) := do
    let procName := baseName
    let genExp := Lean.mkConst genIName
    let act ← genExp |>.runUnfold (genIName :: wpUnfold)
    let act ← act |>.runUnfold [``Function.toWp]
    let ⟨act, actPf, _⟩ <- act.runSimp `(tactic| simp only [actSimp, logicSimp, smtSimp, quantifierSimp])
    let mut attr : Array Attribute := #[{name := `actSimp}]
    simpleAddDefn procName act (attr := attr) («type» := ← inferType genExp)
    return (procName, actPf)

/-- Defines `act` : `Wp m σ ρ` monad computation, parametrised over `br`. More
specifically it defines:
  - `act.genI` : internal action interpretation of the action, unsimplified
  - `act.genE` : external action interpretation of the action, unsimplified

  - `act.ext` : external action interpretation of the action, simplified
  - `act` : internal action interpretation (for procedure calls) of the action, simplified
  - `act.tr` : (external) transition of the action, with existentially quantified arguments
-/
def defineAction (actT : TSyntax `actionKind) (act : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (l : doSeq) : CommandElabM Unit := do
  let (genIName, genEName) ← defineProcedureGenerators act br l
  defineActionFromGenerators actT act br genIName genEName
  registerProcedureSyntax act.getId l

def defineProcedure (proc : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (l : doSeq) : CommandElabM Unit := do
  let (genIName, _genEName) ← defineProcedureGenerators proc br l
  defineProcedureFromGenerator proc br genIName
  registerProcedureSyntax proc.getId l

/-- We support executing actions from dependent modules is by `monadLift`ing
them to the current module's state. This function generates the
`IsSubStateOf` instances required to do this. -/
def genStateExtInstances : CommandElabM Unit := do
  let currName <- getCurrNamespace
  let vd := (<- getScope).varDecls
  let insts <- Command.runTermElabM fun vs => do
    let mut insts := #[]
    for (modAlias, dep) in (<- localSpecCtx.get).spec.dependencies do
      let ts ← dep.stateArguments
      let currTs <- getStateArgumentsStx vd vs
      let alia := mkIdent modAlias
      let stateExtTypeclass := mkIdent ``IsSubStateOf
      let inst <-
        `(@[actSimp]
          instance :
           $stateExtTypeclass
             (@$(mkIdent $ dep.name ++ `State) $ts*)
             (@$(mkIdent $ currName ++ `State) $currTs*) where
            setIn := fun s s' => { s' with $alia:ident := s }
            getFrom := fun s' => s'.$alia
            setIn_getFrom_idempotent := by intros; dsimp only
            getFrom_setIn_idempotent := by intros; dsimp only)
      insts := insts.push inst
    return insts
  for inst in insts do
    trace[veil.debug] "Generating state extension instance {inst}"
    elabCommand inst
    trace[veil.info] "State extension instance is defined"

-- def baz (n  q: Nat) := @monadLift (Wlp Mode.internal (Test₁.State node')) (Wlp Mode.internal (State node' node'')) _ Unit (@Test₁.f.genI node' node'_dec node'_ne n q)
def liftProcedureGenerators (forAct : TSyntax `ident) (withBinders : Option (TSyntax `Lean.explicitBinders)) (stateTpT : TSyntax `term) (fromBaseGenerator : Name) (instatiatedWithArgs : Array Term) (isInitialAction : Bool := false) : CommandElabM (Name × Name) := do
  Command.runTermElabM fun vs => do
    let baseName := (← getCurrNamespace) ++ forAct.getId
    let (genIName, _genExpI) ← liftGenerator baseName vs withBinders fromBaseGenerator instatiatedWithArgs .internal isInitialAction
    let (genEName, _genExpE) ← liftGenerator baseName vs withBinders fromBaseGenerator instatiatedWithArgs .external isInitialAction
    return (genIName, genEName)
where
  liftGenerator (liftedActName : Name) (actVs : Array Expr) (actBinders :  Option (TSyntax `Lean.explicitBinders)) (baseNameToLift : Name) (depArgs : Array Term) (mode : Mode) (isInitialAction : Bool)  := do
    let baseGenName := toGenName baseNameToLift mode
    let (actParams, actArgs) ← match actBinders with
    | some br => pure (← toFunBinderArray br, ← explicitBindersIdents br)
    | none => pure (#[], #[])
    let infer ← `(term|_)
    let (srcWpType, typeClassInst, retType) := (infer, infer, infer)
    -- e.g. `Wp Mode.internal (State node' node'')`
    let dstWpType ← `(term|Wp $(← mode.stx) ($stateTpT))
    let liftedGenStx ← `(fun $actParams* => @monadLift $srcWpType $dstWpType $typeClassInst $retType <| @$(mkIdent baseGenName) $depArgs* $actArgs*)
    let liftedGenName := toGenName liftedActName mode
    trace[veil.info] "{liftedGenName} := {liftedGenStx}"
    let genExp <- withDeclName liftedGenName do elabTermAndSynthesize liftedGenStx .none
    let wpSimp := mkIdent `wpSimp
    let ⟨genExp, _, _⟩ <- genExp.runSimp `(tactic| simp only [$wpSimp:ident])
    let genExp <- instantiateMVars <| <- mkLambdaFVarsImplicit actVs genExp
    let initAttr := if isInitialAction then #[{name := `initSimp}] else #[]
    simpleAddDefn liftedGenName genExp (attr := #[{name := `generatorSimp}, {name := `actSimp}, {name := `reducible}] ++ initAttr)
    return (liftedGenName, genExp)

def defineDepsProcedures : CommandElabM Unit := do
  let stateTpT ← liftCoreM $ getStateTpStx
  for (modAlias, dependency) in (<- localSpecCtx.get).spec.dependencies do
    -- arguments with which the dependency was instantiated
    let depArgs := dependency.arguments
    let globalCtx <- globalSpecCtx.get
    let some depCtx := globalCtx[dependency.name]? | throwError "Module {dependency.name} is not declared"
    -- Lift initializer
    let initName := dependency.name ++ `initializer
    let liftedName := mkIdent <| modAlias ++ (stripFirstComponent initName)
    trace[veil.info] "lifting {initName} from module {dependency.name} to module {← specName} as {liftedName}"
    let (genIName, genEName) ← liftProcedureGenerators liftedName .none stateTpT initName depArgs (isInitialAction := true)
    defineInitialActionFromGenerators liftedName genIName genEName
    -- Lift actions
    for procToLift in depCtx.spec.procedures do
      let procBaseName := dependency.name ++ procToLift.name
      -- If an action has a pre-post specification, we use the the specification
      -- instead of the action itself as the lifted action. Recall that
      -- specification are just `action`s` themselves. In particular they have
      -- `genE` and `genI` generators that we can use to lift the action.
      let actBaseName := if procToLift.hasSpec then toSpecName procBaseName else procBaseName
      let liftedName := mkIdent <| modAlias ++ (stripFirstComponent actBaseName)
      -- When we lift an action from a dependency, the binders of the action
      -- may have types that are not syntactically present in the action's
      -- signature. We have to substitute the types with the arguments of the
      -- dependency instantiation. We cannot use `_` to infer the types, since
      -- we use these type arguments to construct the `Label` type, so they
      -- must be explicit.
      let liftedBinders ← do match procToLift.br with
        | some br => pure (Option.some (← toBindersWithMappedTypes br (← dependency.typeMapping)))
        | none => pure .none
      trace[veil.info] "lifting {procToLift.kindString} {actBaseName} from module {dependency.name} to module {← specName} as {liftedName}"
      let (genIName, genEName) ← liftProcedureGenerators liftedName liftedBinders stateTpT actBaseName depArgs
      match procToLift.kind with
      | .action decl =>
        let actionKind ← decl.kind.stx
        defineActionFromGenerators actionKind liftedName liftedBinders genIName genEName
      | .procedure _ => defineProcedureFromGenerator liftedName liftedBinders genIName

/-- Given `tr` : `σ → σ → Prop` (parametrised over `br`), this defines:
  - `tr.genI` : internal action interpretation of the action, unsimplified
  - `tr.genE` : external action interpretation of the action, unsimplified

  This is used to re-cast a transition as an action.
-/
def defineTransition (actT : TSyntax `actionKind) (nm : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (tr : Term) : CommandElabM Unit := do
  let vd ← getImplicitProcedureParameters
  let baseName := (← getCurrNamespace) ++ nm.getId
  let (origName, trName) := (toOriginalIdent nm, toTrIdent nm)
  let (originalDef, trDef) ← Command.runTermElabM fun vs => do
    let stateTpT ← getStateTpStx
    let trType <- `($stateTpT -> $stateTpT -> Prop)
    let sectionArgs ← getSectionArgumentsStx vs
    let (univBinders, args) ← match br with
    | some br => pure (← toBracketedBinderArray br, ← explicitBindersIdents br)
    | none => pure (#[], #[])
    -- We keep the original definition of the transition, as given by the user.
    let originalDef ← `(@[actSimp] def $origName $[$vd]* $univBinders* : $trType := $tr)
    -- We also define a `.tr` version, with existentially quantified arguments.
    -- We do this "manually" rather than reusing the code in `defineActionFromGenerators`
    -- since our conversion to `Wp` increases the size of the formula.
    let trDef ← do
      let (st, st') := (mkIdent `st, mkIdent `st')
      let rhs ← match br with
      | some br => `(fun ($st $st' : $stateTpT) => ∃ $br, @$origName $sectionArgs* $args* $st $st')
      | none => `(fun ($st $st' : $stateTpT) => @$origName $sectionArgs* $args* $st $st')
      `(@[actSimp] def $trName $[$vd]* : $trType := $(← unfoldWp rhs))
    return (originalDef, trDef)
  trace[veil.info] "{originalDef}"
  elabCommand originalDef
  trace[veil.info] "{trDef}"
  elabCommand trDef
  let (genIName, genEName) ← Command.runTermElabM fun vs => do
    let (genIName, _genExpI) ← genGeneratorFromTransition vs origName baseName .internal
    let (genEName, _genExpE) ← genGeneratorFromTransition vs origName baseName .external
    return (genIName, genEName)
  -- We don't generate the transition based on `Wp`, since we already have it from the user.
  defineActionFromGenerators actT nm br genIName genEName (generateTransition := false)
where
  genGeneratorFromTransition (vs : Array Expr) (origName : Ident) (baseName : Name) (mode : Mode) := do
    let genName := toGenName baseName mode
    let sectionArgs ← getSectionArgumentsStx vs
    let (funBinders, args) ← match br with
    | some br => pure (← toFunBinderArray br, ← explicitBindersIdents br)
    | none => pure (#[], #[])
    let term ← match mode with
    | Mode.internal => `((@$origName $sectionArgs* $args*).toWp .internal)
    | Mode.external => `((@$origName $sectionArgs* $args*).toWp .external)
    let genl ← `(fun $funBinders* => $term)
    let genExp <- withDeclName genName do elabTermAndSynthesize genl none
    -- let wpSimp := mkIdent `wpSimp
    -- let ⟨genExp, _, _⟩ <- genExp.runSimp `(tactic| simp only [$wpSimp:ident])
    let genExp <- instantiateMVars <| <- mkLambdaFVarsImplicit vs genExp
    simpleAddDefn genName genExp (attr := #[{name := `generatorSimp}, {name := `actSimp}, {name := `reducible}]) («type» := ← inferType genExp)
    return (genName, genExp)
