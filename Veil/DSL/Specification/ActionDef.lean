import Lean

import Veil.DSL.Action.Lang
import Veil.DSL.Tactic
import Veil.DSL.Specification.Syntax
import Veil.DSL.Specification.SpecDef
import Veil.Util.TermSimp

open Lean Elab Command Term Meta Lean.Parser

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
  let vd ← getActionParameters
  let labelTypeName := mkIdent `Label
  let labelTypeArgs ← bracketedBindersToTerms $ ← (← localSpecCtx.get).spec.generic.applyGetStateArguments vd
  let labelT ← `(term|$labelTypeName $labelTypeArgs*)
  Command.runTermElabM fun _ => do
    let name := nm.getId
    let br ← match br with
    | some br => toBracketedBinderArray br
    | none => pure $ TSyntaxArray.mk #[]
    let ctor ← `(ctor| | $nm:ident $br* : $labelT)
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

def defineProcedure (act : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (l : doSeq) : CommandElabM (Name × Name) := do
  Command.runTermElabM fun vs => do
    let funBinders ← match br with
    | some br => toFunBinderArray br
    | none => pure #[]
    let baseName := (← getCurrNamespace) ++ act.getId
    let (genIName, _genExpI) ← genGenerator vs funBinders baseName .internal l
    let (genEName, _genExpE) ← genGenerator vs funBinders baseName .external l
    return (genIName, genEName)
  where
    genGenerator (vs : Array Expr) (funBinders : TSyntaxArray `Lean.Parser.Term.funBinder) (baseName : Name) (mode : Mode) (l : doSeq) := do
      let genName := toActName baseName mode
      let genl ← match mode with
      | Mode.internal => do `(fun $funBinders* => do' .internal as $genericReader, $genericState in $l)
      | Mode.external => do `(fun $funBinders* => do' .external as $genericReader, $genericState in $l)
      try
        withoutErrToSorry $ do
        let genExp <- withDeclName genName do elabTermAndSynthesize genl none
        let ⟨genExp, _, _⟩ <- genExp.simpAction
        let genExp <- instantiateMVars <| <- mkLambdaFVarsImplicit vs genExp
        simpleAddDefn genName genExp (attr := #[{name := `generatorSimp}, {name := `actSimp}, {name := `reducible}])
        return (genName, genExp)
      catch ex =>
        trace[veil.debug] "Error generating {mode} generator for {genName}: {← ex.toMessageData.toString}"
        -- We have this as a more user-readable message
        throwError "Error in action {baseName}: {← ex.toMessageData.toString}"

/-- Defines a function and simplifies it using `simp` with the given simp lemma and simp sets. -/
def defineAndSimplify (vs : Array Expr)
  (defName : Name)
  (defStx : Array Term -> Array Term -> TermElabM Term)
  (unfolds : List Name)
  (simps : Array Name)
  (br : Option (TSyntax `Lean.explicitBinders)) := do
    let sectionArgs ← getSectionArgumentsStx vs
    let args ← match br with
      | some br => pure (← explicitBindersIdents br)
      | none => pure #[]
    let actStx <- defStx sectionArgs args
    let mut actExp <- elabTermAndSynthesize actStx none
    unless unfolds.isEmpty do
      actExp <- actExp.runUnfold unfolds
    let ⟨act, actPf, _⟩ <- actExp.simp simps
    let act <- mkLambdaFVarsImplicit vs act
    let act <- instantiateMVars act
    simpleAddDefn defName act (attr := #[{name := `actSimp}])
    return (defName, actPf)

partial
def Lean.Expr.removeFunExt (limit : Int) (actPf : Expr)  : MetaM Expr := do
  if limit > 0 then
    match_expr actPf with
    | funext _ _ _ _ h =>
      match h.consumeMData with
      | .lam n tp bd inf  =>
        return Expr.lam n tp (← removeFunExt (limit - 1) bd) inf
      | _ => throwError "Expected a function extensionality lemma"
    | _ => return actPf
  else return actPf

/-- Defines the weakest precondition for the action, generalised over the exception handler. -/
def defineWpForAction (vs : Array Expr)
  (actName : Name) (br : Option (TSyntax `Lean.explicitBinders)) : TermElabM
  (Name × Option Expr) :=
  defineAndSimplify vs (toWpName actName) (fun sectionArgs args => `(fun hd $args* post =>
    [CanRaise hd| wp (@$(mkIdent actName) $sectionArgs* $args*) post]))
    [] #[`wpSimp, actName, `smtSimp, `quantifierSimp] br

/-- Defines the weakest precondition for the action specialised to the case where the
  exception handler is `True`. -/
def defineWpSuccForAction (vs : Array Expr)
  (actName : Name) (br : Option (TSyntax `Lean.explicitBinders)) : TermElabM
  (Name × Option Expr) :=
  let actWpName := toWpName actName
  let actWpSuccName := toWpSuccName actName
  defineAndSimplify vs actWpSuccName (fun sectionArgs args => `(fun $args* post =>
      @$(mkIdent actWpName) $sectionArgs* (fun _ => True) $args* post))
    [actWpName] #[``if_true_right] br

/-- Defines the weakest precondition for the action specialised to the case where the
  exception handler allows all exceptions except the one given. -/
def defineWpExForAction (vs : Array Expr)
  (actName : Name) (br : Option (TSyntax `Lean.explicitBinders)) : TermElabM
  (Name × Option Expr) :=
  let actWpName := toWpName actName
  let actWpExName := toWpExName actName
  defineAndSimplify vs actWpExName (fun sectionArgs args => `(fun ex $args* post =>
    @$(mkIdent actWpName) $sectionArgs* (· ≠ ex) $args* post))
    [actWpName] #[] br

def defineTwoStateAction (vs : Array Expr)
  (actName : Name) (br : Option (TSyntax `Lean.explicitBinders)) :
  TermElabM (Name × Option Expr) := do
  let actWpSuccName := toWpSuccName actName
  let actTwoStateName := toTwoStateName actName
  defineAndSimplify vs actTwoStateName (fun sectionArgs args => `(
    fun $args* =>
      VeilSpecM.toTwoStateDerived <| @$(mkIdent actWpSuccName) $sectionArgs* $args*))
    [actWpSuccName, ``VeilSpecM.toTwoStateDerived, ``Cont.inv] #[] br
    --#[``Pi.compl_def, ``compl] br

def defineTr (vs : Array Expr)
  (actName : Name) (br : Option (TSyntax `Lean.explicitBinders)) :
  TermElabM (Name × Option Expr) := do
  let actTrName := toTrName actName
  let actTwoStateName := toTwoStateName actName
  defineAndSimplify vs actTrName (fun sectionArgs args => `(
    fun r s s' =>
      exists? $br ?, @$(mkIdent actTwoStateName) $sectionArgs* $args* r s s'))
    [actTwoStateName] #[] br

def defineEqLemma
  (vs : Array Expr)
  (vd : Array (TSyntax ``Term.bracketedBinder))
  (lemmaName : Name)
  (lemmaStx :
    Array (TSyntax ``Term.bracketedBinder) ->
    Array (TSyntax ``Term.bracketedBinder) ->
    Array Term -> Array Term -> TermElabM Term)
  (lemmaProof : Option Expr)
  (offset : Option Int)
  (br : Option (TSyntax `Lean.explicitBinders)) : TermElabM Unit := do
  let sectionArgs ← getSectionArgumentsStx vs
  let (univBinders, args) ← match br with
    | some br => pure (← toBracketedBinderArray br, ← explicitBindersIdents br)
    | none => pure (#[], #[])
  let lemmaStx <- lemmaStx vd univBinders sectionArgs args
  let lemmaExpr <- elabTermAndSynthesize lemmaStx none
  let proof ← match lemmaProof with
  | some lemmaProof =>
    let lemmaProof <- lemmaProof.removeFunExt (offset.map (· + 1 + (args.size : Int)) |>.getD 0)
    instantiateMVars <| <- mkLambdaFVarsImplicit vs lemmaProof
  | none => elabTermAndSynthesize (<- `(by intros; rfl)) lemmaExpr -- `simp` returns no proof if the statement is true by reflexivity
  let declName := lemmaName
  addDecl <| Declaration.thmDecl <| mkTheoremValEx declName [] lemmaExpr proof []
  enableRealizationsForConst declName
  applyAttributes declName #[{name := `wpSimp}]

def defineWpLemma (vs : Array Expr)
  (vd : Array (TSyntax ``Term.bracketedBinder))
  (actName : Name) (actWpName : Name)
  (actPf : Option Expr)
  (br : Option (TSyntax `Lean.explicitBinders)) : TermElabM Unit := do
  defineEqLemma vs vd
    (toWpLemmaName actName)
    (fun vd univBinders sectionArgs args =>
    `(forall $vd* hd $univBinders* post,
      [CanRaise hd| wp (@$(mkIdent actName) $sectionArgs* $args*) post =
      @$(mkIdent actWpName) $sectionArgs* hd $args* post]))
    actPf
    (some 1)
    br

def defineWpSuccLemma (vs : Array Expr)
  (vd : Array (TSyntax ``Term.bracketedBinder))
  (actName : Name) (actWpSuccName : Name)
  (actWpName : Name)
  (actWpSuccPf : Option Expr)
  (br : Option (TSyntax `Lean.explicitBinders)) : TermElabM Unit := do
  defineEqLemma vs vd
    (toWpSuccLemmaName actName)
    (fun vd univBinders sectionArgs args =>
      `(forall $vd* $univBinders* post,
        @$(mkIdent actWpName) $sectionArgs* (fun _ => True) $args* post =
        @$(mkIdent actWpSuccName) $sectionArgs* $args* post))
    actWpSuccPf
    (some 0)
    br

def defineWpExLemma (vs : Array Expr)
  (vd : Array (TSyntax ``Term.bracketedBinder))
  (actName : Name)
  (actWpName : Name)
  (actWpExName : Name)
  (actWpExPf : Option Expr)
  (br : Option (TSyntax `Lean.explicitBinders)) : TermElabM Unit := do
  defineEqLemma vs vd
    (toWpExLemmaName actName)
    (fun vd univBinders sectionArgs args =>
      `(forall $vd* ex $univBinders* post,
        @$(mkIdent actWpName) $sectionArgs* (· ≠ ex) $args* post =
        @$(mkIdent actWpExName) $sectionArgs* ex $args* post))
    actWpExPf
    (some 1)
    br

def defineTwoStateLemma (vs : Array Expr)
  (vd : Array (TSyntax ``Term.bracketedBinder))
  (actName : Name) (actTwoStateName : Name)
  (actTwoStatePf : Option Expr)
  (br : Option (TSyntax `Lean.explicitBinders)) : TermElabM Unit := do
  let actWpSuccName := toWpSuccName actName
  let actTwoStateLemmaName := toTwoStateLemmaName actName
  defineEqLemma vs vd actTwoStateLemmaName (fun vd univBinders sectionArgs args =>
    `(forall $vd* $univBinders*,
       VeilSpecM.toTwoStateDerived
         (@$(mkIdent actWpSuccName) $sectionArgs* $args*) =
      @$(mkIdent actTwoStateName) $sectionArgs* $args*))
    actTwoStatePf
    (some $ -1)
    br

def defineTrLemma (vs : Array Expr)
  (vd : Array (TSyntax ``Term.bracketedBinder))
  (actName : Name) (actTrName : Name)
  (actTrPf : Option Expr)
  (br : Option (TSyntax `Lean.explicitBinders)) : TermElabM Unit := do
  let actTwoStateName := toTwoStateName actName
  let actTrLemmaName := toTrLemmaName actName
  defineEqLemma vs vd actTrLemmaName (fun vd _univBinders sectionArgs args =>
    `(forall $vd*,
      @$(mkIdent actTrName) $sectionArgs* =
      fun r s s' => exists? $br ?, @$(mkIdent actTwoStateName) $sectionArgs* $args* r s s'))
    actTrPf
    none
    br

inductive DeclType : Type where
  | proc
  | act
  | init
deriving DecidableEq

def defineAuxiliaryDeclarations (declType : DeclType) (actName : Name) (br : Option (TSyntax `Lean.explicitBinders)) := do
  let vd ← getImplicitProcedureParameters
  runTermElabM fun vs => do
    let (actWpName, actWpPf) ← defineWpForAction vs actName br
    defineWpLemma vs vd actName actWpName actWpPf br

    unless declType = DeclType.proc do
      let (actWpSuccName, actWpSuccPf) ← defineWpSuccForAction vs actName br
      defineWpSuccLemma vs vd actName actWpSuccName actWpName actWpSuccPf br

      unless declType = DeclType.init do
        let (actWpExName, actWpExPf) ← defineWpExForAction vs actName br
        defineWpExLemma vs vd actName actWpName actWpExName actWpExPf br

      let (actTwoStateName, actTwoStatePf) ← defineTwoStateAction vs actName br
      defineTwoStateLemma vs vd actName actTwoStateName actTwoStatePf br

      let (actTrName, actTrPf) ← defineTr vs actName br
      defineTrLemma vs vd actName actTrName actTrPf br

def registerAction (actT : TSyntax `actionKind) (act : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (l : doSeq) := do
  declareProcedure (toActionKind actT) act.getId
  registerIOActionDecl actT act br
  registerProcedureBinders act.getId br
  registerProcedureSyntax act.getId l

def registerProcedure (proc : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (l : doSeq) :
  CommandElabM Unit := do
  declareProcedure .none proc.getId
  registerProcedureBinders proc.getId br
  registerProcedureSyntax proc.getId l


/-- Defines `act` : `VeilM m ρ σ α` monad computation, parametrised over `br`. More
specifically it defines:
  - `act.ext` : external action interpretation of the action, simplified
  - `act` : internal action interpretation (for procedure calls) of the action, simplified
  - `act.ext.gen_wp` : simplified weakest precondition for the external action interpretation
    generalised over the exception handler
  - `act.gen_wp` : simplified weakest precondition for the internal action interpretation
    generalised over the exception handler
  - `act.ext.wp.eq` : equality between the weakest precondition for the external action interpretation and
     its simplified version
  - `act.wp.eq` : equality between the weakest precondition for the internal action interpretation and
    its simplified version
-/
def defineAction (actT : TSyntax `actionKind) (act : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (l : doSeq) : CommandElabM Unit := do
  let (actIntName, actExtName) ← defineProcedure act br l
  defineAuxiliaryDeclarations DeclType.act actExtName br
  defineAuxiliaryDeclarations DeclType.act actIntName br
  registerAction actT act br l

def defineInitialAction (l : doSeq) : CommandElabM Unit := do
  let initName := mkIdent initializerName
  let (_, actExtName) ← defineProcedure initName none l
  defineAuxiliaryDeclarations DeclType.init actExtName none


-- def defineProcedure (proc : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (l : doSeq) : CommandElabM (Name × Name) := do
--   let (actExtName, actIntName) ← defineProcedure act br l
--   defineAuxiliaryDeclarations DeclType.act actExtName br
--   defineAuxiliaryDeclarations DeclType.act actIntName br
--   registerAction actT act br l

/- TODO: fix state extension instances
/-- We support executing actions from dependent modules by executing
them on the current module's state. This function generates the
`IsSubStateOf` instances required to do this. -/
def genStateExtInstances : CommandElabM Unit := do
  let currName <- getCurrNamespace
  let insts <- Command.runTermElabM fun _ => do
    let mut insts := #[]
    for (modAlias, dep) in (<- localSpecCtx.get).spec.dependencies do
      let ts ← dep.applyGetStateArguments dep.arguments
      let currTs <- getStateTpArgsStx
      let alia := mkIdent modAlias
      let stateExtTypeclass := mkIdent ``IsSubStateOf
      let instName := subStateInstIdent alia
      -- Prove sub-state is a sub-state of the current state
      let inst <-
        `(@[actSimp]
          def $instName:ident :
           $stateExtTypeclass
             (@$(mkIdent $ dep.name ++ `State) $ts*)
             (@$(mkIdent $ currName ++ `State) $currTs*) where
            setIn := fun s s' => { s' with $alia:ident := s }
            getFrom := fun s' => s'.$alia
            setIn_getFrom_idempotent := by intros; dsimp only
            getFrom_setIn_idempotent := by intros; dsimp only)
      insts := insts.push inst
      -- Create an instance showing that the sub-state is of the
      -- generic state type `σ`
      let transInstName := subStateInstIdent' alia genericState
      let transInst ← `(command|@[actSimp] def $transInstName := IsSubStateOf.trans ($instName $currTs*) $genericSubStateIdent)
      insts := insts.push transInst
    return insts
  for inst in insts do
    trace[veil.debug] "Generating state extension instance:\n{inst}"
    elabCommand inst
    trace[veil.info] "State extension instance is defined"

/- TODO: fix -/
def liftAction (liftedName : TSyntax `ident) (originalName : TSyntax `ident) (instatiatedWithArgs : Array Term) (σ instSubState : Term)  : CommandElabM Unit := do
  let params ← getImplicitProcedureParameters
  let stx ← `(command|@[actSimp]def $liftedName $params* := @$originalName $instatiatedWithArgs* $σ $instSubState)
  trace[veil.debug] "Lifting action {liftedName} to {liftedName}:\n{stx}"
  elabCommand stx

/- TODO: fix -/
def defineDepsProcedures : CommandElabM Unit := do
  for (modAlias, dependency) in (<- localSpecCtx.get).spec.dependencies do
    -- arguments with which the dependency was instantiated
    let depArgs := dependency.arguments
    let globalCtx <- globalSpecCtx.get
    let some depCtx := globalCtx[dependency.name]? | throwError "Module {dependency.name} is not declared"
    -- Lift initializer
    let initName := mkIdent $ dependency.name ++ `initializer
    let liftedName := mkIdent $ modAlias ++ (stripFirstComponent initName.getId)
    -- trace[veil.info] "lifting {initName} from module {dependency.name} to module {← specName} as {liftedName}"
    let subStateInst ← Command.runTermElabM fun _ => do
      let subStateInstName := subStateInstIdent' (mkIdent modAlias) genericState
      return ← `(term|@$subStateInstName $(← getStateTpArgsStx)* $genericState _)
    liftAction liftedName initName depArgs genericState subStateInst
    -- Lift actions
    for procToLift in depCtx.spec.procedures do
      let procBaseName := mkIdent $ dependency.name ++ procToLift.name
      let liftedName := mkIdent <| modAlias ++ (stripFirstComponent procBaseName.getId)
      liftAction liftedName procBaseName depArgs genericState subStateInst
-/
#exit

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
    try
      let act ← genExp |>.runUnfold (genName :: wpUnfold)
      let ⟨act, _actPf, _⟩ <- act.simpAction
      let mut attr : Array Attribute := #[{name := `initSimp}, {name := `actSimp}]
      simpleAddDefn actName act (attr := attr) («type» := ← inferType genExp)
      return actName
    catch ex =>
      trace[veil.debug] "Error generating {mode} initial action {actName} (from generator {genName}): {← ex.toMessageData.toString}"
      throwError "Error in action {baseName}: {← ex.toMessageData.toString}"

/-- Defines `act` : `Wp m ρ σ` monad computation, parametrised over `br`. This
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
    let origName := toFnName baseName
    try
      withoutErrToSorry $ do
      let act ← genExp |>.runUnfold (genName :: wpUnfold)
      let act ← act |>.runUnfold [``Function.toWp, origName]
      let ⟨act, actPf, _⟩ <- act.simpAction
      let mut attr : Array Attribute := #[{name := `actSimp}]
      simpleAddDefn actName act (attr := attr) («type» := ← inferType genExp)
      return (actName, actPf)
    catch ex =>
      trace[veil.debug] "Error generating {mode} view of action {actName} (from generator {genName}): {← ex.toMessageData.toString}"
      throwError "Error in action {baseName}: {← ex.toMessageData.toString}"

  /-- This generates a two-state transition from the action, with existentially
  quantified arguments. -/
  genTransition (vs : Array Expr) (sectionArgs : Array (TSyntax `term)) (baseName : Name) := do
    let (params, args) ← match br with
      | some br => pure (← toFunBinderArray br, ← explicitBindersIdents br)
      | none => pure (#[], #[])

    let (genName, actFnName, actTrName) := (toGenName baseName .external, toFnName baseName, toTrName baseName)
    let actTrStx <- `(fun st st' => exists? $br ?, (@$(mkIdent genName) $sectionArgs* $args*).toTwoState st st')
    try
      withoutErrToSorry $ do
      let actTr <- elabTermAndSynthesize actTrStx none
      -- For transitions that are lifted from a dependency (i.e. run through
      -- `.toWp.lift.toTwoState`), simplifying the definitions leads to a
      -- transition that existentially quantifies over the state of the
      -- dependency, which is bad. Instead, we apply the `lift_transition`
      -- theorem, giving us a nicer lifted transition.
      let ⟨actTr, _, _⟩ <- actTr.runSimp `(tactic| simp only [$(mkIdent `generatorSimp):ident, setIn, getFrom, lift_transition])
      -- After (potentially) `lift_transition` theorem, we simplify as usual
      let ⟨actTr, _, _⟩ <- actTr.simpAction
      let actTr <- mkLambdaFVarsImplicit vs actTr
      let actTr <- instantiateMVars actTr
      simpleAddDefn actTrName actTr (attr := #[{name := `actSimp}])

      let actFnStx <- `(fun $params* st st' => (@$(mkIdent genName) $sectionArgs* $args*).toTwoState st st')
      let actFn <- elabTermAndSynthesize actFnStx none
      let ⟨actFn, _, _⟩ <- actFn.simpAction
      let actFn <- mkLambdaFVarsImplicit vs actFn
      let actFn <- instantiateMVars actFn
      simpleAddDefn actFnName actFn (attr := #[{name := `actSimp}])

    catch ex =>
      throwError "Error generating transition for {actTrName} (from generator {genName}): {← ex.toMessageData.toString}"

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
    let trActThm ← withoutErrToSorry $ elabTermAndSynthesize trActThmStatement mkProp
    let ⟨afterSimp, thmPf, _⟩ <- trActThm.simpAction
    if !afterSimp.isTrue then
      throwError "[genSoundness] {trActThmStatement} could not be proven by `simp`"
    let proof ← match thmPf with
    | some thmPf => mkAppM ``of_eq_true #[thmPf]
    | none => mkEqRefl trActThm -- `simp` returns no proof if the statement is true by reflexivity

    let declName := toActTrEqName baseName
    addDecl <| Declaration.thmDecl <| mkTheoremValEx declName [] trActThm proof []
    enableRealizationsForConst declName

    let genSoundnessInstance (mode : Mode) (genName actName : Name) (vd : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) (univBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) (sectionArgs args : Array (TSyntax `term)) (actPf : Option Expr) := do
      let instTp <- `(forall? $[$vd]* $univBinders*, LawfulAction (@$(mkIdent genName):ident $sectionArgs* $args*))
      let instTp <- withoutErrToSorry $ elabTermAndSynthesize instTp none
      simpleAddThm (toGenInstName baseName mode) instTp `(tacticSeq| intros; infer_instance) (attr := #[{name := `instance}])

      let eqTp <- `(@$(mkIdent genName) = @$(mkIdent actName))
      let eqTp <- withoutErrToSorry $ elabTermAndSynthesize eqTp none
      let eq <- ensureHasType eqTp <| actPf.getD <| <- mkAppM ``Eq.refl #[mkConst actName]
      let eq <- Term.exprToSyntax eq

      let instTp <- `(forall? $[$vd]* $univBinders*, LawfulAction (m := $(← mode.stx)) (@$(mkIdent actName):ident $sectionArgs* $args*))
      let instTp <- withoutErrToSorry $ elabTermAndSynthesize instTp none
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
    let ⟨act, actPf, _⟩ <- act.simpAction
    let mut attr : Array Attribute := #[{name := `actSimp}]
    simpleAddDefn procName act (attr := attr) («type» := ← inferType genExp)
    return (procName, actPf)

/-- Defines `act` : `Wp m ρ σ` monad computation, parametrised over `br`. More
specifically it defines:
  - `act.genI` : internal action interpretation of the action, unsimplified
  - `act.genE` : external action interpretation of the action, unsimplified

  - `act.ext` : external action interpretation of the action, simplified
  - `act` : internal action interpretation (for procedure calls) of the action, simplified
  - `act.tr` : (external) transition of the action, with existentially quantified arguments
-/
def defineAction (actT : TSyntax `actionKind) (act : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (l : doSeq) : CommandElabM Unit := do
  trace[veil.debug] "Defining generators for action {act}"
  let (genIName, genEName) ← defineProcedureGenerators act br l
  trace[veil.debug] "Defining action {act} from generators {genIName} and {genEName}"
  defineActionFromGenerators actT act br genIName genEName
  registerProcedureSyntax act.getId l

def defineProcedure (proc : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (l : doSeq) : CommandElabM Unit := do
  let (genIName, _genEName) ← defineProcedureGenerators proc br l
  defineProcedureFromGenerator proc br genIName
  registerProcedureSyntax proc.getId l

/-- Given `tr` : `σ → σ → Prop` (parametrised over `br`), this defines:
  - `tr.genI` : internal action interpretation of the action, unsimplified
  - `tr.genE` : external action interpretation of the action, unsimplified

  This is used to re-cast a transition as an action.
-/
def defineTransition (actT : TSyntax `actionKind) (nm : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (tr : Term) : CommandElabM Unit := do
  let vd ← getImplicitProcedureParameters
  let baseName := (← getCurrNamespace) ++ nm.getId
  let (origName, trName) := (toFnIdent nm, toTrIdent nm)
  let (originalDef, trDef) ← Command.runTermElabM fun vs => do
    let trType <- `($genericState -> $genericState -> Prop)
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
      | some br => `(fun ($st $st' : $genericState) => ∃ $br, @$origName $sectionArgs* $args* $st $st')
      | none => `(fun ($st $st' : $genericState) => @$origName $sectionArgs* $args* $st $st')
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
    let genExp <- instantiateMVars <| <- mkLambdaFVarsImplicit vs genExp
    simpleAddDefn genName genExp (attr := #[{name := `generatorSimp}, {name := `actSimp}, {name := `reducible}]) («type» := ← inferType genExp)
    return (genName, genExp)
