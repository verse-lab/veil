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
  let labelTypeArgs ← bracketedBindersToTerms $ ← (← localSpecCtx.get).spec.generic.applyGetStateArguments vd
  let labelT ← `(term|$labelIdent $labelTypeArgs*)
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
        s.spec.procedures.map fun t =>
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

def mkProcedureGenerators (act : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (l : doSeq) : CommandElabM (Name × Name) := do
  let vd ← getImplicitProcedureParameters
  Command.runTermElabM fun vs => do
    let baseName := (← getCurrNamespace) ++ act.getId
    let (genIName, _genExpI) ← genGenerator vs vd br baseName .internal l
    let (genEName, _genExpE) ← genGenerator vs vd br baseName .external l
    return (genIName, genEName)
  where
    genGenerator (vs : Array Expr) (vd : Array (TSyntax ``Term.bracketedBinder)) (br : Option (TSyntax `Lean.explicitBinders)) (baseName : Name) (mode : Mode) (l : doSeq) := do
      let genName := toActName baseName mode
      let funBinders ← match br with
      | some br => toFunBinderArray br
      | none => pure #[]
      let genl ← match mode with
      | Mode.internal => do `(fun $funBinders* => do' .internal as $genericReader, $genericState in $l)
      | Mode.external => do `(fun $funBinders* => do' .external as $genericReader, $genericState in $l)
      try
        withoutErrToSorry $ do
        let genExp <- withDeclName genName do elabTermAndSynthesize genl none
        let ⟨genExp, _, _⟩ <- genExp.simpAction
        let genExp <- instantiateMVars <| <- mkLambdaFVarsImplicit vs genExp
        if mode == Mode.internal then
          simpleAddDefn genName genExp (attr := #[{name := `generatorSimp}, {name := `actSimp}, {name := `reducible}])
        else
          let withRetName := genName ++ `withRet
          simpleAddDefn withRetName genExp (attr := #[{name := `generatorSimp}, {name := `actSimp}, {name := `reducible}])
          defineUnitAct vs vd genName withRetName br
        return (genName, genExp)
      catch ex =>
        trace[veil.debug] "Error generating {mode} generator for {genName}: {← ex.toMessageData.toString}"
        -- We have this as a more user-readable message
        throwError "Error in action {baseName}: {← ex.toMessageData.toString}"
    defineUnitAct (vs : Array Expr) (vd : Array (TSyntax ``Term.bracketedBinder))
    (outputActName : Name) (inputActName : Name) (br : Option (TSyntax `Lean.explicitBinders)) : TermElabM Unit := do
      let sectionArgs ← getSectionArgumentsStx vs
      let (univBinders, args) ← match br with
        | some br => pure (← toBracketedBinderArray br, ← explicitBindersIdents br)
        | none => pure (#[], #[])
      liftCommandElabM <| elabCommand <| <- `(command|
        @[generatorSimp, actSimp, reducible] def $(mkIdent outputActName) $vd* $univBinders* : VeilM .external $genericReader $genericState PUnit := do
          let _ ← @$(mkIdent inputActName) $sectionArgs* $args*; pure PUnit.unit)

/-- Defines a function and simplifies it using `simp` with the given simp lemma and simp sets. -/
def defineAndSimplify (vs : Array Expr)
  (defName : Name)
  (defStx : Array Term -> Array Term -> TermElabM Term)
  (unfolds : List Name)
  (simps : Array Name)
  (br : Option (TSyntax `Lean.explicitBinders))
  (extraAttr : Array Name := #[])
   := do
    let sectionArgs ← getSectionArgumentsStx vs
    let args ← match br with
      | some br => pure (← explicitBindersIdents br)
      | none => pure #[]
    withoutErrToSorry $ do
    let actStx <- defStx sectionArgs args
    let mut actExp <- elabTermAndSynthesize actStx none
    unless unfolds.isEmpty do
      actExp <- actExp.runUnfold unfolds
    let mut act := actExp
    let mut actPf := none
    unless simps.isEmpty do
      let actAndPf <- actExp.simp simps
      act := actAndPf.expr
      actPf := actAndPf.proof?
    act <- mkLambdaFVarsImplicit vs act
    act <- instantiateMVars act
    simpleAddDefn defName act (attr := (#[{name := `actSimp}] : Array Attribute) ++ extraAttr.map (fun x => ({name := x} : Attribute)))
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
  (actName : Name) (br : Option (TSyntax `Lean.explicitBinders)) (isInit : Bool := false) : TermElabM
  (Name × Option Expr) :=
  defineAndSimplify vs (toWpName actName) (fun sectionArgs args => `(fun hd $args* post =>
    [CanRaise hd| wp (@$(mkIdent actName) $sectionArgs* $args*) post]))
    [] #[`wpSimp, actName, `smtSimp, `quantifierSimp] br (if isInit then #[`initSimp] else #[])

/-- Defines the weakest precondition for the action specialised to the case where the
  exception handler is `True`. -/
def defineWpSuccForAction (vs : Array Expr)
  (actName : Name) (br : Option (TSyntax `Lean.explicitBinders)) (isInit : Bool := false) : TermElabM
  (Name × Option Expr) :=
  let actWpName := toWpName actName
  let actWpSuccName := toWpSuccName actName
  defineAndSimplify vs actWpSuccName (fun sectionArgs args => `(fun $args* post =>
      @$(mkIdent actWpName) $sectionArgs* (fun _ => True) $args* post))
    [actWpName] #[``if_true_right] br (if isInit then #[`initSimp] else #[])

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
  (actName : Name) (br : Option (TSyntax `Lean.explicitBinders)) (isInit : Bool := false) :
  TermElabM (Name × Option Expr) := do
  let actWpSuccName := toWpSuccName actName
  let actTwoStateName := toTwoStateName actName
  defineAndSimplify vs actTwoStateName (fun sectionArgs args => `(
    fun $args* =>
      VeilSpecM.toTwoStateDerived <| @$(mkIdent actWpSuccName) $sectionArgs* $args*))
    [actWpSuccName, ``VeilSpecM.toTwoStateDerived, ``Cont.inv] #[] br (if isInit then #[`initSimp] else #[])
    --#[``Pi.compl_def, ``compl] br

def defineTr (vs : Array Expr)
  (actName : Name) (br : Option (TSyntax `Lean.explicitBinders)) (isInit : Bool := false) :
  TermElabM (Name × Option Expr) := do
  let actTrName := toTrName actName
  let actTwoStateName := toTwoStateName actName
  defineAndSimplify vs actTrName (fun sectionArgs args => `(
    fun r s s' =>
      exists? $br ?, @$(mkIdent actTwoStateName) $sectionArgs* $args* r s s'))
    [actTwoStateName] #[] br (if isInit then #[`initSimp] else #[])

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

def defineEndToEndLemma (vs : Array Expr) (vd : Array (TSyntax ``Term.bracketedBinder))
  (actName : Name) (actTwoStateName : Name)
  (br : Option (TSyntax `Lean.explicitBinders)) : TermElabM Unit := do
  let sectionArgs ← getSectionArgumentsStx vs
  let (univBinders, args) ← match br with
    | some br => pure (← toBracketedBinderArray br, ← explicitBindersIdents br)
    | none => pure (#[], #[])
  let thm ← `(command|
  @[nextSimp] theorem $(mkIdent $ toEndToEndLemmaName actName) $vd* $univBinders* :
    VeilM.toTwoStateDerived (@$(mkIdent actName) $sectionArgs* $args*) = @$(mkIdent actTwoStateName) $sectionArgs* $args*
   := by
   unfold VeilM.toTwoStateDerived
   simp only [← $(mkIdent $ toTwoStateLemmaName actName)]
   unfold VeilSpecM.toTwoStateDerived Cont.inv
   simp only [← $(mkIdent $ toWpSuccLemmaName actName), ← $(mkIdent $ toWpLemmaName actName)]
  )
  trace[veil.info] "Defining end-to-end lemma for {actName}: {thm}"
  liftCommandElabM <| elabCommand thm

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

def defineAuxiliaryDeclarations (declType : DeclType) (mode : Mode) (actName : Name) (br : Option (TSyntax `Lean.explicitBinders)) := do
  let vd ← getImplicitProcedureParameters
  runTermElabM fun vs => do
    let isInit := declType = DeclType.init

    let (actWpName, actWpPf) ← defineWpForAction vs actName br isInit
    defineWpLemma vs vd actName actWpName actWpPf br

    unless declType = DeclType.proc do
      let (actWpSuccName, actWpSuccPf) ← defineWpSuccForAction vs actName br isInit
      defineWpSuccLemma vs vd actName actWpSuccName actWpName actWpSuccPf br

      unless declType = DeclType.init do
        let (actWpExName, actWpExPf) ← defineWpExForAction vs actName br
        defineWpExLemma vs vd actName actWpName actWpExName actWpExPf br

      if mode == Mode.external then
        let (actTwoStateName, actTwoStatePf) ← defineTwoStateAction vs actName br isInit
        defineTwoStateLemma vs vd actName actTwoStateName actTwoStatePf br
        defineEndToEndLemma vs vd actName actTwoStateName br
        let (actTrName, actTrPf) ← defineTr vs actName br isInit
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

def registerTransition (actT : TSyntax `actionKind) (nm : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) : CommandElabM Unit:= do
  declareProcedure (toActionKind actT) nm.getId
  registerIOActionDecl actT nm br
  registerProcedureBinders nm.getId br

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
  let (actIntName, actExtName) ← mkProcedureGenerators act br l
  defineAuxiliaryDeclarations .act .external actExtName br
  defineAuxiliaryDeclarations .act .internal actIntName br
  registerAction actT act br l

def defineInitialAction (l : doSeq) : CommandElabM Unit := do
  let initName := mkIdent initializerName
  let (_, actExtName) ← mkProcedureGenerators initName none l
  defineAuxiliaryDeclarations .init .external actExtName none

def defineProcedure (proc : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (l : doSeq) : CommandElabM Unit := do
  let (_, actIntName) ← mkProcedureGenerators proc br l
  defineAuxiliaryDeclarations .proc .internal actIntName br
  registerProcedure proc br l

def defineTransition (actT : TSyntax `actionKind) (nm : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (tr : Term) : CommandElabM Unit := do
  trace[veil.debug] "Defining {actT} transition {nm}: {tr}"
  let vd ← getImplicitProcedureParameters
  let baseName := (← getCurrNamespace) ++ nm.getId
  let origName := toOriginalIdent nm
  let originalDef ← Command.runTermElabM fun _ => do
    let trType <- `($genericReader -> $genericState -> $genericState -> Prop)
    let univBinders ← match br with
    | some br => pure (← toBracketedBinderArray br)
    | none => pure #[]
    -- We keep the original definition of the transition, as given by the user.
    let originalDef ← `(@[actSimp] def $origName $[$vd]* $univBinders* : $trType := $tr)
    return originalDef
  trace[veil.debug] "{originalDef}"
  elabCommand originalDef
  let (_genIName, genEName) ← Command.runTermElabM fun vs => do
    let genIName ← genGeneratorFromTransition vs origName baseName .internal
    let genEName ← genGeneratorFromTransition vs origName baseName .external
    return (genIName, genEName)
  defineAuxiliaryDeclarations .act .external genEName br
  registerTransition actT nm br
where
  genGeneratorFromTransition (vs : Array Expr) (origName : Ident) (baseName : Name) (mode : Mode) := do
    let genName := toActName baseName mode
    let sectionArgs ← getSectionArgumentsStx vs
    let (funBinders, args) ← match br with
    | some br => pure (← toFunBinderArray br, ← explicitBindersIdents br)
    | none => pure (#[], #[])
    let term ← match mode with
    | Mode.internal => `(@TwoState.toVeilM .internal _ _ (@$origName $sectionArgs* $args*))
    | Mode.external => `(@TwoState.toVeilM .external _ _ (@$origName $sectionArgs* $args*))
    let genl ← `(fun $funBinders* => $term)
    let genExp <- withDeclName genName do elabTermAndSynthesize genl none
    let ⟨genExp, _, _⟩ <- genExp.simp #[``TwoState.toVeilM, origName.getId]
    let genExp <- instantiateMVars <| <- mkLambdaFVarsImplicit vs genExp
    simpleAddDefn genName genExp (attr := #[{name := `generatorSimp}, {name := `actSimp}, {name := `reducible}]) («type» := ← inferType genExp)
    return genName


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
