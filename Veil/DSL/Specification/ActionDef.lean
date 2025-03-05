import Lean

import Veil.DSL.Action.Lang
import Veil.DSL.Tactic
import Veil.DSL.Specification.Syntax
import Veil.DSL.Specification.SpecDef

open Lean Elab Command Term Meta Lean.Parser

def wlpUnfold := [``Wlp.bind, ``Wlp.pure, ``Wlp.get, ``Wlp.set, ``Wlp.modifyGet,
  ``Wlp.assert, ``Wlp.assume, ``Wlp.require, ``Wlp.spec, ``Wlp.lift, ``Wlp.toActProp]

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

open Command Term in
/-- Record the action type and signature of this action in the `localSpecificationCtx`.  -/
def registerIOActionDecl (actT : TSyntax `actionKind) (nm : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)): CommandElabM Unit := do
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
      kind := toActionKind actT,
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


/-- Given `l` : `Wlp m σ ρ` (parametrised over `br`), this defines:
  - `act.genI` : internal action interpretation of the action, unsimplified
  - `act.genE` : external action interpretation of the action, unsimplified
-/
def defineActionGenerators (act : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (l : doSeq) : CommandElabM (Name × Name) := do
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
    let wlpSimp := mkIdent `wlpSimp
    let ⟨genExp, _, _⟩ <- genExp.runSimp `(tactic| simp only [$wlpSimp:ident])
    let genExp <- instantiateMVars <| <- mkLambdaFVarsImplicit vs genExp
    simpleAddDefn genName genExp (attr := #[{name := `actSimp}, {name := `reducible}])
    return (genName, genExp)

/-- Defines `act` : `Wlp m σ ρ` monad computation, parametrised over `br`. This
assumes that `act.genE` and `act.genI` have already been defined. Specifically
it defines:
  - `act.ext` : external action interpretation of the action, simplified
  - `act` : internal action interpretation (for procedure calls) of the action, simplified
  - `act.tr` : (external) transition of the action, with existentially quantified arguments
-/
def defineActionFromGenerators (actT : TSyntax `actionKind) (act : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (genIName genEName : Name) (generateTransition : Bool := true): CommandElabM Unit := do
    let vd ← getImplicitActionParameters
    Command.runTermElabM fun vs => do
      -- Create binders and arguments
      let sectionArgs ← getSectionArgumentsStx vs
      let baseName := (← getCurrNamespace) ++ act.getId
      let (_actIName, actIPf) ← genAction baseName .internal genIName
      let (_actEName, actEPf) ← genAction baseName .external genEName
      if generateTransition then
        let (_actTrName, actTrStx, actTrPf) ← genTransition vs sectionArgs baseName
        if veil.gen_sound.get <| <- getOptions then
          genSoundness vd vs br baseName actTrStx actIPf actEPf actTrPf
where
  /-- This generates the 'simplified' (fully unfolded) action interpretation,
  assuming the generator for this `mode` has already been defined and can be
  found in the environment with name `genName`. -/
  genAction (baseName : Name) (mode : Mode) (genName : Name) := do
    let actName := match mode with
    | Mode.internal => baseName
    | Mode.external => toExtName baseName
    let genExp := Lean.mkConst genName
    let act ← genExp |>.runUnfold (genName :: wlpUnfold)
    let ⟨act, actPf, _⟩ <- act.runSimp `(tactic| simp only [actSimp, logicSimp, smtSimp, quantifierSimp])
    let mut attr : Array Attribute := #[{name := `actSimp}]
    -- We "register" the internal interpretation of the action as an IO automata action
    -- FIXME George: is this the right thing to do?
    if mode == Mode.internal then
      attr := attr.push (toActionAttribute' (toActionKind actT))
    simpleAddDefn actName act (attr := attr) («type» := ← inferType genExp)
    return (actName, actPf)

  /-- This generates a two-state transition from the action, with existentially
  quantified arguments. -/
  genTransition (vs : Array Expr) (sectionArgs : Array (TSyntax `term)) (baseName : Name) := do
    let args  ← match br with
      | some br => explicitBindersIdents br
      | none => pure #[]
    let (actEName, actTrName) := (toExtName baseName, toTrName baseName)
    let actTrStx <- `(fun st st' => exists? $br ?, (@$(mkIdent actEName) $sectionArgs* $args*).toActProp st st')
    let actTr <- elabTermAndSynthesize actTrStx none
    let actTr <- mkLambdaFVarsImplicit vs actTr
    let ⟨actTr, actTrPf, _⟩ <- actTr.runSimp `(tactic| simp only [actSimp, logicSimp, smtSimp, quantifierSimp])
    let actTr <- instantiateMVars actTr
    simpleAddDefn actTrName actTr (attr := #[{name := `actSimp}])
    return (actTrName, actTrStx, actTrPf)

  /-- This generates type class instances that are required to prove the
  _soundness_ of the translation of the imperative action into the two-state
  transition. This can be expensive, so it is off by default. -/
  genSoundness (vd : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) (vs : Array Expr) (br : Option (TSyntax `Lean.explicitBinders)) (baseName : Name) (actTrStx : TSyntax `term) (actIPf actEPf actTrPf : Option Expr) := do
    let (actTrName, genEName, genIName, actEName, actIName) :=
      let actTrName := toTrName baseName
      let genEName := toGenName baseName .external
      let genIName := toGenName baseName .internal
      let actEName := toExtName baseName
      let actIName := baseName
      (actTrName, genEName, genIName, actEName, actIName)
    let sectionArgs ← getSectionArgumentsStx vs
    let (univBinders, args) ← match br with
      | some br => pure (← toBracketedBinderArray br, ← explicitBindersIdents br)
      | none => pure (#[], #[])

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
      addDecl <| Declaration.thmDecl <| mkTheoremValEx (toActTrEqName baseName) [] trActThm proof []

    let instETp <- `(forall? $[$vd]* $univBinders*, Sound (@$(mkIdent genEName):ident $sectionArgs* $args*))
    let instETp <- elabTermAndSynthesize instETp none
    let instITp <- `(forall? $[$vd]* $univBinders*, Sound (@$(mkIdent genIName):ident $sectionArgs* $args*))
    let instITp <- elabTermAndSynthesize instITp none

    simpleAddThm (toGenInstName baseName .external) instETp `(tacticSeq| intros; infer_instance) (attr := #[{name := `instance}])
    simpleAddThm (toGenInstName baseName .internal) instITp `(tacticSeq| intros; infer_instance) (attr := #[{name := `instance}])
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
    simpleAddThm (toInstName baseName .external) instETp
      `(tacticSeq|
        have h : @$(mkIdent genEName) = @$(mkIdent actEName) := $eqE
        rw [<-h]; intros; infer_instance) (attr := #[{name := `instance}])
    simpleAddThm (toInstName baseName .internal) instITp
      `(tacticSeq|
        have h : @$(mkIdent genIName) = @$(mkIdent actIName) := $eqI
        rw [<-h]; intros; infer_instance) (attr := #[{name := `instance}])

/-- Defines `act` : `Wlp m σ ρ` monad computation, parametrised over `br`. More
specifically it defines:
  - `act.genI` : internal action interpretation of the action, unsimplified
  - `act.genE` : external action interpretation of the action, unsimplified

  - `act.ext` : external action interpretation of the action, simplified
  - `act` : internal action interpretation (for procedure calls) of the action, simplified
  - `act.tr` : (external) transition of the action, with existentially quantified arguments
-/
def defineAction (actT : TSyntax `actionKind) (act : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (l : doSeq) : CommandElabM Unit := do
  let (genIName, genEName) ← defineActionGenerators act br l
  defineActionFromGenerators actT act br genIName genEName


/-- We support executing actions from dependent modules is by `monadLift`ing
them to the current module's state. This function generates the
`IsStateExtension` instances required to do this. -/
def genStateExtInstances : CommandElabM Unit := do
  let currName <- getCurrNamespace
  let vd := (<- getScope).varDecls
  let insts <- Command.runTermElabM fun vs => do
    let mut insts := #[]
    for (modAlias, dep) in (<- localSpecCtx.get).spec.dependencies do
      let ts ← dep.stateArguments
      let currTs <- getStateArgumentsStx vd vs
      let alia := mkIdent modAlias
      let inst <-
        `(@[actSimp]
          instance :
           IsStateExtension
             (@$(mkIdent $ dep.name ++ `State) $ts*)
             (@$(mkIdent $ currName ++ `State) $currTs*) where
            extendWith := fun s s' => { s' with $alia:ident := s }
            restrictTo := fun s' => s'.$alia)
      insts := insts.push inst
    return insts
  for inst in insts do
    trace[veil.debug] "Generating state extension instance {inst}"
    elabCommand inst
    trace[veil.info] "State extension instance is defined"

-- def baz (n  q: Nat) := @monadLift (Wlp Mode.internal (Test₁.State node')) (Wlp Mode.internal (State node' node'')) _ Unit (@Test₁.f.genI node' node'_dec node'_ne n q)
def liftActionGenerators (forAct : TSyntax `ident) (withBinders : Option (TSyntax `Lean.explicitBinders)) (stateTpT : TSyntax `term) (fromBaseGenerator : Name) (instatiatedWithArgs : Array Term) : CommandElabM (Name × Name) := do
  Command.runTermElabM fun vs => do
    let baseName := (← getCurrNamespace) ++ forAct.getId
    let (genIName, _genExpI) ← liftGenerator baseName vs withBinders fromBaseGenerator instatiatedWithArgs .internal
    let (genEName, _genExpE) ← liftGenerator baseName vs withBinders fromBaseGenerator instatiatedWithArgs .external
    return (genIName, genEName)
where
  liftGenerator (liftedActName : Name) (actVs : Array Expr) (actBinders :  Option (TSyntax `Lean.explicitBinders)) (baseNameToLift : Name) (depArgs : Array Term) (mode : Mode)  := do
    let baseGenName := toGenName baseNameToLift mode
    let (actParams, actArgs) ← match actBinders with
    | some br => pure (← toFunBinderArray br, ← explicitBindersIdents br)
    | none => pure (#[], #[])
    let infer ← `(term|_)
    let (srcWlpType, typeClassInst, retType) := (infer, infer, infer)
    -- e.g. `Wlp Mode.internal (State node' node'')`
    let dstWlpType ← `(term|Wlp $(← mode.stx) ($stateTpT))
    let liftedGenStx ← `(fun $actParams* => @monadLift $srcWlpType $dstWlpType $typeClassInst $retType <| @$(mkIdent baseGenName) $depArgs* $actArgs*)
    let liftedGenName := toGenName liftedActName mode
    trace[veil.info] "{liftedGenName} := {liftedGenStx}"
    let genExp <- withDeclName liftedGenName do elabTermAndSynthesize liftedGenStx .none
    let wlpSimp := mkIdent `wlpSimp
    let ⟨genExp, _, _⟩ <- genExp.runSimp `(tactic| simp only [$wlpSimp:ident])
    let genExp <- instantiateMVars <| <- mkLambdaFVarsImplicit actVs genExp
    simpleAddDefn liftedGenName genExp (attr := #[{name := `actSimp}, {name := `reducible}])
    return (liftedGenName, genExp)

def defineDepsActions : CommandElabM Unit := do
  for (modAlias, dependency) in (<- localSpecCtx.get).spec.dependencies do
    -- arguments with which the dependency was instantiated
    let depArgs := dependency.arguments
    let globalCtx <- globalSpecCtx.get
    let some depCtx := globalCtx[dependency.name]? | throwError "Module {dependency.name} is not declared"
    for actToLift in depCtx.actions do
      let actBaseName := dependency.name ++ actToLift.decl.name
      -- If an action has a pre-post specification, we use the the specification
      -- instead of the action itself as the lifted action. Recall that
      -- specification are just `action`s` themselves. In particular they have
      -- `genE` and `genI` generators that we can use to lift the action.
      let actBaseName := if actToLift.hasSpec then toSpecName actBaseName else actBaseName
      let liftedName := mkIdent <| modAlias ++ actBaseName.componentsRev[0]!
      -- When we lift an action from a dependency, the binders of the action
      -- may have types that are not syntactically present in the action's
      -- signature. We have to substitute the types with the arguments of the
      -- dependency instantiation. We cannot use `_` to infer the types, since
      -- we use these type arguments to construct the `Label` type, so they
      -- must be explicit.
      let liftedBinders ← do match actToLift.br with
        | some br => pure (Option.some (← toBindersWithMappedTypes br (← dependency.typeMapping)))
        | none => pure .none
      let stateTpT ← liftCoreM $ getStateTpStx
      trace[veil.info] "lifting action {actBaseName} from module {dependency.name} to module {← specName} as {liftedName}"
      let actionKind ← actToLift.decl.kind.stx
      let (genIName, genEName) ← liftActionGenerators liftedName liftedBinders stateTpT actBaseName depArgs
      defineActionFromGenerators actionKind liftedName liftedBinders genIName genEName
      -- Important: don't forget to register the label
      registerIOActionDecl actionKind liftedName liftedBinders
      -- let stx <- `(action $liftedName:ident $(liftedBinders)? = { monadLift <| @$(mkIdent $ actBaseName) $depArgs* $actArgs* })
      -- trace[veil.debug] stx
      -- elabCommand stx

/-- Given `tr` : `σ → σ → Prop` (parametrised over `br`), this defines:
  - `tr.genI` : internal action interpretation of the action, unsimplified
  - `tr.genE` : external action interpretation of the action, unsimplified

  This is used to re-cast a transition as an action.
-/
def defineTransition (actT : TSyntax `actionKind) (nm : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (tr : Term) : CommandElabM Unit := do
  let vd ← getImplicitActionParameters
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
    -- since our conversion to `Wlp` increases the size of the formula.
    let trDef ← do
      let (st, st') := (mkIdent `st, mkIdent `st')
      let rhs ← match br with
      | some br => `(fun ($st $st' : $stateTpT) => ∃ $br, @$origName $sectionArgs* $args* $st $st')
      | none => `(fun ($st $st' : $stateTpT) => @$origName $sectionArgs* $args* $st $st')
      `(@[actSimp] def $trName $[$vd]* : $trType := $(← unfoldWlp rhs))
    return (originalDef, trDef)
  trace[veil.info] "{originalDef}"
  elabCommand originalDef
  trace[veil.info] "{trDef}"
  elabCommand trDef
  let (genIName, genEName) ← Command.runTermElabM fun vs => do
    let (genIName, _genExpI) ← genGeneratorFromTransition vs origName baseName .internal
    let (genEName, _genExpE) ← genGeneratorFromTransition vs origName baseName .external
    return (genIName, genEName)
  -- We don't generate the transition based on `Wlp`, since we already have it from the user.
  defineActionFromGenerators actT nm br genIName genEName (generateTransition := false)
where
  genGeneratorFromTransition (vs : Array Expr) (origName : Ident) (baseName : Name) (mode : Mode) := do
    let genName := toGenName baseName mode
    let sectionArgs ← getSectionArgumentsStx vs
    let (funBinders, args) ← match br with
    | some br => pure (← toFunBinderArray br, ← explicitBindersIdents br)
    | none => pure (#[], #[])
    let term ← match mode with
    | Mode.internal => `((@$origName $sectionArgs* $args*).toWlp .internal)
    | Mode.external => `((@$origName $sectionArgs* $args*).toWlp .external)
    let genl ← `(fun $funBinders* => $(← unfoldWlp term))
    let genExp <- withDeclName genName do elabTermAndSynthesize genl none
    -- let wlpSimp := mkIdent `wlpSimp
    -- let ⟨genExp, _, _⟩ <- genExp.runSimp `(tactic| simp only [$wlpSimp:ident])
    let genExp <- instantiateMVars <| <- mkLambdaFVarsImplicit vs genExp
    simpleAddDefn genName genExp (attr := #[{name := `actSimp}, {name := `reducible}]) («type» := ← inferType genExp)
    return (genName, genExp)

/-- Elaborates a two-state transition. FIXME: get rid of code duplication with `elabCallableFn`. -/
def elabCallableTr (actT : TSyntax `actionKind) (nm : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (tr : Term) : CommandElabM Unit := do
    let vd ← getImplicitActionParameters
    -- `nm.unsimplified`
    let (uName, fnName, extName, trName) := (toOriginalIdent nm, nm, toExtIdent nm, toTrIdent nm)
    let (unsimplifiedDef, trDef, extDef, fnDef) ← Command.runTermElabM fun vs => do
      let stateTpT ← getStateTpStx
      let trType <- `($stateTpT -> $stateTpT -> Prop)
      -- Create binders and arguments
      let sectionArgs ← getSectionArgumentsStx vs
      let (univBinders, args) ← match br with
      | some br => pure (← toBracketedBinderArray br, ← explicitBindersIdents br)
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
      let attr ← toActionAttribute (toActionKind actT)
      let fnDef ← `(@[$attr, actSimp] def $fnName $[$vd]* $univBinders* := $(← unfoldWlp $ ← `((@$uName $sectionArgs* $args*).toWlp .internal)))
      -- FIXME George: does this actually make sense?
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
