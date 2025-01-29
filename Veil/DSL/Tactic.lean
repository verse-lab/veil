import Lean.Elab.Tactic
import Veil.DSL.Util
import Veil.SMT.Main
import Veil.DSL.ActionLang -- TODO: can we remove this?

open Lean Lean.Elab

/--
  `exact_state` is usually used after `funcases` ar `funcasesM`. At this point the goal should
  contain all state fields as hypotheses. This tactic will then construct the
  state term using the field hypotheses and close the goal.
-/
elab "exact_state" : tactic => do
  let stateName ← getStateName
  let stateTp := (<- localSpecCtx.get).spec.stateType
  let .some sn := stateTp.constName?
    | throwError "{stateTp} is not a constant"
  let .some _sinfo := getStructureInfo? (<- getEnv) sn
    | throwError "{stateTp} is not a structure"
  let fns := _sinfo.fieldNames.map mkIdent
  -- fileds' names should be the same as ones in the local context
  let constr <- `(term| (⟨$[$fns],*⟩ : $(mkIdent stateName) ..))
  Tactic.evalTactic $ ← `(tactic| exact $constr)

open Tactic in
elab _tk:"conv! " conv:conv " => " e:term : term => do
  let e ← Elab.Term.elabTermAndSynthesize e none
  let (rhs, g) ← Conv.mkConvGoalFor e
  _ ← Tactic.run g.mvarId! (do
    evalTactic conv
    for mvarId in (← getGoals) do
      liftM <| mvarId.refl <|> mvarId.inferInstance <|> pure ()
    pruneSolvedGoals
    let e' ← instantiateMVars rhs
    trace[dsl.debug] "[conv!] {e}\nsimplifies to\n{e'}"
  )
  return rhs

/-- We use this to evaluate `wlp` inside function bodies at definition time.
  Otherwise it has to be evaluated in the kernel during proofs, which is very slow.
  `conv!` applies a tactic to a term. -/
def unfoldWlp (t : TSyntax `term) : TermElabM (TSyntax `term) := do
  let actSimp := mkIdent `actSimp
  -- We have to do this round-about `let t : = .. ; exact t` because we
  -- want to delay the evaluation of `t` until types are available to be
  -- inferred, otherwise `$t` might fail to type-check.
  let t' ← `(term|by first | let t := conv! (dsimp only [$actSimp:ident]; unfold_wlp; dsimp only) => $t; exact t | exact $t)
  return t'

def dsimpOnly (t : TSyntax `term) (classes : Array Name := #[]) : TermElabM (TSyntax `term) := do
  let classes := classes.map mkIdent
  let t' ← `(term|by first | let t := conv! (dsimp only [$[$classes:ident],*]) => $t; exact t | exact $t)
  return t'

/-- This does `unfoldWlp` followed by some other simplifications. -/
def simplifyTerm (t : TSyntax `term) : TermElabM (TSyntax `term) := do
  let (actSimp, smtSimp, logicSimp, quantifierElim) := (mkIdent `actSimp, mkIdent `smtSimp, mkIdent `logicSimp, mkIdent `quantifierElim)
  -- Reduce the body of the function
  let t' ← `(term| by
    -- Try simplifying first, but this might fail if there's no `wlp` in the
    -- definition, e.g. for transitions that are not actions.
    -- If that fails, we try to evaluate the term as is.
    -- We do `simp only [and_assoc]` at the end to normalize conjunctions.
    first | (let t := conv! (
        dsimp only [$actSimp:ident];
        -- for two-state version of the cation
        unfold_wlp
        simp only [$smtSimp:ident, $logicSimp:ident];
        simp only [$quantifierElim:ident]) => $t; exact t) | exact $t)
  return t'

open Tactic Lean.Meta

private def addDeclToUnfoldOrTheorem (config : Meta.ConfigWithKey) (thms : SimpTheorems) (id : Origin) (e : Expr) (post : Bool) (inv : Bool) (kind : SimpKind) : MetaM SimpTheorems := do
  if e.isConst then
    let declName := e.constName!
    let info ← getConstInfo declName
    if (← isProp info.type) then
      thms.addConst declName (post := post) (inv := inv)
    else
      if inv then
        throwError "invalid '←' modifier, '{declName}' is a declaration name to be unfolded"
      if kind == .dsimp then
        return thms.addDeclToUnfoldCore declName
      else
        thms.addDeclToUnfold declName
  else if e.isFVar then
    let fvarId := e.fvarId!
    let decl ← fvarId.getDecl
    if (← isProp decl.type) then
      thms.add id #[] e (post := post) (inv := inv) (config := config)
    else if !decl.isLet then
      throwError "invalid argument, variable is not a proposition or let-declaration"
    else if inv then
      throwError "invalid '←' modifier, '{e}' is a let-declaration name to be unfolded"
    else
      return thms.addLetDeclToUnfold fvarId
  else
    thms.add id #[] e (post := post) (inv := inv) (config := config)

private def addSimpTheorem (config : Meta.ConfigWithKey) (thms : SimpTheorems) (id : Origin) (stx : Syntax) (post : Bool) (inv : Bool) : TermElabM SimpTheorems := do
  let thm? ← Term.withoutModifyingElabMetaStateWithInfo <| withRef stx do
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
    let e ← instantiateMVars e
    if e.hasSyntheticSorry then
      return none
    let e := e.eta
    if e.hasMVar then
      let r ← abstractMVars e
      return some (r.paramNames, r.expr)
    else
      return some (#[], e)
  if let some (levelParams, proof) := thm? then
    thms.add id levelParams proof (post := post) (inv := inv) (config := config)
  else
    return thms



/--
  Elaborate extra simp theorems provided to `simp`. `stx` is of the form `"[" simpTheorem,* "]"`
  If `eraseLocal == true`, then we consider local declarations when resolving names for erased theorems (`- id`),
  this option only makes sense for `simp_all` or `*` is used.
  When `recover := true`, try to recover from errors as much as possible so that users keep seeing
  the current goal.
-/
def elabSimpArgs (stx : Syntax) (ctx : Simp.Context) (simprocs : Simp.SimprocsArray) (eraseLocal : Bool) (kind : SimpKind) : TermElabM ElabSimpArgsResult := do
  if stx.isNone then
    return { ctx, simprocs }
  else
    /-
    syntax simpPre := "↓"
    syntax simpPost := "↑"
    syntax simpLemma := (simpPre <|> simpPost)? "← "? term

    syntax simpErase := "-" ident
    -/
    let go := do --withMainContext do
      let mut thmsArray := ctx.simpTheorems
      let mut thms      := thmsArray[0]!
      let mut simprocs  := simprocs
      let mut starArg   := false
      for arg in stx[1].getSepArgs do
        try -- like withLogging, but compatible with do-notation
          if arg.getKind == ``Lean.Parser.Tactic.simpErase then
            let fvar? ← if eraseLocal || starArg then Term.isLocalIdent? arg[1] else pure none
            if let some fvar := fvar? then
              -- We use `eraseCore` because the simp theorem for the hypothesis was not added yet
              thms := thms.eraseCore (.fvar fvar.fvarId!)
            else
              let id := arg[1]
              if let .ok declName ← observing (realizeGlobalConstNoOverloadWithInfo id) then
                if (← Simp.isSimproc declName) then
                  simprocs := simprocs.erase declName
                else if ctx.config.autoUnfold then
                  thms := thms.eraseCore (.decl declName)
                else
                  thms ← withRef id <| thms.erase (.decl declName)
              else
                -- If `id` could not be resolved, we should check whether it is a builtin simproc.
                -- before returning error.
                let name := id.getId.eraseMacroScopes
                if (← Simp.isBuiltinSimproc name) then
                  simprocs := simprocs.erase name
                else
                  withRef id <| throwUnknownConstant name
          else if arg.getKind == ``Lean.Parser.Tactic.simpLemma then
            let post :=
              if arg[0].isNone then
                true
              else
                arg[0][0].getKind == ``Parser.Tactic.simpPost
            let inv  := !arg[1].isNone
            let term := arg[2]
            match (← resolveSimpIdTheorem? ⟨term⟩) with
            | .expr e  =>
              let name ← mkFreshId
              thms ← addDeclToUnfoldOrTheorem ctx.indexConfig thms (.stx name arg) e post inv kind
            | .simproc declName =>
              simprocs ← simprocs.add declName post
            | .ext (some ext₁) (some ext₂) _ =>
              thmsArray := thmsArray.push (← ext₁.getTheorems)
              simprocs  := simprocs.push (← ext₂.getSimprocs)
            | .ext (some ext₁) none _ =>
              thmsArray := thmsArray.push (← ext₁.getTheorems)
            | .ext none (some ext₂) _ =>
              simprocs  := simprocs.push (← ext₂.getSimprocs)
            | .none    =>
              let name ← mkFreshId
              thms ← addSimpTheorem ctx.indexConfig thms (.stx name arg) term post inv
          else if arg.getKind == ``Lean.Parser.Tactic.simpStar then
            starArg := true
          else
            throwUnsupportedSyntax
        catch ex =>
            throw ex
      return { ctx := ctx.setSimpTheorems (thmsArray.set! 0 thms), simprocs, starArg }
    -- If recovery is disabled, then we want simp argument elaboration failures to be exceptions.
    -- This affects `addSimpTheorem`.
    Term.withoutErrToSorry go
where
  isSimproc? (e : Expr) : MetaM (Option Name) := do
    let .const declName _ := e | return none
    unless (← Simp.isSimproc declName) do return none
    return some declName

  resolveSimpIdTheorem? (simpArgTerm : Term) : TermElabM ResolveSimpIdResult := do
    let resolveExt (n : Name) : TermElabM ResolveSimpIdResult := do
      let ext₁? ← getSimpExtension? n
      let ext₂? ← Simp.getSimprocExtension? n
      if h : ext₁?.isSome || ext₂?.isSome then
        return .ext ext₁? ext₂? h
      else
        return .none
    match simpArgTerm with
    | `($id:ident) =>
      try
        if let some e ← Term.resolveId? simpArgTerm (withInfo := true) then
          if let some simprocDeclName ← isSimproc? e then
            return .simproc simprocDeclName
          else
            return .expr e
        else
          let name := id.getId.eraseMacroScopes
          if (← Simp.isBuiltinSimproc name) then
            return .simproc name
          else
            resolveExt name
      catch _ =>
        resolveExt id.getId.eraseMacroScopes
    | _ =>
      if let some e ← Term.elabCDotFunctionAlias? simpArgTerm then
        return .expr e
      else
        return .none

@[inline] def simpOnlyBuiltins : List Name := [``eq_self, ``iff_self]

structure MkSimpContextResult where
  ctx              : Simp.Context
  simprocs         : Simp.SimprocsArray
  dischargeWrapper : Simp.DischargeWrapper

/--
  Implement a `simp` discharge function using the given tactic syntax code.
  Recall that `simp` dischargers are in `SimpM` which does not have access to `Term.State`.
  We need access to `Term.State` to store messages and update the info tree.
  Thus, we create an `IO.ref` to track these changes at `Term.State` when we execute `tacticCode`.
  We must set this reference with the current `Term.State` before we execute `simp` using the
  generated `Simp.Discharge`. -/
def tacticToDischarge (tacticCode : Syntax) : TermElabM (IO.Ref Term.State × Simp.Discharge) := do
  let tacticCode ← `(tactic| try ($(⟨tacticCode⟩):tacticSeq))
  let ref ← IO.mkRef (← getThe Term.State)
  let ctx ← readThe Term.Context
  let disch : Simp.Discharge := fun e => do
    let mvar ← mkFreshExprSyntheticOpaqueMVar e `simp.discharger
    let s ← ref.get
    let runTac? : TermElabM (Option Expr) :=
      try
        /- We must only save messages and info tree changes. Recall that `simp` uses temporary metavariables (`withNewMCtxDepth`).
           So, we must not save references to them at `Term.State`.
        -/
        withoutModifyingStateWithInfoAndMessages do
          Term.withSynthesize (postpone := .no) do
            Term.runTactic (report := false) mvar.mvarId! tacticCode .term
          let result ← instantiateMVars mvar
          if result.hasExprMVar then
            return none
          else
            return some result
      catch _ =>
        return none
    let (result?, s) ← liftM (m := MetaM) <| Term.TermElabM.run runTac? ctx s
    ref.set s
    return result?
  return (ref, disch)

/-- Construct a `Simp.DischargeWrapper` from the `Syntax` for a `simp` discharger. -/
private def mkDischargeWrapper (optDischargeSyntax : Syntax) : TermElabM Simp.DischargeWrapper := do
  if optDischargeSyntax.isNone then
    return Simp.DischargeWrapper.default
  else
    let (ref, d) ← tacticToDischarge optDischargeSyntax[0][3]
    return Simp.DischargeWrapper.custom ref d

@[inline] def simpOnlyBuiltins' : List Name := [``eq_self, ``iff_self]
/--
   Create the `Simp.Context` for the `simp`, `dsimp`, and `simp_all` tactics.
   If `kind != SimpKind.simp`, the `discharge` option must be `none`

   TODO: generate error message if non `rfl` theorems are provided as arguments to `dsimp`.

   The argument `simpTheorems` defaults to `getSimpTheorems`,
   but allows overriding with an arbitrary mechanism to choose
   the simp theorems besides those specified in the syntax.
   Note that if the syntax includes `simp only`, the `simpTheorems` argument is ignored.
-/
def mkSimpContext' (stx : Syntax) (eraseLocal : Bool) (kind := SimpKind.simp)
    (ignoreStarArg : Bool := false) (simpTheorems : CoreM SimpTheorems := getSimpTheorems) :
    TermElabM _root_.MkSimpContextResult := do
  if !stx[2].isNone then
    if kind == SimpKind.simpAll then
      throwError "'simp_all' tactic does not support 'discharger' option"
    if kind == SimpKind.dsimp then
      throwError "'dsimp' tactic does not support 'discharger' option"
  let dischargeWrapper ← mkDischargeWrapper stx[2]
  let simpOnly := !stx[3].isNone
  let simpTheorems ←
    if simpOnly then
      simpOnlyBuiltins'.foldlM (·.addConst ·) ({} : SimpTheorems)
    else simpTheorems
  let simprocs ← if simpOnly then pure {} else Simp.getSimprocs
  let congrTheorems ← getSimpCongrTheorems
  let ctx ← Simp.mkContext
     (config := { dsimp := kind == .dsimp })
     (simpTheorems := #[simpTheorems])
     congrTheorems
  let r ← elabSimpArgs stx[4] (eraseLocal := eraseLocal) (kind := kind) (simprocs := #[simprocs]) ctx
  if !r.starArg || ignoreStarArg then
    return { r with dischargeWrapper }
  else
    let ctx := r.ctx
    let simprocs := r.simprocs
    let mut simpTheorems := ctx.simpTheorems
    /-
    When using `zeta := false`, we do not expand let-declarations when using `[*]`.
    Users must explicitly include it in the list.
    -/
    let hs ← getPropHyps
    for h in hs do
      unless simpTheorems.isErased (.fvar h) do
        simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr (config := ctx.indexConfig)
    let ctx := ctx.setSimpTheorems simpTheorems
    return { ctx, simprocs, dischargeWrapper }

def Lean.Expr.runSimp (e : Expr) (stx : TermElabM (TSyntax `tactic)) : TermElabM Simp.Result := do
  let ctx <- mkSimpContext' (← stx) false
  let res <- simp e ctx.ctx (simprocs := ctx.simprocs) (discharge? := none)
  return res.1

def Lean.Expr.runUnfold (e : Expr) (defs : List Name) : TermElabM Expr := do
  let mut eu := e
  for name in defs do eu := (<- unfold eu name).expr
  return eu

-- #check Nat.add_comm

-- example {P : Nat -> Prop} (x : Nat) : P (x + 3 + 4) := by
--   simp only [Nat.add_assoc]


-- #eval do
--   withLocalDeclD `x (mkConst ``Nat) fun x => do
--     let x <- Term.exprToSyntax x
--     let e <- `((fun x => (x + x + x) : Nat -> Nat))
--     let e <- Term.elabTerm e none
--     dbg_trace <- ppExpr e
--     let res <- e.runSimp `(tactic| simp only [Nat.add_assoc])
--     dbg_trace <- ppExpr res.1
--     dbg_trace res.2
--     return res.1.dbgToString
