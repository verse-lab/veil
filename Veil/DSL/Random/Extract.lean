import Veil.DSL.Specification.SpecDef
import Veil.Util.TermSimp

lemma decidable_irrelevance (p : Prop) (i1 i2 : Decidable p) : i1 = i2 := by
  cases i1 <;> cases i2 <;> aesop

section replacement

open Lean Meta Elab Term

/-- A simple matcher that only checks if `e` is in the form of
    `Classical.propDecidable _`. -/
def replaceDecidableInstStepSimpleMatcher (e : Expr) : SimpM (Option Expr) := do
  match_expr e with
  | Classical.propDecidable p => pure <| .some p
  | _ => pure none

/-- A matcher that checks if `e` is of some known forms of `Decidable`
    instances. This applies to more scenarios than the simple one. -/
def replaceDecidableInstStepBasicMatcher (e : Expr) : SimpM (Option Expr) := do
  unless e.containsConst (· == ``Classical.propDecidable) do
    return none
  let res :=
    match_expr e with
    | instDecidableAnd p q _ _ => some <| mkAppN (mkConst ``And) #[p, q]
    | instDecidableOr p q _ _ => some <| mkAppN (mkConst ``Or) #[p, q]
    | instDecidableNot p _ => some <| mkAppN (mkConst ``Not) #[p]
    | _ => none
  pure res

/-- A matcher that checks if `e` is of type `Decidable p` using
    `inferType`. This could be expensive. -/
def replaceDecidableInstStepDeepMatcher (e : Expr) : SimpM (Option Expr) := do
  let ty ← inferType e
  let ty ← instantiateMVars ty
  match_expr ty with
  | Decidable p => pure <| .some p
  | _ => pure none

simproc ↓ replaceDecidableInst (_) := fun e => do
  -- idea: if any of the arguments is a potential target, replace it
  -- and `visit` again; otherwise, `continue`
  -- NOTE: it seems that `simp` will skip instance arguments in the recursion,
  -- so we need to visit all arguments and implement this manually
  let args := e.getAppArgs'
  let args' := args.zip (Array.range args.size)
  let go (mc : Array (Expr → SimpM (Option Expr))) : SimpM (Option (Expr × Nat)) := do
    args'.findSomeM? fun (arg, idx) => do
      let arg := arg.consumeMData
      let tmp := mc.map (· arg)
      if let some res ← tmp.findSomeM? id then pure <| Option.some (res, idx) else pure none
  let some (p, idx) ← go
    #[replaceDecidableInstStepSimpleMatcher,
      replaceDecidableInstStepBasicMatcher,
      replaceDecidableInstStepDeepMatcher] | return .continue
  let arg := args[idx]! |>.consumeMData
  let q ← synthInstance (mkApp (mkConst ``Decidable) p)
  let proof := mkAppN (mkConst ``decidable_irrelevance) #[p, arg, q]
  -- use congruence here
  let f := e.getAppFn'
  let fpre := mkAppN f <| args.take idx
  let proof2 ← mkAppM ``congrArg #[fpre, proof]
  let proof3 ← Array.foldlM (fun subproof sufarg => mkAppM ``congrFun #[subproof, sufarg])
    proof2 (args.drop (idx + 1))
  return .visit { expr := mkAppN f (args.set! idx q), proof? := .some proof3 }

/-- Replacing all `Decidable` instances within a term `t` with those that
    are inferred at the point of running this metaprogram. `idts` specifies
    what definitions to unfold in `t` before doing the replacement. This is
    useful in the case where `t` uses definitions that do not have executable
    code, and by doing the replacement, we want `t` to be executable. -/
def elabDecidableReplaceCore (idts : TSyntaxArray `ident) (t : TSyntax `term)
  (expectedType? : Option Expr) : TermElabM Simp.Result := do
  let things ← idts.mapM resolveGlobalConstNoOverload
  let t ← deltaMore t expectedType? things
  t.simp #[``replaceDecidableInst]

@[inherit_doc elabDecidableReplaceCore]
syntax (name := decidableReplaceElabStx) "decidable_replace% " "[" ident* "] " term : term

open Lean Meta Elab Term in
@[term_elab decidableReplaceElabStx]
def elabDecidableReplace : TermElab := fun stx expectedType? =>
  match stx with
  | `(decidable_replace% [ $idts:ident* ] $t) => do
    let res ← elabDecidableReplaceCore idts t expectedType?
    pure res.expr
  | _ => throwUnsupportedSyntax

end replacement

section label_to_executable_action

-- conceptually, "how to replace `Decidable` instances" and "how to extract
-- their executable versions" are two different things, so we should separate them

open Lean Elab Command Term Meta Lean.Parser

/-- Generate `initComputable` (the computable version of the `after_init`)
    and `nextActComputable` (a function from the `Label` datatype to the
    corresponding `VeilM`) by replacing all `Classical.propDecidable` instances
    inside them with the computable `Decidable` instances inferred at the point of
    running this metaprogram.

    This command is expected to be run inside a `veil module` with sufficiently
    many assumptions made about computable `Decidable` instances so that
    the `Decidable` replacement will be successful. -/
def generateReplacedActions : CommandElabM Unit := do
  let vd ← getSystemParameters
  let spec := (← localSpecCtx.get).spec
  let originalvd := spec.generic.parameters
  -- `vd` might contain additional section variables
  -- NOTE: assume that a prefix of `vd` is the same as `originalvd`, which will be provided as arguments to many things below
  -- this assumption is just for convenience, might be relaxed later
  unless vd.take originalvd.size == originalvd do
    throwError "[generateReplacedActions]: the system parameters {vd} should start with {originalvd}"
  let magicNumber := originalvd.size + 4      -- NOTE: accounting for `ρ` and `σ` stuff; similar below
  let (initComputableCmd, nextActComputableCmd) ← Command.runTermElabM fun vs => do
    -- prepare the usual things
    let sectionArgs ← getSectionArgumentsStx vs
    let sectionArgsPrefix := sectionArgs.take magicNumber
    let labelTypeBinders ← spec.generic.applyGetStateArguments vd
    let labelTypeArgs ← bracketedBindersToTerms labelTypeBinders
    let labelT ← `(term|$labelIdent $labelTypeArgs*)
    -- prepare the names
    let initComputableIdent := mkIdent `initComputable
    let nextActComputableIdent := mkIdent `nextActComputable
    -- build `initComputable`
    let initComputableCmd ← do
      let mainTarget := mkIdent initializerName
      let replacedTarget ← `(term| (decidable_replace% [] (@$mainTarget $sectionArgsPrefix*)))
      `(def $initComputableIdent $[$vd]* : VeilM .external $genericReader $genericState Unit :=
          $replacedTarget)
    /-
      now, build the computable version for each action `a`, each branch in the form of:
      `(fun args => (decidable_replace!% [ds] (@a sectionArgsPrefix args)))`
      where `args` are the arguments to `a` obtained by pattern-matching on the label,
      `ds` are the dependencies to `a` (possibly not computable so needed to be inlined
      via delta-reduction).
    -/
    -- adapted from `assembleLabelType`
    let procNames := spec.procedures.map (fun p => p.name)
    let a_ctions := spec.actions
    let alts ← a_ctions.mapM (fun s => do
      let .some decl := s.actionDecl | unreachable!
      let mainTarget := mkIdent <| toExtName <| decl.name
      -- NOTE: this heuristic could be enhanced
      let dependencies := Array.map Lean.mkIdent #[((decl.name |> toExtName) ++ `withRet)]
      let dependencies := dependencies ++ Array.map Lean.mkIdent procNames
      -- for use with `casesOn` to generated the functions of `ActionLabel`
      let alt ← match s.br with
        | some br => do
          let funArgs ← toFunBinderArray br
          let args ← explicitBindersIdents br
          let replacedTarget ← `(term| (decidable_replace% [$dependencies*] (@$mainTarget $sectionArgsPrefix* $args*)))
          `(term| (fun $funArgs* => $replacedTarget))
        | none => do
          let replacedTarget ← `(term| (decidable_replace% [$dependencies*] (@$mainTarget $sectionArgsPrefix*)))
          `(term| ($replacedTarget))
      pure alt)
    let nextActComputableCmd ← `(
      def $nextActComputableIdent $[$vd]* : $labelT → VeilM .external $genericReader $genericState Unit :=
        fun (l : $labelT) => l.casesOn $alts*
    )
    pure (initComputableCmd, nextActComputableCmd)
  elabCommand initComputableCmd
  trace[veil.debug] "[generateReplacedActions] {initComputableCmd}"
  trace[veil.info] "initActComputable defined"
  elabCommand nextActComputableCmd
  trace[veil.debug] "[generateReplacedActions] {nextActComputableCmd}"
  trace[veil.info] "nextActComputable defined"

@[inherit_doc generateReplacedActions]
elab "#gen_computable_actions" : command => do
  generateReplacedActions

-- this proof seems only doable at the meta-level (not using proof script)
-- so, running the same term elaboration twice

/-- Generate equality proofs about `initComputable` and `nextActComputable`. -/
def generateReplacedActionProofs : CommandElabM Unit := do
  let vd ← getSystemParameters
  let spec := (← localSpecCtx.get).spec
  let originalvd := spec.generic.parameters
  let magicNumber := originalvd.size + 4
  -- for `initComputable`
  let (initFinalGoal, initFinalProof) ← Command.runTermElabM fun vs => do
    let init ← resolveGlobalConstNoOverloadCore initializerName
    let initComputable ← resolveGlobalConstNoOverloadCore `initComputable
    let lhsTerm ← mkAppOptM init ((vs.take magicNumber |>.map Option.some))
    let rhsTerm ← mkAppOptM initComputable ((vs.map Option.some))
    let goal ← mkEq lhsTerm rhsTerm
    trace[veil.debug] "goal: {goal}"
    let res ← elabDecidableReplaceCore' #[] lhsTerm
    let proof ← res.getProof
    trace[veil.debug] "proof: {proof}"
    let finalProof ← mkLambdaFVars vs proof
    check finalProof
    let finalProof ← instantiateMVars finalProof
    trace[veil.debug] "finalProof: {finalProof}"
    let finalGoal ← mkForallFVars vs goal
    let _ ← ensureHasType finalGoal finalProof
    let finalGoal ← instantiateMVars finalGoal
    pure (finalGoal, finalProof)
  -- for `nextActComputable`
  let (nextFinalGoal, nextFinalProof) ← Command.runTermElabM fun vs => do
    -- get label type
    let labelTypeBinders ← spec.generic.applyGetStateArguments vd
    let labelTypeArgs ← bracketedBindersToTerms labelTypeBinders
    -- NOTE: this is highly heuristic, but no better way to do this?
    let labelT ← elabTerm (← `(term|$labelIdent $labelTypeArgs*)) (.some <| .sort <| .succ .zero)
    -- the statement to prove
    let (goal, motive) ← withLocalDeclD `l labelT fun l => do
      let nextAct ← resolveGlobalConstNoOverloadCore `NextAct
      let nextActComputable ← resolveGlobalConstNoOverloadCore `nextActComputable
      let lhsTerm ← mkAppOptM nextAct ((vs.take magicNumber |>.map Option.some) ++ #[some l])
      let rhsTerm ← mkAppOptM nextActComputable ((vs.map Option.some) ++ #[some l])
      let goalWithoutForallArgs ← mkEq lhsTerm rhsTerm
      let motive ← liftMetaM <| mkLambdaFVars #[l] goalWithoutForallArgs
      let goal ← liftMetaM <| mkForallFVars #[l] goalWithoutForallArgs
      pure (goal, motive)
    trace[veil.debug] "motive: {motive}, goal: {goal}"
    -- do the proof
    let proof ← withLocalDeclD `l labelT fun l => do
      let name ← resolveGlobalConstNoOverloadCore (labelName ++ `casesOn)
      let casesOn ← mkAppOptM name ((Array.replicate labelTypeBinders.size none) ++ #[some motive, some l])
      trace[veil.debug] "casesOn: {casesOn}"
      -- get all clauses by `inferType`
      let ty ← inferType casesOn
      -- get the core proofs by rerunning `elabDecidableReplaceCore`
      let alts ← forallTelescope ty fun xs _ => do
        let procNames := spec.procedures.map (fun p => p.name)
        let a_ctions := spec.actions
        unless a_ctions.size == xs.size do
          throwError "failed due to unknown reason"
        a_ctions.zip xs |>.mapM (fun (s, clause) => do
          let .some decl := s.actionDecl | unreachable!
          let clauseArgs ← inferType clause
          forallTelescope clauseArgs fun funArgs _ => do
            let mainTarget := toExtName <| decl.name
            let mainTarget ← resolveGlobalConstNoOverloadCore mainTarget
            let mainTarget ← mkAppOptM mainTarget ((vs.take magicNumber |>.map Option.some) ++ funArgs.map Option.some)
            let dependencies := #[((decl.name |> toExtName) ++ `withRet)]
            let dependencies := dependencies ++ procNames
            let res ← elabDecidableReplaceCore' dependencies mainTarget
            let subproof ← res.getProof
            liftMetaM <| mkLambdaFVars funArgs subproof
        )
      let tmp ← mkAppM' casesOn alts
      liftMetaM <| mkLambdaFVars #[l] tmp
    let finalProof ← mkLambdaFVars vs proof
    check finalProof
    let finalProof ← instantiateMVars finalProof
    let finalGoal ← mkForallFVars vs goal
    let _ ← ensureHasType finalGoal finalProof
    let finalGoal ← instantiateMVars finalGoal
    pure (finalGoal, finalProof)
  -- add the prefix
  let moduleName ← getCurrNamespace
  Command.liftCoreM <| simpleAddTheorem (moduleName ++ `replaced_init_eq) [] initFinalGoal initFinalProof false
  Command.liftCoreM <| simpleAddTheorem (moduleName ++ `replaced_actions_eq) [] nextFinalGoal nextFinalProof false
where
  elabDecidableReplaceCore' (idts : Array Name) (t : Expr) : TermElabM Simp.Result := do
    let things ← idts.mapM resolveGlobalConstNoOverloadCore
    let t ← deltaMoreCore t things
    t.simp #[``replaceDecidableInst]

@[inherit_doc generateReplacedActionProofs]
elab "#gen_computable_action_equality_proofs" : command => do
  generateReplacedActionProofs

/-- Doing both `#gen_computable_actions` and
    `#gen_computable_action_equality_proofs` in one go. -/
elab "#gen_computable" : command => do
  generateReplacedActions
  generateReplacedActionProofs

/-- Generate `initExec` (the `VeilExecM` version of the
    `after_init`) and a function `nextActExec` from label to the
    corresponding `VeilExecM`. Also generate a lemma similar to
    `next_refine` for `nextActExec`. These are achieved by two steps:
    first generate a function `nextExtract` from label to the
    corresponding `ExtractNonDet` using the provided `extractNonDet`
    (which can be a tactic), and then `nextActExec` is defined
    as a thin wrapper around `nextExtract` and the lemma is proved
    using `nextActExec` and the `next_refine` lemma.

    This command is expected to be run inside a `veil module` with sufficiently
    many assumptions made about `ExtractNonDet` so that
    their synthesis will be successful. -/
def generateVeilExecM (extractNonDet : TSyntax `term) (useWeak : Bool := true) : CommandElabM Unit := do
  let vd ← getSystemParameters
  let spec := (← localSpecCtx.get).spec
  let originalvd := spec.generic.parameters
  let magicNumber := originalvd.size + 4
  let (initExecCmd, nextExtractFuncCmd, nextActExecCmd, nextExecRefineCmd) ← Command.runTermElabM fun vs => do
    -- prepare the usual things
    let sectionArgs ← getSectionArgumentsStx vs
    let sectionArgsPrefix := sectionArgs.take magicNumber
    -- prepare the names
    let initExecIdent := mkIdent `initExec
    let nextExtractIdent := mkIdent `nextExtract
    let nextActExecIdent := mkIdent `nextActExec
    let nextActComputable ← resolveGlobalConstNoOverloadCore `nextActComputable
    let findable := mkIdent <| (if useWeak then ``WeakFindable else ``Findable)
    let extractor := mkIdent <| (if useWeak then ``NonDetT.extractWeak else ``NonDetT.extract)
    -- build `initExec`
    let initExecCmd ← do
      let initComputable ← resolveGlobalConstNoOverloadCore `initComputable
      let initComputableIdent := mkIdent initComputable
      `(def $initExecIdent $[$vd]* : VeilExecM .external $genericReader $genericState Unit :=
        ($extractor (@$initComputableIdent $sectionArgs*) $extractNonDet))
    -- build `nextExtract`
    let a_ctions := spec.actions
    let alts ← a_ctions.mapM (fun s => do
      let alt ← match s.br with
        | some br => do
          let funArgs ← toFunBinderArray br
          `(term| (fun $funArgs* => $extractNonDet))
        | none => `(term| ($extractNonDet))
      pure alt)
    let lIdent := mkIdent `l
    let target1 := Syntax.mkApp (← `(term| @$(mkIdent nextActComputable))) (sectionArgs ++ #[lIdent])
    let nextExtractFuncCmd ← `(
      def $nextExtractIdent $[$vd]* : ∀ $lIdent, ExtractNonDet $findable ($target1) :=
        fun l => l.casesOn $alts*
    )
    -- build `nextActExec`
    let target2 := Syntax.mkApp (← `(term| @$nextExtractIdent)) (sectionArgs ++ #[lIdent])
    let nextActExecCmd ← `(
      def $nextActExecIdent $[$vd]* :=
        fun $lIdent => $extractor ($target1) ($target2)
    )
    -- prove `next_exec_refine`
    let systemInQuestion ← resolveGlobalConstNoOverloadCore `System
    let nextRefineLemma ← resolveGlobalConstNoOverloadCore `next_refine
    let otherIdents := Array.map Lean.mkIdent #[`rd, `st, `st']
    let target3 := Syntax.mkApp (← `(term| @$nextActExecIdent)) (sectionArgs ++ #[lIdent])
    let target4 := Syntax.mkApp (← `(term| @$(mkIdent systemInQuestion))) sectionArgsPrefix
    let target5 := Syntax.mkApp (← `(term| @$(mkIdent nextRefineLemma))) (sectionArgsPrefix ++ otherIdents ++ #[lIdent])
    let nextExecRefineCmd ← `(
      theorem $(mkIdent `next_exec_refine) $[$vd]* $lIdent : ∀ (rd : $genericReader) (st st' : $genericState),
        ($target3).operational rd st st' (Except.ok ()) →
        ($target4).nextLab rd st $lIdent st' := by
        intro $[$otherIdents]* h
        have htmp := $target5
        rw [$(mkIdent `replaced_actions_eq):ident] at htmp
        apply htmp ($target2) h
    )
    pure (initExecCmd, nextExtractFuncCmd, nextActExecCmd, nextExecRefineCmd)
  elabCommand initExecCmd
  trace[veil.debug] "[generateVeilExecM] {initExecCmd}"
  trace[veil.info] "initExec defined"
  elabCommand nextExtractFuncCmd
  trace[veil.debug] "[generateVeilExecM] {nextExtractFuncCmd}"
  trace[veil.info] "nextExtract defined"
  elabCommand nextActExecCmd
  trace[veil.debug] "[generateVeilExecM] {nextActExecCmd}"
  trace[veil.info] "nextActExec defined"
  elabCommand nextExecRefineCmd
  trace[veil.debug] "[generateVeilExecM] {nextExecRefineCmd}"
  trace[veil.info] "next_exec_refine proved"

@[inherit_doc generateVeilExecM]
elab "#gen_executable" : command => do
  let tac ← `(term| by extract_tactic)
  generateVeilExecM tac

end label_to_executable_action
