import Veil.DSL.Specification.SpecDef
import Veil.Util.TermSimp

lemma decidable_irrelevance (p : Prop) (i1 i2 : Decidable p) : i1 = i2 := by
  cases i1 <;> cases i2 <;> aesop

-- NOTE: the following two are specialized versions of lemmas for `Decidable` replacement
-- they should be removed once the `Decidable` replacement is more generic
lemma ite_decidable_irrelevance c (e1 e2 : α) (i1 i2 : Decidable c) :
  @ite _ c i1 e1 e2 = @ite _ c i2 e1 e2 := by congr

lemma VeilM.assert_decidable_irrelevance
  {m : Mode} {ρ σ : Type} (p : Prop) (ex : ℤ) (i1 i2 : Decidable p) :
  @VeilM.assert m ρ σ p i1 ex = @VeilM.assert m ρ σ p i2 ex := by congr

-- TODO move these two somewhere else
instance ExtractNonDet.pick' {τ : Type u} [Inhabited τ] :
  ExtractNonDet Findable (MonadNonDet.pick (m := NonDetT m) τ) := by
    dsimp [MonadNonDet.pick, NonDetT.pickSuchThat]; constructor
    apply Findable.mk (some default) <;> simp
    intro ; constructor

instance ExtractNonDet.pick_weak' {τ : Type u} [Inhabited τ] :
  ExtractNonDet WeakFindable (MonadNonDet.pick (m := NonDetT m) τ) := by
    dsimp [MonadNonDet.pick, NonDetT.pickSuchThat]; constructor
    apply WeakFindable.mk (some default) ; simp
    intro ; constructor

section replacement

open Lean Meta Elab Term

simproc ↓ replaceDecidableInst (ite _ _ _) := fun e => do
  let_expr ite α c h e1 e2 := e | return .continue
  let_expr Classical.propDecidable _ := h | return .continue
  let q ← synthInstance (mkApp (mkConst ``Decidable) c)
  let proof := mkAppN (mkConst ``ite_decidable_irrelevance) #[c, e1, e2, h, q]
  let res ← mkAppOptM ``ite #[some α, some c, some q, some e1, some e2]
  return .done { expr := res, proof? := some proof }

simproc ↓ replaceDecidableInst2 (VeilM.assert _ _) := fun e => do
  let_expr VeilM.assert m ρ σ p i1 ex := e | return .continue
  let_expr Classical.propDecidable _ := i1 | return .continue
  let i2 ← synthInstance (mkApp (mkConst ``Decidable) p)
  let proof := mkAppN (mkConst ``VeilM.assert_decidable_irrelevance) #[m, ρ, σ, p, ex, i1, i2]
  let res ← mkAppOptM ``VeilM.assert #[some m, some ρ, some σ, some p, some i2, some ex]
  return .done { expr := res, proof? := some proof }

/-- Replacing all `Decidable` instances within a term `t` with those that
    are inferred at the point of running this metaprogram. `idts` specifies
    what definitions to unfold in `t` before doing the replacement. This is
    useful in the case where `t` uses definitions that do not have executable
    code, and by doing the replacement, we want `t` to be executable. -/
def elabDecidableReplaceCore (idts : TSyntaxArray `ident) (t : TSyntax `term)
  (expectedType? : Option Expr) : TermElabM Simp.Result := do
  let things ← idts.mapM resolveGlobalConstNoOverload
  let t ← deltaMore t expectedType? things
  t.simp #[``replaceDecidableInst, ``replaceDecidableInst2]

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

open Lean Elab Command Term Meta Lean.Parser

/-- Used for generating `initExec` (the `VeilExecM` version of the
    `after_init`) and a function `nextActExec` from label to the
    corresponding `VeilExecM`.
    It is expected to be run inside a `veil module` with sufficiently
    many assumptions made about computable `Decidable` instances so that
    the `Decidable` replacement will be successful. -/
def generateVeilExecM (extractNonDet : TSyntax `term) (useWeak : Bool := true) : CommandElabM Unit := do
  let vd ← getSystemParameters
  let spec := (← localSpecCtx.get).spec
  let originalvd := spec.generic.parameters
  -- `vd` might contain additional section variables
  -- NOTE: assume that a prefix of `vd` is the same as `originalvd`, which will be provided as arguments to many things below
  -- this assumption is just for convenience, might be relaxed later
  unless vd.take originalvd.size == originalvd do
    throwError "[assembleNextFuncToExecM]: the system parameters {vd} should start with {originalvd}"
  let magicNumber := originalvd.size + 4      -- NOTE: accounting for `ρ` and `σ` stuff
  let (initExecCmd, nextActExecCmd) ← Command.runTermElabM fun vs => do
    -- prepare the usual things
    let sectionArgs ← getSectionArgumentsStx vs
    let sectionArgsPrefix := sectionArgs.take magicNumber
    let labelTypeBinders ← spec.generic.applyGetStateArguments vd
    let labelTypeArgs ← bracketedBindersToTerms labelTypeBinders
    let labelT ← `(term|$labelIdent $labelTypeArgs*)
    -- prepare the names
    let initExecIdent := mkIdent `initExec
    let nextActExecIdent := mkIdent `nextActExec
    let extractor := mkIdent <| (if useWeak then ``NonDetT.extractWeak else ``NonDetT.extract)
    -- build `initExec`
    let initExecCmd ← do
      let mainTarget := mkIdent initializerName
      let replacedTarget ← `(decidable_replace% [] (@$mainTarget $sectionArgsPrefix*))
      `(def $initExecIdent $[$vd]* : VeilExecM .external $genericReader $genericState Unit :=
        ($extractor $replacedTarget $extractNonDet))
    /-
      now, build the executable version for each action `a`, each branch in the form of:
      `(fun args => NonDetT.extract(Weak) (decidable_replace!% [ds] (@a sectionArgsPrefix args)) tac)`
      where `args` are the arguments to `a` obtained by pattern-matching on the label,
      `ds` are the dependencies to `a` (possibly not computable so needed to be inlined
      via delta-reduction), and `tac` is the tactic for solving `NonDetT.extract`.
    -/
    -- adapted from `assembleLabelType`
    let a_ctions := spec.actions
    let alts ← a_ctions.mapM (fun s => do
      let .some decl := s.actionDecl | unreachable!
      let mainTarget := mkIdent <| toExtName <| decl.name
      let dependencies := Array.map Lean.mkIdent #[((decl.name |> toExtName) ++ `withRet)]
      -- for use with `casesOn` to generated the functions of `ActionLabel`
      let alt ← match s.br with
        | some br => do
          let funArgs ← toFunBinderArray br
          let args ← explicitBindersIdents br
          let replacedTarget ← `(term| (decidable_replace% [$dependencies*] (@$mainTarget $sectionArgsPrefix* $args*)))
          `(term| (fun $funArgs* => $extractor $replacedTarget $extractNonDet))
        | none => do
          let replacedTarget ← `(term| (decidable_replace% [$dependencies*] (@$mainTarget $sectionArgsPrefix*)))
          `(term| ($extractor $replacedTarget $extractNonDet))
      pure alt)
    let nextActExecCmd ← `(
      def $nextActExecIdent $[$vd]* : $labelT → VeilExecM .external $genericReader $genericState Unit :=
        fun (l : $labelT) => l.casesOn $alts*
    )
    pure (initExecCmd, nextActExecCmd)
  elabCommand initExecCmd
  trace[veil.debug] "[generateVeilExecM] {initExecCmd}"
  trace[veil.info] "initActExec defined"
  elabCommand nextActExecCmd
  trace[veil.debug] "[generateVeilExecM] {nextActExecCmd}"
  trace[veil.info] "nextActExec defined"

@[inherit_doc generateVeilExecM]
elab "#gen_executable" : command => do
  let tac ← `(term| by extract_tactic)
  generateVeilExecM tac

end label_to_executable_action
