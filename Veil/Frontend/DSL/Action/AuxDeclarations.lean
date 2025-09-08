import Veil.Frontend.DSL.Action.WPGen
import Veil.Frontend.DSL.Module.Util

/-! # Auxiliary Declarations for Veil actions

    This file contains the utilities for defining auxiliary declarations
    for Veil actions, including their weakest preconditions (WPs),
    equality theorems between the WPs before/after simplification, and
    their two-state versions.
-/

-- TODO add back `smtSimp` and `quantifierSimp` when ready; for example, transition version needs simp for `compl`
-- TODO allow definition/theorem names in `simps`?
-- TODO the shape of `act.exTr_eq` is not exactly the same as before, would that be a problem?

namespace Veil

open Lean Meta Elab Term

/-- `sourceName` should be a full name, indicating where to obtain the information of
    arguments. Names in `unfolds` should be fully qualified.
    `defStx argIdents` should return the syntax of a term, assuming all variables
    from `argIdents` are already in the local context.
    `simps` only represents simp attributes here; definition/theorem names are not allowed. -/
private def simplifyAndDefine
  (sourceName : Name)
  (defName : Name)
  (defStx : Array Ident → TermElabM Term)
  (unfolds : Array Name)
  (preSimp? : Option (Array Expr → Expr → TermElabM (Expr × Expr)))
  (simps : Array Name)
  (attrs : Array Attribute := #[]) : TermElabM (Name × Expr × (Array Expr → Expr)) := do
  trace[veil.debug] "[{decl_name%}] defining {defName}"
  let info ← getConstVal sourceName
  -- `pree`: the elaboration result of `defStx`
  let pree ← forallTelescope info.type fun args _ => do
    let argIdents ← args.mapM (fun a => mkIdent <$> a.fvarId!.getUserName)
    let stx ← defStx argIdents
    let res ← withoutErrToSorry $ elabTermAndSynthesize stx none
    let res ← instantiateMVars res
    mkLambdaFVars args res (usedOnly := true)   -- since some variables can be captured by `∃` inside `defStx`
  let preeArgsNum := pree.getNumHeadLambdas
  let e ← if unfolds.isEmpty then pure pree else deltaExpand pree fun n => n ∈ unfolds
  -- `e` here would be a function, and typically we only want to simplify its body;
  -- we do so inside `lambdaTelescope`. Also, `e` might contain more arguments than `pree`,
  -- but the proof might depend on the arguments of `pree` only, so we do `lambdaBoundedTelescope`.

  -- `e'` is the final simplified `e` (a function)
  -- `partialProof` is the equality proof of the __body__ before and after simplification
  let (e', partialProof) ← lambdaBoundedTelescope e preeArgsNum fun xs body => do
    -- Optionally do some pre-simplification (e.g., WP generation)
    let (e1, proof1) ← match preSimp? with
      | some f => f xs body
      | none => pure (body, ← mkEqRefl body)
    let (e2, proof2) ← if simps.isEmpty then pure (e1, proof1) else do
      let simpResult ← e1.simp simps
      let proof2 ← match simpResult.proof? with
        | some pf => mkEqTrans proof1 pf
        | none => pure proof1
      pure (simpResult.expr, proof2)
    let e' ← mkLambdaFVars xs e2
    pure (e', proof2.replaceFVars xs)
  let fullDefName ← addVeilDefinition defName e' (attr := attrs)
    (applyAttrTime := if attrs.isEmpty then .some .beforeElaboration else .none)
  return (fullDefName, pree, partialProof)

/-- Given `pree = fun xs => body`, `defName =delta= fun xs => body'`
    and `partialProof` being the proof of `body = body'`,
    this function defines the equality theorem `∀ xs, body = defName xs`.

    `defName` should be fully qualified. -/
private def proveEqAboutBody
  (pree : Expr)
  (partialProof : Array Expr → Expr)
  (defName theoremName : Name)
  (attrs : Array Attribute := #[]) : TermElabM Unit := do
  let (theoremStatement, proof) ← lambdaTelescope pree fun xs lhs => do
    let rhs ← mkAppOptM defName $ xs.map Option.some
    let eq ← mkEq lhs rhs
    pure (← mkForallFVars xs eq, ← mkLambdaFVars xs (partialProof xs))
  let theoremStatement ← instantiateMVars theoremStatement
  let proof ← instantiateMVars proof
  -- CHECK separate the following out to be a subprocedure?
  addDecl <| Declaration.thmDecl <| mkTheoremValEx theoremName [] theoremStatement proof []
  enableRealizationsForConst theoremName
  unless attrs.isEmpty do
    applyAttributes theoremName attrs

def defineWpForAction (preSimp : Array Expr → Expr → TermElabM (Expr × Expr)) (unfoldSelf? : Bool) (sourceName defName : Name) := do
  let (hdIdent, postIdent) := (mkIdent `hd, mkIdent `post)
  simplifyAndDefine sourceName defName
    (fun argIdents =>
      `(fun $hdIdent $postIdent => [IgnoreEx $hdIdent| $(mkIdent ``wp) (@$(mkIdent sourceName) $argIdents*) $postIdent]))
    (if unfoldSelf? then #[sourceName] else #[])
    (Option.some preSimp)
    #[]
    (attrs := #[{name := `wpDefUnfoldSimp}])

/-- Defines the weakest precondition for the action specialised to the case where the
  exception handler is `True`. -/
def defineWpSuccForAction (sourceName wpName defName : Name) := do
  let postIdent := mkIdent `post
  simplifyAndDefine sourceName defName
    (fun argIdents =>
      `(fun $postIdent => @$(mkIdent wpName) $argIdents* (fun _ => $(mkIdent ``True)) $postIdent))
    #[wpName] Option.none #[]

/-- Defines the weakest precondition for the action specialised to the case where the
  exception handler allows all exceptions except the one given. -/
def defineWpExForAction (sourceName wpName defName : Name) := do
  let (exIdent, postIdent) := (mkIdent `ex, mkIdent `post)
  simplifyAndDefine sourceName defName
    (fun argIdents =>
      `(fun $exIdent $postIdent => @$(mkIdent wpName) $argIdents* (· ≠ $exIdent) $postIdent))
    #[wpName] Option.none #[]

def deriveTransitionVersion (sourceName wpSuccName defName : Name) := do
  let name1 := ``VeilSpecM.toTransitionDerived
  simplifyAndDefine sourceName defName
    (fun argIdents =>
      `($(mkIdent name1) <| @$(mkIdent wpSuccName) $argIdents*))
    #[wpSuccName, name1, ``Cont.inv] Option.none #[]

def deriveExQuantifiedTransitionVersion (br : Option (TSyntax ``explicitBinders)) (sourceName actTransitionName defName : Name) := do
  let (rIdent, sIdent, s'Ident) := (mkIdent `r, mkIdent `s, mkIdent `s')
  simplifyAndDefine sourceName defName
    (fun argIdents =>
      `(fun $rIdent $sIdent $s'Ident => exists? $br ?, @$(mkIdent actTransitionName) $argIdents* $rIdent $sIdent $s'Ident))
    #[actTransitionName] Option.none #[]

/-
Considerations:
- Since `act.do` is parameterized by `mode`, certain parts of its WP will
  be parameterized by `mode` as well. For those parts, we can either
  (1) use carefully crafted rewriting rules to avoid formula size blowup, or
  (2) rewrite them after determining the `mode`.
  Currently we use (1).
- `act` and `act.ext` are simplified versions of `act.do` in different modes;
  they do not contain `act.do` as a subterm. However, we want to reuse the WP(s)
  of `act.do` for both of them. Currently this is done in the following way,
  assuming we are simplifying `wp act`:
  - We know that `wp act` is definitionally equal to `wp (@act.do Mode.internal)`.
  - So using `act.do.wp_eq`, we can rewrite `wp act` to `@act.do.wpGen Mode.internal`.
    By configuring `preSimp?`, we can easily insert this step.
  For `wp act.ext post`, it is definitionally equal to
  `wp (VeilM.returnUnit $ @act.do Mode.external) post`, which can be rewritten into
  `@act.do.wpGen Mode.external (fun _ => post ())` using `wp_bind`, `wp_pure`
  and `act.do.wp_eq`. For convenience, we prove a specialized theorem for
  doing all these at once.

  Note that `act.do` is marked `reducible`, otherwise we only need to do the
  first step of rewriting, and then rely on the core WP generation procedure.
  A possible alternative is to "hide" `act.do` behind another semireducible
  definition and then proceed.
-/

private def switchToDoWp (sourceName : Name) (mode : Mode) (xs : Array Expr) : TermElabM (Expr × Expr) := do
  let doName := toDoName sourceName.getRoot
  let wpEqThmName ← resolveGlobalConstNoOverloadCore (toWpEqName doName)
  let wpEqThmInfo ← getConstInfo wpEqThmName
  let partiallyAppliedThm := mkApp (← mkConstWithFreshMVarLevels wpEqThmName) mode.expr
  let (eq, proof) ← match mode with
  | .external =>
    -- here leverage the fact that the last argument of `xs` is `post`
    let proof ← mkAppM ``VeilM.wp_returnUnit #[mkAppN partiallyAppliedThm xs.pop, xs.back!]
    let wpEq' ← inferType proof
    let wpEq' ← instantiateMVars wpEq'
    pure (wpEq', proof)
  | .internal =>
    let wpEq ← instantiateForall wpEqThmInfo.type #[mode.expr] >>= (instantiateForall · xs)
    pure (wpEq, mkAppN partiallyAppliedThm xs)
  let .some (_, _, rhs) := eq.eq? | throwError "{eq} is not an equality!"
  let proof ← instantiateMVars proof
  trace[veil.debug] "[{decl_name%}] rhs: {rhs}"
  -- `act.do.wpGen` should be simplified, so here only do `dsimp`
  let rhs' ← whnfD rhs
  let rhs' ← rhs'.dsimp #[]
  trace[veil.debug] "[{decl_name%}] rhs': {rhs'}"
  return (rhs', proof)

/-- `sourceName` should be short (e.g., `act.do`), while `fullSourceName` should be
    fully qualified (e.g., `MyModule.act.do`).
    When `mode?` is `none`, the following is for `act.do`. -/
def defineAuxiliaryDeclarations
  (pi : ProcedureInfo)
  (mode? : Option Mode)
  (br : Option (TSyntax ``explicitBinders))
  (sourceName fullSourceName : Name) : TermElabM Unit := do
  let fullWpName ← do
    let wpName := toWpName sourceName
    let preSimp? := match mode? with
      | some m => (fun xs _ => switchToDoWp sourceName m xs)
      | none => (fun _ => wpGenBySimprocCore)
    let (fullWpName, pree, partialProof) ← defineWpForAction preSimp? mode?.isNone fullSourceName wpName
    proveEqAboutBody pree partialProof fullWpName (toWpEqName sourceName) (attrs := #[{name := `wpEqSimp}])
    pure fullWpName

  unless pi matches .procedure _ do
    let fullWpSuccName ← do
      let wpSuccName := toWpSuccName sourceName
      let (fullWpSuccName, pree, partialProof) ← defineWpSuccForAction fullSourceName fullWpName wpSuccName
      proveEqAboutBody pree partialProof fullWpSuccName (toWpSuccEqName sourceName)
      pure fullWpSuccName

    let _ ← do
      let wpExName := toWpExName sourceName
      let (fullWpExName, pree, partialProof) ← defineWpExForAction fullSourceName fullWpName wpExName
      proveEqAboutBody pree partialProof fullWpExName (toWpExEqName sourceName)

    if mode? matches .some .external then
      let fullActTransitionName ← do
        let actTransitionName := toTransitionName sourceName
        let (fullActTransitionName, pree, partialProof) ← deriveTransitionVersion fullSourceName fullWpSuccName actTransitionName
        proveEqAboutBody pree partialProof fullActTransitionName (toTransitionEqName sourceName)
        pure fullActTransitionName

      -- TODO define end-to-end equality theorem if needed

      let _ ← do
        let actExTrName := toExQuantifiedTransitionName sourceName
        let (fullActExTrName, pree, partialProof) ← deriveExQuantifiedTransitionVersion br fullSourceName fullActTransitionName actExTrName
        proveEqAboutBody pree partialProof fullActExTrName (toExQuantifiedTransitionEqName sourceName)

end Veil
