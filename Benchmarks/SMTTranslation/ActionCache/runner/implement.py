from pathlib import Path
r=Path('/home/george/src/veil-issue-123')
p=r/'Veil/Core/Tools/ModelChecker/Symbolic/TraceLang.lean'; s=p.read_text()
# Share the exact syntax constructors between cache generation and trace queries.
chunks=[]
for start,end in [('/-- Generated connectives','def parseTraceSpec'),('open Lean.Parser.Term in','/-- Accumulated binders'),('/-- Create both bracketed','/-- Create a tag binder'),('/-- Instantiate a parameter type','/-- State threaded')]:
 a=s.index(start); b=s.index(end,a); chunks.append(s[a:b]); s=s[:a]+s[b:]
shared='module\n\npublic meta import Veil.Frontend.DSL.Module.Util\n\npublic meta section\nnamespace Veil\nopen Lean Elab Term Meta\n\n'+''.join(chunks).replace('private def ', 'def ')+'\nend Veil\n'
(r/'Veil/Frontend/DSL/Module/Util/TraceTemplates.lean').write_text(shared)
s=s.replace('public meta import Veil.Frontend.DSL.Infra.TraceSyntax','public meta import Veil.Frontend.DSL.Module.Util.TraceTemplates\npublic meta import Veil.Frontend.DSL.Infra.TraceSyntax');p.write_text(s)
p=r/'Veil/Base.lean';s=p.read_text();i=s.index('register_option veil.deferVCGeneration')
s=s[:i]+'''register_option veil.experimental.bmcCache : Bool := {
  defValue := false
  descr := "Precompute exact symbolic transition normal forms at specification setup and reuse them in veil_bmc. Set before #gen_spec; unmatched formulas use ordinary normalization."
}

'''+s[i:];p.write_text(s)
p=r/'Veil/Frontend/DSL/Infra/Simp.lean';s=p.read_text().replace('register_simp_attr nextSimp','''register_simp_attr nextSimp

/-- Exact, specialized transition equalities for BMC. Applied only at a clause's
root, never as recursive simplification rules. -/
register_simp_attr bmcNormalize''');p.write_text(s)
(r/'Veil/Frontend/DSL/Module/Util/BmcCache.lean').write_text('''module

public meta import Veil.Frontend.DSL.Module.Util.TraceTemplates
public meta import Veil.Frontend.DSL.Infra.Quantifiers

public meta section
namespace Veil
open Lean Elab Command Term Meta

/-- Normalize under a closed parameter telescope and save an exact equality.
Every state, action argument (including its dependencies), universe and instance
is bound by the theorem. No query-local expressions or chosen witnesses are
stored. In particular, the ordinary hoister must prove every Nonempty condition.
The theorem contains its normal form, so using it requires no proof replay. -/
private def saveBmcNormalForm (name : Name)
    (binders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) (body : Term) : TermElabM Unit := do
  elabBinders binders fun xs => do
    let lhs ← withoutErrToSorry <| elabTermAndSynthesize body (some (mkSort .zero))
    let unfolded ← Simp.simp #[`nextSimp] { instances := true } lhs
    let hoisted ← if ← hasHOQuantification unfolded.expr then
        Simp.simp #[`existsQuantifierSimp] {} unfolded.expr
      else pure { expr := unfolded.expr }
    let result ← unfolded.mkEqTrans hoisted
    let type ← instantiateMVars (← mkForallFVars xs (← mkEq lhs result.expr))
    let value ← instantiateMVars (← mkLambdaFVars xs (← result.getProof))
    unless !type.hasFVar && !type.hasMVar && !value.hasFVar && !value.hasMVar do
      throwError "BMC normal form contains unbound parameters"
    -- Use the declaration elaborator for universe generalization and kernel
    -- checking, rather than installing a theorem with an empty level telescope.
    let type ← Term.exprToSyntax type
    let value ← Term.exprToSyntax value
    elabCommand (← `(command| @[bmcNormalize] theorem $(mkIdent name) : $type := $value))

/-- Cache init, named transitions and the complete disjunction used by `any
 action`. Sharing the builders with TraceLang keeps action tags and dependent
 argument telescopes identical. Assertions and proof headers retain the ordinary
 normalization path. Disabled by default while the performance tradeoff is
 measured. -/
def Module.generateBmcNormalForms (mod : Module) : CommandElabM Unit := do
  unless veil.experimental.bmcCache.get (← getOptions) do return
  liftTermElabM do
    let sorts ← mod.uninterpretedParamIdents
    let theoryT ← mod.theoryStx
    let stateT ← `(term| $(mkIdent stateName) ($fieldAbstractDispatcher $sorts*))
    let rts ← `(term| @$assembledRTS $sorts*)
    let th := mkIdent `th
    let pre := mkIdent `pre
    let post := mkIdent `post
    let base := (← collectModuleBinders mod).map (·.1)
    let states := #[← `(bracketedBinder| ($th : $theoryT)),
                    ← `(bracketedBinder| ($pre $post : $stateT))]
    saveBmcNormalForm `__bmc_init_eq (base ++ states)
      (← `(term| ($rts).$(mkIdent `init) $th $post))
    for act in mod.actions do
      let (_, params) ← mod.declarationAllParams act.name act.declarationKind
      let (args, bindings) ← mkParamBinders params s!"_act_{act.name}"
      let label := mkIdent (labelTypeName ++ act.name)
      let expr ← `(term| ($rts).$(mkIdent `tr) $th $pre ($label $args*) $post)
      saveBmcNormalForm (`__bmc_action ++ act.name ++ `eq)
        (base ++ states ++ bindings.map (·.1)) expr
    if mod.actions.size > 1 then
      let tag := mkIdent `tag
      let (body, args) ← mkAnyActionDisjunction mod rts th pre post tag 0
      let tags := (← mkActionTagBinders).map (·.1)
      saveBmcNormalForm `__bmc_any_eq
        (base ++ tags ++ #[← `(bracketedBinder| ($tag : $actionTagType))] ++ states ++ args.map (·.1)) body

end Veil
''')
p=r/'Veil/Frontend/DSL/Module/Elaborators/Verification.lean';s=p.read_text().replace('public meta import Veil.Frontend.DSL.Module.Elaborators.Core','public meta import Veil.Frontend.DSL.Module.Util.BmcCache\npublic meta import Veil.Frontend.DSL.Module.Elaborators.Core').replace('  Verifier.runManager\n  mod.generateDoesNotThrowVCs','  mod.generateBmcNormalForms\n  Verifier.runManager\n  mod.generateDoesNotThrowVCs');p.write_text(s)
p=r/'Veil/Frontend/DSL/Tactic/Core.lean';s=p.read_text();i=s.index('/-- `veil_smt` selects hypotheses')
s=s[:i]+'''/-- Apply a stored exact equality at the clause root and stop. In particular,
do not traverse/hoist its already-normalized result again. A miss uses precisely
the ordinary two normalization passes, with proofs composed by transitivity. -/
def bmcNormalizeClause : Lean.Meta.Simp.Simproc := fun e => do
  if veil.experimental.bmcCache.get (← getOptions) then
    let some ext ← getSimpExtension? `bmcNormalize
      | throwError "missing BMC normal form simp extension"
    let thms ← ext.getTheorems
    if let some result ← Lean.Meta.Simp.rewrite? e thms.post thms.erased "bmc-cache" false then
      return .done result
  let unfolded ← Veil.Simp.simp #[`nextSimp] { instances := true } e
  let hoisted ← if ← hasHOQuantification unfolded.expr then
      Veil.Simp.simp #[`existsQuantifierSimp] {} unfolded.expr
    else pure { expr := unfolded.expr }
  return .done (← unfolded.mkEqTrans hoisted)

simproc_decl bmcNormalizeClauseProc (_) := bmcNormalizeClause

elab "__veil_bmc_normalize" : tactic => do
  evalTactic (← `(tactic| __veil_bmc_hyps simp +$(mkIdent `instances)
    ($(mkIdent `failIfUnchanged):ident := $(mkIdent ``false)) only
    [↓ $(mkIdent ``bmcNormalizeClauseProc):ident]))

'''+s[i:]
s=s.replace('  let localPath ← `(tactic|','''  let normalize ← if veil.experimental.bmcCache.get (← getOptions) then
      `(tactic| __veil_bmc_normalize)
    else `(tactic|
      (__veil_bmc_hyps simp +$(mkIdent `instances) ($(mkIdent `failIfUnchanged):ident := $(mkIdent ``false)) only [$(mkIdent `nextSimp):ident]
       __veil_bmc_hyps simp +$(mkIdent `instances) ($(mkIdent `failIfUnchanged):ident := $(mkIdent ``false)) only [↓ $(mkIdent ``existsQuantifierSimpGuarded):ident]))
  let localPath ← `(tactic|''')
old='''     __veil_bmc_hyps simp +$(mkIdent `instances) ($(mkIdent `failIfUnchanged):ident := $(mkIdent ``false)) only [$(mkIdent `nextSimp):ident]
     __veil_bmc_hyps simp +$(mkIdent `instances) ($(mkIdent `failIfUnchanged):ident := $(mkIdent ``false)) only [↓ $(mkIdent ``existsQuantifierSimpGuarded):ident]'''
s=s.replace(old,'     $normalize:tactic');p.write_text(s)
