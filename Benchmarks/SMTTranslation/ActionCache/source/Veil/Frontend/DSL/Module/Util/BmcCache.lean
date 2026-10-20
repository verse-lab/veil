module

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
    let ty ← levelMVarToParam (← instantiateMVars (← mkForallFVars xs (← mkEq lhs result.expr)))
    let value ← levelMVarToParam (← instantiateMVars (← mkLambdaFVars xs (← result.getProof)))
    unless !ty.hasFVar && !ty.hasMVar && !value.hasFVar && !value.hasMVar do
      throwError "BMC normal form contains unbound parameters"
    let levels := (collectLevelParams (collectLevelParams {} ty) value).params.toList
    let fullName := (← getCurrNamespace) ++ name
    addDecl (.thmDecl (mkTheoremValEx fullName levels ty value []))
    enableRealizationsForConst fullName
    Term.applyAttributes fullName #[{ name := `bmcNormalize }]

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
    let th := mkIdent (← mkFreshUserName `_bmc_th)
    let pre := mkIdent (← mkFreshUserName `_bmc_pre)
    let post := mkIdent (← mkFreshUserName `_bmc_post)
    let base := (← collectModuleBinders mod).map (·.1)
    let states := #[← `(bracketedBinder| ($th : $theoryT)),
                    ← `(bracketedBinder| ($pre $post : $stateT))]
    saveBmcNormalForm `__bmc_init_eq (base ++ #[states[0]!, ← `(bracketedBinder| ($post : $stateT))])
      (← `(term| ($rts).$(mkIdent `init) $th $post))
    for act in mod.actions do
      let (_, params) ← mod.declarationAllParams act.name act.declarationKind
      let (args, bindings) ← mkParamBinders params (← mkFreshUserName `_bmc_args).toString
      let label := mkIdent (labelTypeName ++ act.name)
      let expr ← `(term| ($rts).$(mkIdent `tr) $th $pre ($label $args*) $post)
      saveBmcNormalForm (`__bmc_action ++ act.name ++ `eq)
        (base ++ states ++ bindings.map (·.1)) expr
    if mod.actions.size > 1 then
      let tag := mkIdent (← mkFreshUserName `_bmc_tag)
      let (body, args) ← mkAnyActionDisjunction mod rts th pre post tag 0
        (prefix_ := some (← mkFreshUserName `_bmc_any_args).toString)
      let tags := (← mkActionTagBinders).map (·.1)
      saveBmcNormalForm `__bmc_any_eq
        (base ++ tags ++ #[← `(bracketedBinder| ($tag : $actionTagType))] ++ states ++ args.map (·.1)) body

end Veil
