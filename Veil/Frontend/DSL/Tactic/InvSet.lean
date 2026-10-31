module

public meta import Veil.Frontend.DSL.Tactic.Core
public meta import Veil.Frontend.DSL.Module.Util.InvSet

public meta section

open Lean Meta Elab Tactic

namespace Veil

syntax (name := enforceInvSetSupport) "veil_enforce_invset_support" "[" ident,* "]" : tactic
syntax (name := restrictInvSetPre) "veil_restrict_invset_pre" "[" ident,* "]" : tactic

private def andChain (props : Array Expr) : Expr :=
  if props.isEmpty then mkConst ``True
  else props.pop.foldr (fun p rest => mkApp2 (mkConst ``And) p rest) props.back!

/-- Prove an obligation with a weaker precondition containing only selected
invariants. The original concrete VC is recovered by conjunction projections;
the new solver goal has no hypothesis containing the full precondition. -/
@[tactic restrictInvSetPre]
def elabRestrictInvSetPre : Tactic := fun stx => withMainContext do
  let `(tactic| veil_restrict_invset_pre [$ids:ident,*]) := stx
    | throwUnsupportedSyntax
  evalTactic (← `(tactic| unhygienic intros))
  withMainContext do
    let mod ← getCurrentModule
    let original ← getMainGoal
    let target ← instantiateMVars (← original.getType)
    let target := target.consumeMData
    let args := target.getAppArgs
    let head := target.getAppFn
    let isTransition := head.isConstOf ``Transition.meetsSpecificationIfSuccessfulAssuming
    let preIndex ←
      if head.isConstOf ``VeilM.meetsSpecificationIfSuccessfulAssuming ||
          head.isConstOf ``VeilM.doesNotThrowAssuming_ex then pure 6
      else if head.isConstOf ``Transition.meetsSpecificationIfSuccessfulAssuming then pure 4
      else throwError "invset restriction expected a concrete Veil verification condition"
    let pre := args[preIndex]!
    let invariantsName ← resolveGlobalConstNoOverloadCore assembledInvariantsName
    unless pre.getAppFn'.isConstOf invariantsName do
      throwError "invset restriction expected the original invariant conjunction"
    -- The asynchronous discharger's module snapshot can predate registration
    -- of assembled definitions. Reconstruct the same parameter union used by
    -- assembleInvariants from the already registered source assertions.
    let dependencies := Std.HashSet.ofArray (mod.invariants.map (·.name))
    let (baseParams, extraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·)
      (.derivedDefinition .invariantLike dependencies)
    let allParams := baseParams ++ extraParams
    let actualArgs := pre.getAppArgs'
    unless allParams.size == actualArgs.size do
      throwError "invset restriction found an unexpected invariant parameter layout"
    let selectedNames ← ids.getElems.mapM (fun id => resolveGlobalConstNoOverloadCore id.getId)
    let mut predicates := #[]
    let mut indices := #[]
    for h : i in [:mod.invariants.size] do
      let inv := mod.invariants[i]
      let name ← resolveGlobalConstNoOverloadCore inv.name
      if selectedNames.contains name then
        let (params, _) ← mod.declarationAllParams inv.name inv.declarationKind
        let invArgs ← params.mapM fun p => do
          let some index := allParams.findIdx? (·.name == p.name)
            | throwError "invset restriction cannot find predicate parameter {p.name}"
          return actualArgs[index]!
        predicates := predicates.push (mkAppN (← mkConstWithFreshMVarLevels name) invArgs)
        indices := indices.push i
    unless predicates.size == selectedNames.size do
      throwError "invset support contains a declaration that is not an invariant"
    let preType ← inferType pre
    let restrictedPre ← forallBoundedTelescope preType (some 2) fun states _ => do
      unless states.size == 2 do throwError "invalid invariant predicate type"
      mkLambdaFVars states (andChain (predicates.map (mkAppN · states)))
    let restrictedType := mkAppN head (args.set! preIndex restrictedPre)
    let restricted ← mkFreshExprMVar (some restrictedType) .syntheticOpaque
    let binderCount := if isTransition then 5 else 3
    let proof ← forallBoundedTelescope target (some binderCount) fun inputs _ => do
      unless inputs.size == binderCount do throwError "invalid verification precondition shape"
      let preInput := inputs[if isTransition then 3 else 2]!
      let assumptions ← mkAppM ``And.left #[preInput]
      let fullInv ← mkAppM ``And.right #[preInput]
      let facts ← indices.mapM fun index => do
        let mut fact := fullInv
        for _ in [:index] do fact ← mkAppM ``And.right #[fact]
        if index + 1 < mod.invariants.size then
          fact ← mkAppM ``And.left #[fact]
        return fact
      let selected ← if facts.isEmpty then pure (mkConst ``True.intro)
        else facts.pop.foldrM (fun fact rest => mkAppM ``And.intro #[fact, rest]) facts.back!
      let restrictedInput ← mkAppM ``And.intro #[assumptions, selected]
      let restrictedArgs := if isTransition then
          #[inputs[0]!, inputs[1]!, inputs[2]!, restrictedInput, inputs[4]!]
        else #[inputs[0]!, inputs[1]!, restrictedInput]
      mkLambdaFVars inputs (mkAppN restricted restrictedArgs)
    original.assign proof
    replaceMainGoal [restricted.mvarId!]

/-- Split only syntactic conjunctions. Reducing a named invariant before its
support decision would lose the provenance of an excluded fact. -/
private partial def splitInvariantConjunctions : TacticM Unit := withMainContext do
  let some decl := (← getLCtx).findDecl? fun decl =>
      if decl.type.getAppFn'.isConstOf ``And then some decl else none
    | return
  let left ← mkFreshUserName `__veil_invset_left
  let right ← mkFreshUserName `__veil_invset_right
  evalTactic (← `(tactic| rcases $(mkIdent decl.userName):ident with
    ⟨$(mkIdent left):ident, $(mkIdent right):ident⟩))
  splitInvariantConjunctions

@[tactic enforceInvSetSupport]
def elabEnforceInvSetSupport : Tactic := fun stx => withMainContext do
  let `(tactic| veil_enforce_invset_support [$ids:ident,*]) := stx
    | throwUnsupportedSyntax
  let mod ← getCurrentModule
  let support ← ids.getElems.mapM (fun id => resolveGlobalConstNoOverloadCore id.getId)
  let invariantNames ← mod.invariants.mapM (fun inv =>
    resolveGlobalConstNoOverloadCore inv.name)
  let excluded := invariantNames.filter (!support.contains ·)
  evalTactic (← `(tactic| unfold $(mkIdent assembledInvariantsName):ident at $(mkIdent `hinv):ident))
  splitInvariantConjunctions
  let toClear ← withMainContext do
    return (← getLCtx).foldl (init := (#[] : Array FVarId)) fun acc decl =>
      if excluded.contains (decl.type.getAppFn'.constName?.getD .anonymous) then
        acc.push decl.fvarId
      else acc
  let mut goal ← getMainGoal
  -- A failure to clear is a restriction failure, never a full-context retry.
  for id in toClear.reverse do
    goal ← goal.clear id
  replaceMainGoal [goal]
  withMainContext do
    for decl in ← getLCtx do
      let used := decl.type.getUsedConstants ++
        (decl.value?.map (·.getUsedConstants) |>.getD #[])
      if used.any excluded.contains then
        throwError "invset support restriction left an excluded invariant in hypothesis {decl.userName}"

end Veil
