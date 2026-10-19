/- Attribution candidate: ONLY add dependency-aware output/congruence
   handling. Deliberately omit withDefault in both branches. Prepared for validation, not yet compiled or tested.
   Include after importing Veil or Smt; this does not edit the dependency. -/

open Lean Meta Simp

namespace Issue123EmbeddingCandidate

meta def withAdditionalLemmas (xs : Array Expr) (f : SimpM α) : SimpM α := do
  Simp.withFreshCache do
    let mut s ← Simp.getSimpTheorems
    let mut updated := false
    let ctx ← Simp.getContext
    for x in xs do
      if ← isProof x then
        s ← s.addTheorem (.fvar x.fvarId!) x (config := ctx.indexConfig)
        updated := true
    if updated then Simp.withSimpTheorems s f else f

meta def contextualArrow (guard : Expr → Bool) : Simproc := fun e => do
  let .forallE n p q _ := e | return .continue
  -- This algorithm simplifies an originally nondependent implication.
  -- Let Lean's ordinary simpForall handle originally dependent proof binders.
  unless e.isArrow do return .continue
  unless guard p do return .continue
  let rp ← simp p
  let r ← Meta.withLocalDeclD n rp.expr fun hp => do
    let rq ← withAdditionalLemmas #[hp] (simp q)
    match rq.proof? with
    | none => mkImpCongr e rp rq
    | some hq =>
      let hq ← mkLambdaFVars #[hp] hq
      if rq.expr.containsFVar hp.fvarId! then
        return {
          expr := ← mkForallFVars #[hp] rq.expr
          proof? := ← mkImpDepCongrCtx (← rp.getProof) hq }
      else
        return {
          expr := e.updateForallE! rp.expr rq.expr
          proof? := ← mkImpCongrCtx (← rp.getProof) hq }
  return .done r

meta def fixedAddIntGtZeroLemma : Simproc :=
  contextualArrow Smt.Preprocess.Embedding.isIntGeLitZero

end Issue123EmbeddingCandidate

attribute [-embedding] Smt.Preprocess.Embedding.add_int_gt_zero

simproc ↓ [embedding] issue123_fixed_add_int_gt_zero (_ → _) :=
  Issue123EmbeddingCandidate.fixedAddIntGtZeroLemma
