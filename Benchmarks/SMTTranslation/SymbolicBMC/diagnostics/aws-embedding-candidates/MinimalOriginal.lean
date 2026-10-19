import Veil
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/- Candidate minimal shape; not claimed to reproduce until actually run.
   The opaque predicate keeps the Fin constructor/bound proof in the matrix.
   Only simplification and its equality proof are checked; no solver is used.
   This headerless body can be appended after imports and an optional fix. -/

namespace Issue123EmbeddingRegression

opaque finPredicate : Fin 10 → Prop

open Lean Elab Command Meta in
elab "#check_fin_embedding_shape " label:str proposition:term : command => do
  liftTermElabM do
    let e ← Term.elabTermAndSynthesize proposition (some (mkSort .zero))
    let some thmsExt ← Meta.getSimpExtension? `embedding
      | throwError "missing embedding theorem extension"
    let some procsExt ← Meta.Simp.getSimprocExtension? `embedding
      | throwError "missing embedding simproc extension"
    let ctx ← Meta.Simp.mkContext { zeta := false, singlePass := true }
      #[← thmsExt.getTheorems] (← Meta.getSimpCongrTheorems)
    let (result, _) ← Meta.simp e ctx (simprocs := #[← procsExt.getSimprocs])
    let proof ← result.getProof
    Meta.check result.expr
    Meta.check proof
    unless ← isDefEq (← inferType proof) (← mkEq e result.expr) do
      throwError "simplifier returned a proof of the wrong equality"
    if result.expr.hasFVar || proof.hasFVar then
      throwError "a free variable escaped from the closed simplification input"
    logInfo m!"{label.getString}: expression and equality proof type-check"

-- Nondependent result: the fresh nonnegativity proof is needed only to prove
-- the rewrite; it does not occur in the resulting proposition.
#check_fin_embedding_shape "scalar control"
  (∀ z : Int, z ≥ 0 → ((z.toNat : Int) = z))

-- Candidate trigger: simplifying the bound changes the type of the inner
-- proof binder; rebuilding the Fin value can use the outer nonnegativity
-- proof inside a transport. No hypothesis is introduced in the outer context.
#check_fin_embedding_shape "Fin bound proof"
  (∀ z : Int, z ≥ 0 → ∀ h : z.toNat < 10, finPredicate ⟨z.toNat, h⟩)

-- Closer to AWS: retain an extra scalar fact before the proof-valued bound.
#check_fin_embedding_shape "Fin bound proof with antecedent"
  (∀ z : Int, z ≥ 0 → z.toNat < 10 →
    ∀ h : z.toNat < 10, finPredicate ⟨z.toNat, h⟩)

end Issue123EmbeddingRegression
