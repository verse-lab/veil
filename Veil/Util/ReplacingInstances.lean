import Lean

namespace Veil.Util

theorem neutralize_Decidable (p : Prop) [inst : Decidable p] :
  inst = Classical.propDecidable p := by grind

section replacement

open Lean Meta Elab Term

private def getLambdaBody : Expr → Expr
  | .lam _ _ b ..   => getLambdaBody b
  | e               => e

/-- Essentially a special case of `neutralizeDecidableInstGeneralStep`, but should be more efficient? -/
private def neutralizeDecidableInstDepth0Step (arg : Expr) (idx : Nat) : SimpM (Option (Simp.Result × Nat)) := do
  if arg.getAppFn'.isConstOf ``Classical.propDecidable then
    return none
  let ty ← inferType arg
  ty.withApp fun fn args => do
    if fn.isConstOf ``Decidable then
      let p := args[0]!
      let q ← mkAppM ``Classical.propDecidable #[p]
      let proof := mkAppN (mkConst ``neutralize_Decidable) #[p, arg]
      return some ({ expr := q, proof? := .some proof }, idx)
    else
      return none

private def neutralizeDecidableInstGeneralStep (arg : Expr) (idx : Nat) : SimpM (Option (Simp.Result × Nat)) := do
  if (getLambdaBody arg).getAppFn'.isConstOf ``Classical.propDecidable then
    return none
  let ty ← inferType arg
  forallTelescope ty fun xs body =>
    body.withApp fun fn args => do
      if fn.isConstOf ``Decidable then
        let p := args[0]!
        let q ← mkAppM ``Classical.propDecidable #[p]
        let proof := mkAppN (mkConst ``neutralize_Decidable) #[p, mkAppN arg xs]
        let res ← Simp.Result.addLambdas { expr := q, proof? := .some proof } xs
        return some (res, idx)
      else
        return none

private def neutralizeDecidableInstCore (step : Expr → Nat → SimpM (Option (Simp.Result × Nat))) : Expr → SimpM Simp.Step := fun e => do
  -- idea: if any of the arguments is a potential target, replace it
  -- and `visit` again; otherwise, `continue`
  -- NOTE: it seems that `simp` will skip instance arguments in the recursion,
  -- so we need to visit all arguments and implement this manually
  let args := e.getAppArgs
  let args' := args.zipIdx
  let some (res, idx) ← args'.findSomeM? (fun (arg, idx) => step arg idx) | return .continue
  -- use congruence here
  let f := e.getAppFn'
  let fpre := mkAppN f <| args.take idx
  let proof2 ← mkAppM ``congrArg #[fpre, (← res.getProof)]
  let proof3 ← Array.foldlM (fun subproof sufarg => mkAppM ``congrFun #[subproof, sufarg])
    proof2 (args.drop (idx + 1))
  return .visit { expr := mkAppN f (args.set! idx res.expr), proof? := .some proof3 }

simproc_decl neutralizeDecidableInstDepth0 (_) := neutralizeDecidableInstCore neutralizeDecidableInstDepth0Step
simproc_decl neutralizeDecidableInstGeneral (_) := neutralizeDecidableInstCore neutralizeDecidableInstGeneralStep

end replacement

end Veil.Util
