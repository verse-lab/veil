import Lean
import Mathlib.Lean.Expr.Basic

namespace Veil.Util

theorem neutralize_Decidable (p : Prop) [inst : Decidable p] :
  inst = Classical.propDecidable p := by grind

section replacement

open Lean Meta Elab Term

simproc_decl neutralizeDecidableInst (_) := fun e => do
  -- idea: if any of the arguments is a potential target, replace it
  -- and `visit` again; otherwise, `continue`
  -- NOTE: it seems that `simp` will skip instance arguments in the recursion,
  -- so we need to visit all arguments and implement this manually
  let args := e.getAppArgs
  let args' := args.zipIdx
  let some (p, idx) ← args'.findSomeM? (fun (arg, idx) => do
    if arg.getAppFn'.isConstOf ``Classical.propDecidable then
      return none
    let ty ← inferType arg
    ty.withApp fun fn args =>
      if fn.isConstOf ``Decidable then
        return some (args[0]!, idx)
      else
        return none) | return .continue
  let arg := args[idx]! --|>.consumeMData
  let q ← mkAppM ``Classical.propDecidable #[p]
  let proof := mkAppN (mkConst ``neutralize_Decidable) #[p, arg]
  -- use congruence here
  let f := e.getAppFn'
  let fpre := mkAppN f <| args.take idx
  let proof2 ← mkAppM ``congrArg #[fpre, proof]
  let proof3 ← Array.foldlM (fun subproof sufarg => mkAppM ``congrFun #[subproof, sufarg])
    proof2 (args.drop (idx + 1))
  return .visit { expr := mkAppN f (args.set! idx q), proof? := .some proof3 }

end replacement

end Veil.Util
