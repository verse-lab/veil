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
private def neutralizeDecidableInstDepth0Step (arg : Expr) (expectedType? : Option Expr) (idx : Nat) : SimpM (Option (Simp.Result × Nat)) := do
  if arg.getAppFn'.isConstOf ``Classical.propDecidable then
    return none
  let ty ← match expectedType? with
    | some expectedType => whnf expectedType
    | none => inferType arg
  ty.withApp fun fn args => do
    if fn.isConstOf ``Decidable then
      let p := args[0]!
      let q ← mkAppM ``Classical.propDecidable #[p]
      let proof := mkAppN (mkConst ``neutralize_Decidable) #[p, arg]
      return some ({ expr := q, proof? := .some proof }, idx)
    else
      return none

private def neutralizeDecidableInstGeneralStep (arg : Expr) (expectedType? : Option Expr) (idx : Nat) : SimpM (Option (Simp.Result × Nat)) := do
  if (getLambdaBody arg).getAppFn'.isConstOf ``Classical.propDecidable then
    return none
  let ty ← match expectedType? with
    | some expectedType => pure expectedType
    | none => inferType arg
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

private def neutralizeDecidableInstCore
    (step : Expr → Option Expr → Nat → SimpM (Option (Simp.Result × Nat)))
    (useExpectedType : Bool := false) : Expr → SimpM Simp.Step := fun e => do
  -- idea: if any of the arguments is a potential target, replace it
  -- and `visit` again; otherwise, `continue`
  -- NOTE: it seems that `simp` will skip instance arguments in the recursion,
  -- so we need to visit all arguments and implement this manually
  let args := e.getAppArgs
  let f := e.getAppFn'
  let target? ←
    if useExpectedType then
      let (paramInfos, _) ← try
          instantiateForallWithParamInfos (← inferType f) args
        catch _ =>
          return .continue
      (args.zip paramInfos).zipIdx.findSomeM? fun ((arg, paramInfo), idx) =>
        step arg (some paramInfo.type) idx
    else
      args.zipIdx.findSomeM? fun (arg, idx) =>
        step arg none idx
  let some (res, idx) := target?
    | return .continue
  -- use congruence here
  let fpre := mkAppN f <| args.take idx
  let proof2 ← mkAppM ``congrArg #[fpre, (← res.getProof)]
  let proof3 ← Array.foldlM (fun subproof sufarg => mkAppM ``congrFun #[subproof, sufarg])
    proof2 (args.drop (idx + 1))
  return .visit { expr := mkAppN f (args.set! idx res.expr), proof? := .some proof3 }

simproc_decl neutralizeDecidableInstDepth0 (_) := neutralizeDecidableInstCore neutralizeDecidableInstDepth0Step
simproc_decl neutralizeDecidableInstGeneral (_) := neutralizeDecidableInstCore neutralizeDecidableInstGeneralStep

/-
The default simprocs above inspect the actual type of each argument.  That is
usually the least surprising behavior, and it is what tactics exposed to users
should keep using.

The variants below inspect the _expected_ binder type at the surrounding
application instead.  This is useful only in generated proof artifacts where the
rewritten expression is immediately abstracted again with `mkLambdaFVars`.  In
field-representation mode, an elaborated `Decidable` argument may have a type
whose proposition mentions concrete field variables such as `r_conc`, while the
surrounding application has already exposed the canonical fields `r`.  Replacing
with `Classical.propDecidable` at the expected type keeps the proposition in
that canonical form, so the later abstraction step does not capture the wrong
field variables.
-/
simproc_decl neutralizeDecidableInstDepth0WithExpectedType (_) :=
  neutralizeDecidableInstCore neutralizeDecidableInstDepth0Step (useExpectedType := true)

simproc_decl neutralizeDecidableInstGeneralWithExpectedType (_) :=
  neutralizeDecidableInstCore neutralizeDecidableInstGeneralStep (useExpectedType := true)

end replacement

end Veil.Util
