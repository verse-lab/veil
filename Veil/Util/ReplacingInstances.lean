module

public meta import Lean

public meta section

namespace Veil.Util

section replacement

open Lean Meta Elab Term

private def getLambdaBody : Expr → Expr
  | .lam _ _ b ..   => getLambdaBody b
  | e               => e

/-- If `ty` (the type of `arg`, or the binder type it is passed to) is
`∀ xs, Decidable (p xs)`, replace `arg` by `fun xs => Classical.propDecidable (p xs)`.
This covers both fully applied instances (`xs` empty) and instances passed
unapplied. `forallTelescope` does not unfold `DecidableEq α`, `DecidablePred p`,
etc., so unapplied instances of these types (such as module parameters) are
left alone. -/
private def neutralizeDecidableInstStep (arg : Expr) (expectedType? : Option Expr) : MetaM (Option Simp.Result) := do
  if (getLambdaBody arg).getAppFn'.isConstOf ``Classical.propDecidable then
    return none
  let ty ← match expectedType? with
    | some expectedType => pure expectedType
    | none => inferType arg
  forallTelescope ty fun xs body =>
    body.withApp fun fn args => do
      unless fn.isConstOf ``Decidable do
        return none
      let p := args[0]!
      let q ← mkAppM ``Classical.propDecidable #[p]
      let rhs ← mkLambdaFVars xs q
      -- Decidable and dependent functions into it are subsingletons.
      -- Apply the endpoints directly to avoid unfolding ghosts during unification.
      let elim ← mkAppOptM ``Subsingleton.elim #[some ty, none]
      return some { expr := rhs, proof? := mkApp2 elim arg rhs }

private def neutralizeDecidableInstCore (useExpectedType : Bool) : Expr → SimpM Simp.Step := fun e => do
  -- idea: if any of the arguments is a potential target, replace it
  -- and `visit` again; otherwise, `continue`
  -- NOTE: it seems that `simp` will skip instance arguments in the recursion,
  -- so we need to visit all arguments and implement this manually
  let args := e.getAppArgs
  let f := e.getAppFn'
  let target? ← do
    if useExpectedType then
      let (paramInfos, _) ← try
          instantiateForallWithParamInfos (← inferType f) args
        catch _ =>
          return .continue
      (args.zip paramInfos).zipIdx.findSomeM? fun ((arg, paramInfo), idx) => do
        return (← neutralizeDecidableInstStep arg (some paramInfo.type)).map (·, idx)
    else
      args.zipIdx.findSomeM? fun (arg, idx) => do
        return (← neutralizeDecidableInstStep arg none).map (·, idx)
  let some (res, idx) := target?
    | return .continue
  -- use congruence here
  let fpre := mkAppN f <| args.take idx
  -- Keep the endpoints of the equality. Re-inferring them through `mkAppM`
  -- may unfold a ghost in the instance's type to assign endpoint metavariables.
  let proof2 ← mkCongrArg fpre (← res.getProof)
  let proof3 ← Array.foldlM (fun subproof sufarg => mkCongrFun subproof sufarg)
    proof2 (args.drop (idx + 1))
  return .visit { expr := mkAppN f (args.set! idx res.expr), proof? := .some proof3 }

/-- Replace every `Decidable` instance argument by `Classical.propDecidable`
(by `fun xs => Classical.propDecidable (p xs)` if it is passed unapplied). The
proposition is read off the type of the argument. This is the variant *tactics*
should use. -/
simproc_decl neutralizeDecidableInst (_) := neutralizeDecidableInstCore (useExpectedType := false)

/-- Like `neutralizeDecidableInst`, but reads the proposition off the binder
type of the surrounding application instead of the type of the argument.

The two differ only when these types are definitionally but not syntactically
equal. The result here is then well-typed without unfolding anything; unfolding
is only needed to check the proof (`Subsingleton.elim`). Use this in
*generated proof artifacts* whose result is abstracted again, saved, or compared
while some definitions must stay folded:
* In field-representation mode, the type of an elaborated instance may mention
  concrete field variables such as `r_conc`, while the application has already
  exposed the canonical field `r`. Reading the binder type keeps the
  proposition in terms of `r`, so a later abstraction over `r` (e.g. by
  `mkLambdaFVars`) does not leave `r_conc` behind.
* An instance synthesized through the body of a definition, e.g.
  `Nat.decLt (readCount n) (bound n)` for `if enabled n then …` with a ghost
  relation `enabled`, is replaced by `Classical.propDecidable (enabled n)`
  rather than `Classical.propDecidable (readCount n < bound n)`. -/
simproc_decl neutralizeDecidableInstWithExpectedType (_) :=
  neutralizeDecidableInstCore (useExpectedType := true)

end replacement

end Veil.Util
