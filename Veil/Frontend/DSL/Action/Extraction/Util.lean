import Veil.Frontend.DSL.Action.Extraction.Basic
import Veil.Util.Meta

/-! # Utilities for Displaying -/

namespace Veil

deriving instance Repr for DivM

instance [Repr κ] [Repr α] : Repr (PeDivM κ α) :=
  inferInstanceAs (Repr (_ × _))

instance : Repr Std.Format where
  reprPrec x _ := x

-- NOTE: Not sure why resolution does not work without this
instance [inst : Repr (m (Except ε α))] : Repr (ExceptT ε m α) := inst

instance (priority := high) finFunctionReprCurry (α₁ : Type u) (α₂ : Type v) (β : Type w)
  [Repr α₁] [FinEnum α₁] [Repr α₂] [FinEnum α₂] [Repr β] [inst : Repr (α₁ × α₂ → β)] :
  Repr (α₁ → α₂ → β) where
  reprPrec := fun f n => inst.reprPrec (fun (x, y) => f x y) n

instance (priority := low) finFunctionRepr (α : Type u) (β : Type v) [Repr α] [FinEnum α] [Repr β] :
  Repr (α → β) where
  reprPrec := fun f n =>
    let l := FinEnum.toList α
    let args := l.map (reprPrec · n)
    let res := l.map ((fun x => reprPrec x n) ∘ f)
    args.zip res |>.foldl
      (fun acc (a, b) => acc.append (a ++ " => " ++ b ++ Std.Format.line))
      ("finite_fun : ".toFormat)

instance (priority := high) essentiallyFinSetRepr (α : Type u) [Repr α] [FinEnum α] : Repr (α → Bool) where
  reprPrec := fun f => List.repr (FinEnum.toList α |>.filter f)

open Lean Meta Elab Term Command

private inductive SimpleDerivingReprForCase where
  | fromParams | fromFields

private def simpleDerivingReprForCore (t : Ident) (case : SimpleDerivingReprForCase) : MetaM (TSyntax `command) := do
  let name ← realizeGlobalConstNoOverloadWithInfo t
  let ConstantInfo.inductInfo info1 ← getConstInfo name | throwError "no such structure {t}"
  let .some info2 := getStructureInfo? (← getEnv) name | throwError "no such structure {t}"
  -- get the names of the parameters from the type
  let paramNames := info1.type.getForallBinderNames
  let paramIdents := paramNames.toArray |>.map mkIdent
  let fields := info2.fieldNames
  let t ← mkIdent <$> mkFreshBinderName
  let n ← mkIdent <$> mkFreshBinderName
  -- create the `instance` definition syntax; for fields, need some tricks?
  let embeddedStringStx x : TSyntax `str :=
    { raw := Lean.Syntax.node Lean.SourceInfo.none `str #[Lean.Syntax.atom Lean.SourceInfo.none ("\"" ++ x ++ " := \"")] }
  let fieldReprs ← fields.mapM (fun fn => do
    -- `State.field t`
    let fieldAccess ← `(term| ($(mkIdent <| name ++ fn) $t))
    `(term| $(mkIdent ``Std.Format.append) $(embeddedStringStx <| toString fn)
      ($(mkIdent ``Repr.reprPrec) $fieldAccess $n)))
  let instArgs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) ←
    match case with
    | .fromParams =>
      paramIdents.mapM (fun pn => `(bracketedBinder| [$(mkIdent ``Repr) $pn] ))
    | .fromFields =>
      let ctorTypes ← fields.mapM fun fn => do
        let fnName ← realizeGlobalConstNoOverloadCore (name ++ fn)
        let fnInfo ← getConstInfo fnName
        -- have to resort to delaboration here ... not sure how to do with `Expr`
        let ty ← delabVeilExpr fnInfo.type
        let (res, base) ← splitForallArgsCodomain ty
        let res' := res.drop (1 + paramIdents.size) -- drop the `self` argument and parameters
        mkArrowStx res'.toList base
      ctorTypes.mapM (fun ctorTy => `(bracketedBinder| [$(mkIdent ``Repr) ($ctorTy)] ))
  let target := Syntax.mkApp (mkIdent name) paramIdents
  -- assemble everything
  `(command|
    instance $[$instArgs]* : $(mkIdent ``Repr) $target where
      reprPrec $t:ident $n:ident := $(mkIdent ``Std.Format.bracket) "{ "
        ($(mkIdent ``Std.Format.joinSep) [$fieldReprs,*] ", ") " }")

/-- Attempt to derive a `Repr` instance for a `structure` by assuming all
    its parameters are `Repr`s. This can be useful when the structure
    includes functions, which are finite when the type parameters are finite
    but by default Lean cannot derive `Repr` for them.
    Note that this command does not check if any parameter is not a `Type`. -/
elab "simple_deriving_repr_for " t:ident : command => do
  let cmd ← liftTermElabM <| simpleDerivingReprForCore t .fromParams
  elabVeilCommand cmd

/-- Similar to `simple_deriving_repr_for` but assumes all field types are `Repr`. -/
elab "simple_deriving_repr_for' " t:ident : command => do
  let cmd ← liftTermElabM <| simpleDerivingReprForCore t .fromFields
  elabVeilCommand cmd

end Veil
