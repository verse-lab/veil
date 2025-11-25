import Veil.Core.Tools.Checker.Concrete.State
import Veil.Core.Tools.Checker.Concrete.DataStructure
import Veil.Core.Tools.Checker.Concrete.Util
import Veil.Core.Tools.Checker.Concrete.Concretize
import Veil.Core.Tools.Checker.Concrete.Runlib



def reprFiniteFunc {α β} [FinEnum α] [Repr α] [Repr β] (f : α → β) : String :=
  (FinEnum.toList α).map (fun a => s!"{reprStr a}{reprStr (f a)}")
  |> String.intercalate ""

instance (priority := high) finFunctionReprCurry (α₁ : Type u) (α₂ : Type v) (β : Type w)
  [Repr α₁] [FinEnum α₁] [Repr α₂] [FinEnum α₂] [Repr β] [inst : Repr (α₁ × α₂ → β)] :
  Repr (α₁ → α₂ → β) where
  reprPrec := fun f n => inst.reprPrec (fun (x, y) => f x y) n

open Lean in
instance (priority := low) finFunctionRepr (α : Type u) (β : Type v) [Repr α] [FinEnum α] [Repr β] :
  Repr (α → β) where
  reprPrec := fun f n =>
    let l := FinEnum.toList α
    let args := l.map (reprPrec · n)
    let res := l.map ((fun x => reprPrec x n) ∘ f)
    args.zip res |>.foldl
      (fun acc (a, b) => acc.append (a ++ " => " ++ b ++ Format.line))
      ("finite_fun : ".toFormat)

instance (priority := high) essentiallyFinSetRepr (α : Type u) [Repr α] [FinEnum α] : Repr (α → Bool) where
  reprPrec := fun f => List.repr (FinEnum.toList α |>.filter f)

open Lean Meta Elab Term Command in
/-- Attempt to derive a `Repr` instance for a `structure` by assuming all
    its parameters are `Repr`s. This can be useful when the structure
    includes functions, which are finite when the type parameters are finite
    but by default Lean cannot derive `Repr` for them.
    Note that this command does not check if any parameter is not a `Type`. -/
elab "simple_deriving_repr_for " t:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  let ConstantInfo.inductInfo info1 ← getConstInfo name | throwError "no such structure {name}"
  let .some info2 := getStructureInfo? (← getEnv) name | throwError "no such structure {name}"
  -- get the names of the parameters from the type
  let numParams := info1.numParams
  let .some (paramNames, _) := Nat.foldM (m := Option) numParams (fun _ _ (res, ty) => do
    let Expr.forallE na _ body _ := ty | failure
    pure (na :: res, body)) ([], info1.type) | throwError "unknown error"
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
  -- for all parameters, assume they are `FinEnum`
  -- NOTE: this might be relaxed later
  let paramInsts : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) ←
    paramIdents.mapM (fun pn => `(bracketedBinder| [$(mkIdent ``Repr) $pn] ))
  let target := Syntax.mkApp (mkIdent name) paramIdents
  -- assemble everything
  let cmd ← `(command|
    instance $[$paramInsts]* : $(mkIdent ``Repr) $target where
      reprPrec $t:ident $n:ident := $(mkIdent ``Std.Format.bracket) "{ "
        ($(mkIdent ``Std.Format.joinSep) [$fieldReprs,*] ", ") " }")
  trace[veil.debug] s!"Generated instance command: {cmd}"
  elabCommand cmd
