import Veil.Core.Tools.Checker.Concrete.State
import Veil.Core.Tools.Checker.Concrete.DataStructure
import Veil.Core.Tools.Checker.Concrete.Util
import Veil.Core.Tools.Checker.Concrete.ConcretizeType

open Lean Meta Elab Command in
/-- Given the name of an `enum` type defined in a `veil module`, generates
    the corresponding inductive type and proves that this inductive type
    is an instance of the underlying typeclass of that `enum` type. -/
def deriveEnumInstance (name : Name) : CommandElabM Unit := do
  let clsName ← resolveGlobalConstNoOverloadCore (name.appendAfter "_Enum")
  let .some info := getStructureInfo? (← getEnv) clsName | throwError "no such structure {clsName}"
  -- NOTE: assume the last two are the propositions to satisfy
  let fields := info.fieldNames.pop.pop
  let ctors : Array (TSyntax ``Lean.Parser.Command.ctor) ←
    fields.mapM fun fn => `(Lean.Parser.Command.ctor| | $(mkIdent fn):ident )
  trace[veil.debug] "fields: {fields}"
  let defineIndTypeCmd ← do
    if ctors.size > 0 then
      `(inductive $(mkIdent name) where $[$ctors]* deriving $(mkIdent ``DecidableEq), $(mkIdent ``Repr), $(mkIdent ``Inhabited), $(mkIdent ``Nonempty))
    else
      `(inductive $(mkIdent name) where deriving $(mkIdent ``DecidableEq), $(mkIdent ``Repr))
  let instClauses ←
    fields.mapM fun fn => `(Lean.Parser.Term.structInstField| $(mkIdent fn):ident := $(mkIdent <| name ++ fn):ident )
  let completeRequirement := info.fieldNames.back!
  let distinctRequirement := info.fieldNames.pop.back!
  let proof1 ← `(Lean.Parser.Term.structInstField| $(mkIdent distinctRequirement):ident := (by decide) )
  let proof2 ← do
    let x := mkIdent `x
    `(Lean.Parser.Term.structInstField| $(mkIdent completeRequirement):ident := (by intro $x:ident ; cases $x:ident <;> decide) )
  let instClauses := instClauses.push proof1 |>.push proof2
  let instantiateCmd ←
    `(instance : $(mkIdent clsName) $(mkIdent name) where $[$instClauses]*)
  let allConstructors ← do
    let arr := fields.map fun fn => (mkIdent <| name ++ fn)
    `(term| [ $arr,* ] )
  let instantiateFinEnumCmd ←
    `(instance : $(mkIdent ``FinEnum) $(mkIdent name) :=
      $(mkIdent ``FinEnum.ofList) $allConstructors (by simp ; exact $(mkIdent <| clsName ++ completeRequirement)))
  elabCommand defineIndTypeCmd
  trace[veil.debug] "defineIndTypeCmd: {defineIndTypeCmd}"
  elabCommand instantiateCmd
  trace[veil.debug] "instantiateCmd: {instantiateCmd}"
  elabCommand instantiateFinEnumCmd
  trace[veil.debug] "instantiateFinEnumCmd: {instantiateFinEnumCmd}"

elab "deriving_enum_instance_for " name:ident : command => do
  let name := name.getId
  deriveEnumInstance name



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
