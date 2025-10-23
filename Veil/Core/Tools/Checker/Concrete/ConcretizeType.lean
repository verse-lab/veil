import Lean
import Veil.Core.Tools.Checker.Concrete.State
import Mathlib.Data.FinEnum
import Mathlib.Tactic.ProxyType
import Veil.Util.Meta
open Lean Elab Command Tactic Meta Term Veil

-- #ConcretizeType command implementation
syntax (name := concretizeTypeCmd) "#Concretize" term,* : command

/-- Generate label list (labelList) definition -/
def getLabelList : CommandElabM Unit := do
  trace[veil.info] "[getLabelList] Starting label list generation"
  -- Check if labelList already exists
  let labelListDefName := (← getCurrNamespace) ++ `labelList
  if (← getEnv).contains labelListDefName then
    trace[veil.info] "[getLabelList] labelList already exists, skipping"
    return

  let labelConcreteName ← resolveGlobalConstNoOverloadCore `LabelConcrete
  -- Generate labelList definition using the pattern from BakeryMC.lean
  let labelListCmd ← liftTermElabM do
    let labelListIdent := mkIdent `labelList
    let labelConcreteIdent := mkIdent labelConcreteName
    `(command|
      def $labelListIdent := (FinEnum.ofEquiv _ (Equiv.symm (proxy_equiv%($labelConcreteIdent)))).toList)
  trace[veil.debug] "[getLabelList] {labelListCmd}"
  elabVeilCommand labelListCmd


elab "#Concretize" args:term,* : command => do
    let env ← getEnv
    let termArray := args.getElems
    -- 1) Find State structure
    let stateName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo (mkIdent `State)
    let ConstantInfo.inductInfo _ ← getConstInfo stateName
      | throwError "no such structure {stateName}"

    let theoryName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo (mkIdent `Theory)
    let .some _ := getStructureInfo? env theoryName
      | throwError "no such structure {theoryName}"
    let ConstantInfo.inductInfo _ ← getConstInfo theoryName | throwError "no such structure {theoryName}"

    let labelName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo (mkIdent `Label)
    -- Label is an indutive type, not a structure
    let ConstantInfo.inductInfo _ ← getConstInfo labelName
      | throwError "no such structure {labelName}"

    let FieldConcreteTypeName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo (mkIdent `FieldConcreteType)

    let theoryConcreteName := `TheoryConcrete
    let stateConcreteName := `StateConcrete
    let labelConcreteName := `LabelConcrete

    -- build `TheoryConcrete`
    let theoryCmd ← do
      let assembledTheory ←`(term| $(mkIdent theoryName) $termArray*)
      `(command| @[reducible] def $(mkIdent theoryConcreteName) := $assembledTheory)

    -- build `LabelConcrete`
    let labelCmd ← do
      let assembledLabel ←`(term| $(mkIdent labelName) $termArray*)
      `(command| @[reducible] def $(mkIdent labelConcreteName) := $assembledLabel)

    -- build `FieldConcreteTypeInst`
    let fieldConcreteInstCmd ← do
      let assembledFieldConcreteInst ←`(term | $(mkIdent FieldConcreteTypeName) $termArray*)
      `(command| @[reducible] def $(mkIdent `FieldConcreteTypeInst) := $assembledFieldConcreteInst)

    -- build `StateConcrete`
    let stateCmd ← do
      let assembledState ←`(term| $(mkIdent stateName) $termArray*)
      let fieldConcreteInstTerm ← `(term | $(mkIdent `FieldConcreteType) $termArray*)
      `(command| @[reducible] def $(mkIdent stateConcreteName) := ($assembledState) $fieldConcreteInstTerm)

    elabVeilCommand theoryCmd
    elabVeilCommand labelCmd
    elabVeilCommand fieldConcreteInstCmd
    elabVeilCommand stateCmd

    -- build `initVeilMultiExecM`
    let initCmd ← do
      let assembledInitM ←`(term|
        ((( $(mkIdent `initMultiExec) $(mkIdent `TheoryConcrete) $(mkIdent `StateConcrete) )
        $termArray* )
        $(mkIdent `FieldConcreteTypeInst) ) )
      `(command| def $(mkIdent `initVeilMultiExecM) := $assembledInitM)

    -- build `nextVeilMultiExecM`
    let nextCmd ← do
      let assembledNextM ←`(term|
        ( (( $(mkIdent `nextActMultiExec) $(mkIdent `TheoryConcrete) $(mkIdent `StateConcrete) )
            $termArray* )
          /-$(mkIdent `FieldConcreteTypeInst)-/ ) )
      `(command| def $(mkIdent `nextVeilMultiExecM) := $assembledNextM)

    elabVeilCommand initCmd
    elabVeilCommand nextCmd
    getLabelList

def assembleBEqInstance (fieldNames : Array Name): CommandElabM Unit := do
  -- build `BEq` instance for `StateConcrete`
  let s1 := mkIdent `s1
  let s2 := mkIdent `s2
  let eqTerms : Array (TSyntax `term) ← fieldNames.mapM (fun f => do
    `(term| $s1.$(mkIdent f) == $s2.$(mkIdent f)))

  let beqBody : TSyntax `term ← do
    if h : eqTerms.size = 0 then
      `(term| True)
    else
      let mut acc := eqTerms[0]
      for i in [1:eqTerms.size] do
        acc ← `(term| $acc && $(eqTerms[i]!))
      pure acc

  let BEqInstCmd : Syntax ←
    `(command|
        instance : BEq $(mkIdent `StateConcrete) where
          beq := fun $s1 $s2 => $beqBody)
  elabVeilCommand BEqInstCmd


def assembleHashableInst (fieldNames : Array Name) : CommandElabM Unit := do
  -- build `Hashable` instance for `StateConcrete`
  let s := mkIdent `s
  let binds : Array (Name × TSyntax `term) ←
    fieldNames.mapM (fun f => do
      let rhs ← `(term| hash $s.$(mkIdent f))
      pure (f, rhs))

  -- 3) build final body: hash (rhs₁, rhs₂, ..., rhsₙ)
  let hashIds : Array (TSyntax `term) :=
    fieldNames.map (fun f => (mkIdent f : TSyntax `term))
  let finalBody : TSyntax `term ← liftMacroM <| mkTuple hashIds

  -- 4) from right to left: let xₙ := rhsₙ; ...; let x₁ := rhs₁; finalBody
  let body : TSyntax `term ←
    binds.foldrM (init := finalBody) (fun (f, rhs) acc =>
      `(term| let $(mkIdent f) := $rhs; $acc))

  -- 5) assemble instance (use λ to bind parameters to avoid binder category mismatch)
  let HashableInstCmd : TSyntax `command ←
    `(command|
        instance : Hashable $(mkIdent `StateConcrete) where
          hash := fun $s => hash $body)
  elabVeilCommand HashableInstCmd
where
  mkTuple (xs : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
    match xs.size with
    | 0 => `(term| ())
    | 1 => pure xs[0]!
    | _ =>
      let mut acc : TSyntax `term ← `(term| ($(xs[0]!), $(xs[1]!)))
      for i in [2:xs.size] do
        acc ← `(term| ($acc, $(xs[i]!)))
      return acc

instance [FinEnum α] : BEq α := by infer_instance

elab "#assembleInsts" : command => do
  let env ← getEnv
  let currentNS ← getCurrNamespace
  let stateNames := [currentNS ++ `State, `State]
  let mut sInfo : Option StructureInfo := none
  for stateName in stateNames do
    if env.contains stateName then
      if let some structInfo := getStructureInfo? env stateName then
        sInfo := some structInfo
        trace[veil.debug] "Found State structure: {stateName}"
        break
  let some structInfo := sInfo | throwError "Could not find State structure in any namespace"
  let fieldNames := structInfo.fieldNames
  assembleBEqInstance fieldNames
  assembleHashableInst fieldNames
