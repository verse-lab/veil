import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Action.Elaborators
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Action.Extract
import Veil.Frontend.DSL.State.Repr
import Veil.Core.Tools.Checker.Concrete.State
import Veil.Core.Tools.Checker.Concrete.ConcretizeUtil

import Mathlib.Data.FinEnum
import Mathlib.Tactic.ProxyType
import Veil.Core.Tools.Checker.Concrete.modelCheckerView
import ProofWidgets.Component.HtmlDisplay

import Lean.Parser.Term
open Lean Elab Command Veil


syntax (name := genNextActCommand) "gen_NextAct" : command

/-- Generate both NextAct specialization and executable list commands. -/
def genNextActCommands (mod : Veil.Module) : CommandElabM Unit := do
  let binders ← mod.collectNextActBinders
  -- Generate NextAct specialization
  let nextActCmd ← `(command |
    attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet] $instEnumerationForIteratedProd in
    #specialize_nextact with $(mkIdent `FieldConcreteType)
    injection_begin
      $[$binders]*
    injection_end => $(mkIdent `NextAct'))
  trace[veil.debug] "gen_NextAct: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic nextActCmd}"
  elabVeilCommand nextActCmd

  -- Generate executable list
  let execListCmd ← `(command |
    #gen_executable_list! log_entry_being $(mkIdent ``Std.Format)
    targeting $(mkIdent `NextAct')
    injection_begin
      $[$binders]*
    injection_end)
  trace[veil.debug] "gen_executable_NextAct: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic execListCmd}"
  elabVeilCommand execListCmd

@[command_elab genNextActCommand]
def elabGenNextAct : CommandElab := fun stx => do
  let mod ← getCurrentModule
  genNextActCommands mod

syntax (name := derivingDeciableInsts) "deriving_DecidableProps_state" : command
@[command_elab derivingDeciableInsts]
def deriveDecidablePropsForConcreteState : CommandElab := fun stx => do
  match stx with
  | `(command| deriving_DecidableProps_state) => do
    let mut mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
    let props := mod.invariants ++ mod.terminations
    for base in props do
      let explicitBinder := #[
            ← `(bracketedBinder| ($(mkIdent `rd) : $(mkIdent `TheoryConcrete) )),
            ← `(bracketedBinder| ($(mkIdent `st) : $(mkIdent `StateConcrete) )) ]
      let binder := explicitBinder
      let stx ← `(
        instance $[$binder]* : $(mkIdent ``Decidable) ($(mkIdent base.name) $(mkIdent `rd) $(mkIdent `st)) := by
          unfold $(mkIdent base.name):ident
          try dsimp [$(mkIdent base.name):ident, $(mkIdent `FieldConcreteType):ident, $(mkIdent `State.Label.toDomain):ident, $(mkIdent `State.Label.toCodomain):ident];
          infer_instance
      )
      elabVeilCommand stx
      trace[veil.debug] s!"Elaborated invariant definition for Concrete State: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic stx}"
  | _ => throwUnsupportedSyntax


syntax (name := concretizeTypeCmd) "#Concretize" term,* : command
/-- Generate label list (labelList) definition -/
def getLabelList : CommandElabM Unit := do
  trace[veil.info] "[getLabelList] Starting label list generation"
  let labelListDefName := (← getCurrNamespace) ++ `labelList
  if (← getEnv).contains labelListDefName then
    trace[veil.info] "[getLabelList] labelList already exists, skipping"
    return

  let labelConcreteName ← resolveGlobalConstNoOverloadCore `LabelConcrete
  let labelListCmd ← liftTermElabM do
    let labelListIdent := mkIdent `labelList
    let labelConcreteIdent := mkIdent labelConcreteName
    `(command|
      def $labelListIdent := ($(mkIdent ``FinEnum.ofEquiv) _ ($(mkIdent ``Equiv.symm) (proxy_equiv%($labelConcreteIdent)))).toList)
  trace[veil.debug] "[getLabelList] {labelListCmd}"
  elabVeilCommand labelListCmd


elab "#Concretize" args:term,* : command => do
    let termArray := args.getElems
    let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
    /- The `State`, `Theory` and `Label` can only be used after `#gen_spec` run -/
    if !Module.isSpecFinalized mod then
      throwError "The module specification should be finalized before concretizing types."
    let FieldConcreteTypeName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo (mkIdent `FieldConcreteType)

    let theoryConcreteName := `TheoryConcrete
    let stateConcreteName := `StateConcrete
    let labelConcreteName := `LabelConcrete

    let theoryCmd ← do
      let assembledTheory ←`(term| @$(mkIdent theoryName) $termArray*)
      `(command| @[reducible] def $(mkIdent theoryConcreteName) := $assembledTheory)

    let labelCmd ← do
      let assembledLabel ←`(term| @$(mkIdent labelTypeName) $termArray*)
      `(command| @[reducible] def $(mkIdent labelConcreteName) := $assembledLabel)

    let fieldConcreteInstCmd ← do
      let assembledFieldConcreteInst ←`(term| $(mkIdent FieldConcreteTypeName) $termArray*)
      `(command| @[reducible] def $(mkIdent `FieldConcreteTypeInst) := $assembledFieldConcreteInst)

    let stateCmd ← do
      let assembledState ←`(term| @$(mkIdent stateName))
      let fieldConcreteInstTerm ← `(term| $(mkIdent `FieldConcreteType) $termArray*)
      `(command| @[reducible] def $(mkIdent stateConcreteName) := ($assembledState) $fieldConcreteInstTerm)
    elabVeilCommand theoryCmd
    elabVeilCommand labelCmd
    elabVeilCommand fieldConcreteInstCmd
    elabVeilCommand stateCmd

    let initCmd ← do
      let assembledInitM ←`(term|
        ((( $(mkIdent `initMultiExec) $(mkIdent `TheoryConcrete) $(mkIdent `StateConcrete) )
        $termArray* )
        $(mkIdent `FieldConcreteTypeInst) ) )
      `(command| def $(mkIdent `initVeilMultiExecM) := $assembledInitM)

    let nextCmd ← do
      let assembledNextM ←`(term|
        ( (( $(mkIdent `nextActMultiExec) $(mkIdent `TheoryConcrete) $(mkIdent `StateConcrete) )
            $termArray* )
          /-$(mkIdent `FieldConcreteTypeInst)-/ ) )
      `(command| def $(mkIdent `nextVeilMultiExecM) := $assembledNextM)
    dbg_trace "nextCmd: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic nextCmd}"
    elabVeilCommand initCmd
    elabVeilCommand nextCmd
    getLabelList


def deriveBEqForState (mod : Veil.Module) : CommandElabM Unit := do
  let fieldNames := mod.mutableComponents.map (·.name)
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
        instance : $(mkIdent ``BEq) $(mkIdent `StateConcrete) where
          $(mkIdent `beq):ident := fun $s1 $s2 => $beqBody)
  trace[veil.debug] s!"BEqInstCmd: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic BEqInstCmd}"
  elabVeilCommand BEqInstCmd


def deriveHashableForState (mod : Veil.Module) : CommandElabM Unit := do
  let fieldNames := mod.mutableComponents.map (·.name)
  let s := mkIdent `s
  let binds : Array (Name × TSyntax `term) ←
    fieldNames.mapM (fun f => do
      let rhs ← `(term| $(mkIdent ``hash) $s.$(mkIdent f))
      pure (f, rhs))

  let hashIds : Array (TSyntax `term) :=
    fieldNames.map (fun f => (mkIdent f : TSyntax `term))
  let finalBody : TSyntax `term ← liftMacroM <| mkTuple hashIds

  let body : TSyntax `term ←
    binds.foldrM (init := finalBody) (fun (f, rhs) acc =>
      `(term| let $(mkIdent f) := $rhs; $acc))

  let HashableInstCmd : TSyntax `command ←
    `(command|
        instance : $(mkIdent ``Hashable) $(mkIdent `StateConcrete) where
          $(mkIdent `hash):ident := fun $s => $(mkIdent ``hash) $body)
  trace[veil.debug] s!"tryVlsUnfold : {← liftTermElabM <|Lean.PrettyPrinter.formatTactic HashableInstCmd}"
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

elab "deriving_BEq_ConcreteState" : command => do
  let mod ← getCurrentModule
  deriveBEqForState mod

elab "deriving_BEqHashable_ConcreteState" : command => do
  let mod ← getCurrentModule
  deriveBEqForState mod
  deriveHashableForState mod


def deriveToJsonForState (mod : Veil.Module) : CommandElabM Unit := do
  let sId := mkIdent `s

  let fieldNames := mod.mutableComponents.map (·.name)
  let pairs : Array (TSyntax `term) ← fieldNames.mapM (fun fName => do
    let fieldStr := fName.toString
    let lit      := Syntax.mkStrLit fieldStr
    let projId   := mkIdent fName
    `(term| ($lit, $(mkIdent ``toJson) $sId.$projId))
  )

  let toJsonRhs ← `(term| fun $sId => $(mkIdent ``Json.mkObj) [ $[$pairs],* ])
  let instToJsonIdent := (mkIdent `jsonOfState)
  let traceToJsonInst ←
    `(command|
      instance $instToJsonIdent:ident : $(mkIdent ``ToJson) $(mkIdent `StateConcrete) where
        $(mkIdent `toJson):ident := $toJsonRhs)
  trace[veil.debug] s!"toJsonCmd: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic traceToJsonInst}"
  elabVeilCommand traceToJsonInst

syntax (name := derivingToJsonForState) "deriving_toJson_for_state" : command

@[command_elab derivingToJsonForState]
def deriveToJsonForStateElab : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
  deriveToJsonForState mod


syntax (name := veilMakeExecutable) "#gen_exec" : command

/--Generate all required instances and definitions to make the symbolic model executable. -/
macro_rules
  | `(command| #gen_exec) => do
    `(simple_deriving_repr_for' $(mkIdent `State)
      gen_NextAct)

syntax (name := veilFinitizeTypes) "#finitize_types" term,* : command
macro_rules
  | `(command| #finitize_types $args:term,*) => do
    `(#Concretize $args,*
      deriving_BEqHashable_ConcreteState
      deriving_toJson_for_state
      deriving_DecidableProps_state)

syntax (name := veilSetTheory) "#set_theory" term : command
elab "#set_theory" theoryConcrete:term : command => do
  let setTheoryCmd ← liftTermElabM do
    `(command| def $(mkIdent `concreteTheory) : $(mkIdent `TheoryConcrete) := $theoryConcrete)
  elabVeilCommand setTheoryCmd


elab "#model_check" propTerm:term : command => do
  let prop ← `(term| fun $(mkIdent `rd) $(mkIdent `st) => $propTerm $(mkIdent `rd) $(mkIdent `st))
  let mod ← getCurrentModule
  let terminate ←
    if mod.terminations.size == 0 then
      `(term| fun $(mkIdent `rd) $(mkIdent `st) => $(mkIdent ``True))
    else
      let terminateName := mod.terminations[0]!.name |> mkIdent
      `(term| fun $(mkIdent `rd) $(mkIdent `st) => $terminateName $(mkIdent `rd) $(mkIdent `st))

  let runModelCheckerCmd ← liftTermElabM do
    `(command|
    -- def modelCheckerResult := (runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (fun rd st => mutual_exclusion rd st) default hash).snd
      -- def $(mkIdent `modelCheckerResult) := ($(mkIdent `runModelCheckerx) $(mkIdent `initVeilMultiExecM) $(mkIdent `nextVeilMultiExecM) $(mkIdent `labelList) $prop $terminate $(mkIdent `concreteTheory) $(mkIdent ``hash)).snd)
      def $(mkIdent `modelCheckerResult) := ($(mkIdent `runModelCheckerx) $(mkIdent `initVeilMultiExecM) $(mkIdent `nextVeilMultiExecM) $(mkIdent `labelList) $prop $terminate $(mkIdent `concreteTheory) $(mkIdent ``hash)))
  trace[veil.debug] s!"runModelCheckerCmd: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic runModelCheckerCmd}"
  elabVeilCommand runModelCheckerCmd

  let statesJsonCmd ← liftTermElabM do
    `(command|
      def $(mkIdent `statesJson) : $(mkIdent ``Lean.Json) := $(mkIdent ``Lean.toJson) ( $(mkIdent `recoverTrace) $(mkIdent `initVeilMultiExecM) $(mkIdent `nextVeilMultiExecM) $(mkIdent `concreteTheory) ( $(mkIdent `collectTrace) $(mkIdent `modelCheckerResult) )))
  elabVeilCommand statesJsonCmd
