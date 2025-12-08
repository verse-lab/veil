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
