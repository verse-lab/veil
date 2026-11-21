module

public import Veil

open Lean Elab Command Meta
open Veil

set_option veil.violationIsError false

private meta def stepCounterexamples (property : Name) : CommandElabM (Array AnnotatedSmtModel) := do
  let results ← Verifier.waitFilteredSync (fun _ => true)
  #[VCStyle.wp, .tr].mapM fun style => do
    let some vc := results.vcs.find? (fun vc => match vc.metadata with
      | .induction md => md.action == `step && md.property == property && md.style == style
      | _ => false)
      | throwError "missing {style} verification condition"
    let some model := vc.timing.dischargers.findSome? (fun discharger => match discharger.result with
      | some (.disproven (some (.sat models)) _) => models.findSome? id
      | _ => none)
      | throwError "missing structured {style} counterexample"
    return model

private meta def traceModel : CommandElabM AnnotatedSmtModel := do
  let results ← Verifier.waitFilteredSync VCMetadata.isTrace
  let some model := results.vcs.findSome? (fun vc =>
      vc.timing.dischargers.findSome? fun discharger => match discharger.result with
      | some (.proven _ (some (.sat models)) _) => models.findSome? id
      | _ => none)
    | throwError "missing structured satisfying trace"
  return model

private meta def traceInstantiation : CommandElabM Expr := do
  let model ← traceModel
  let mod ← getCurrentModule
  liftTermElabM do
    let sortMap ← parseSortsFromModel model.raw
    let (sortArgs, enumAdapts) ← resolveSortArgsAndEnumAdapts model.raw mod sortMap
    let (moduleArgs, _) ← resolveModuleArgs model.raw mod sortArgs enumAdapts
    buildInstantiationExpr mod moduleArgs

veil module FunctionParameterCounterexample

type proc
param f : Nat → Nat
function x (p : proc) : Nat
function y (p : proc) : Nat

assumption [function_values] f 1 = 1 ∧ f 2 = 2
after_init {
  x P := 0
  y P := f 0
}
action step (p : proc) {
  x p := x p + 1
  y p := f (x p + 1)
}
invariant [def_y] ∀ p, y p = f (x p)
#gen_spec

#guard_msgs (drop info, drop warning) in
#check_invariants

run_cmd do
  let mod ← getCurrentModule
  for model in ← stepCounterexamples `def_y do
    liftTermElabM do
      let cti ← buildCounterexampleExprs model.raw mod `step
      let f ← mkAppM `FunctionParameterCounterexample.Instantiation.f #[cti.instExpr]
      for n in [1, 2] do
        unless ← isDefEq (mkApp f (mkNatLit n)) (mkNatLit n) do
          throwError "reconstructed f disagrees with the model at {n}"

end FunctionParameterCounterexample

veil module ShadowedParameterCounterexample

param unused : Nat
param flag : Bool
individual x : Nat

assumption [flag_is_true] flag = true
after_init { x := 0 }
action step { x := 7 }
#guard_msgs (drop warning) in
invariant [is_zero] ∀ flag : Bool, flag = false → x = 0
#gen_spec

#guard_msgs (drop info, drop warning) in
#check_invariants

run_cmd do
  let mod ← getCurrentModule
  for model in ← stepCounterexamples `is_zero do
    let values := model.structuredJson.getObjValD "extraVals"
    unless values.getObjValD "param.flag" == toJson true && values.getObjValD "flag" == toJson false do
      throwError "the module parameter and quantified variable lost their separate assignments"
    liftTermElabM do
      let cti ← buildCounterexampleExprs model.raw mod `step
      let flag ← mkAppM `ShadowedParameterCounterexample.Instantiation.flag #[cti.instExpr]
      unless ← isDefEq flag (mkConst ``Bool.true) do
        throwError "reconstructed flag contradicts the module assumption"

end ShadowedParameterCounterexample

veil module DependentParameterTrace

param n : Nat
param chosen : Fin (n + 1)
individual x : Nat

assumption [chosen_value] n = 2 ∧ chosen.val = 1
after_init { x := 0 }
action step { x := chosen.val }
invariant [bound] x ≤ 1
#gen_spec

/-- info: ✅ Satisfying trace found -/
#guard_msgs (substring := true) in
sat trace {
  step
  assert (x = 1)
}

run_cmd do
  let model ← traceModel
  unless model.structuredJson.getObjValD "witnessCheck" == toJson WitnessCheck.checked do
    throwError "dependent trace parameters failed replay"
  let inst ← traceInstantiation
  liftTermElabM do
    let n ← mkAppM `DependentParameterTrace.Instantiation.n #[inst]
    let chosen ← mkAppM `DependentParameterTrace.Instantiation.chosen #[inst]
    let chosenVal ← mkAppM ``Fin.val #[chosen]
    unless ← isDefEq n (mkNatLit 2) do
      throwError "trace reconstructed the wrong bound"
    unless ← isDefEq chosenVal (mkNatLit 1) do
      throwError "trace reconstructed the wrong Fin value"

end DependentParameterTrace

public class CounterexampleDictionary where
  amount : Nat
  deriving Inhabited, Repr

veil module DictionaryParameterCounterexample

param limit : Nat
type tenant
param owner : tenant
param dictionary : CounterexampleDictionary
individual x : Nat
individual holder : tenant

assumption [dictionary_value] dictionary.amount = 7
after_init {
  x := 0
  holder := owner
}
action step (t : tenant) {
  require dictionary.amount > limit
  x := dictionary.amount
  holder := t
}
invariant [bounded] x ≤ limit
#gen_spec

#guard_msgs (drop info, drop warning) in
#check_invariants

run_cmd do
  let mod ← getCurrentModule
  for model in ← stepCounterexamples `bounded do
    liftTermElabM do
      let cti ← buildCounterexampleExprs model.raw mod `step
      let dictionary ← mkAppM `DictionaryParameterCounterexample.Instantiation.dictionary #[cti.instExpr]
      let amount ← mkAppOptM ``CounterexampleDictionary.amount #[some dictionary]
      unless ← isDefEq amount (mkNatLit 7) do
        throwError "reconstructed dictionary lost its amount"

end DictionaryParameterCounterexample

veil module NestedParameterCounterexample

param bound : ULift.{0} (Nat × Nat)
-- This also exposes the pair type to the recursive case splitter.
param unusedPair : Nat × Nat
individual x : Nat

assumption [bound_value] bound.down.1 = 7
after_init { x := 0 }
action step { x := bound.down.1 }
invariant [is_zero] x = 0
#gen_spec

#guard_msgs (drop info, drop warning) in
#check_invariants

run_cmd do
  let mod ← getCurrentModule
  for model in ← stepCounterexamples `is_zero do
    liftTermElabM do
      let cti ← buildCounterexampleExprs model.raw mod `step
      let bound ← mkAppM `NestedParameterCounterexample.Instantiation.bound #[cti.instExpr]
      let pair ← mkAppM ``ULift.down #[bound]
      let fst ← mkAppM ``Prod.fst #[pair]
      unless ← isDefEq fst (mkNatLit 7) do
        throwError "reconstructed bound.down.1 contradicts the solver assignment"

end NestedParameterCounterexample

public inductive ConfigurationMode where
  | manual
  | automatic
  deriving Repr

public structure CounterexampleConfiguration where
  mode : ConfigurationMode
  amount : Nat
  deriving Repr

public instance : Inhabited CounterexampleConfiguration := ⟨⟨.automatic, 11⟩⟩

veil module DefaultedParameterCounterexample

param unused : CounterexampleConfiguration
param config : CounterexampleConfiguration
individual x : Nat

assumption [amount] config.amount = 7
after_init { x := 0 }
action step { x := config.amount }
invariant [is_zero] x = 0
#gen_spec

#guard_msgs (drop info, drop warning) in
#check_invariants

/-- info: ✅ Satisfying trace found -/
#guard_msgs (substring := true) in
sat trace {
  step
  assert (x = 7)
}

run_cmd do
  let mod ← getCurrentModule
  let traceInst ← traceInstantiation
  let counterexamples ← stepCounterexamples `is_zero
  liftTermElabM do
    let check (inst : Expr) (name : Name) (amount : Nat) : MetaM Unit := do
      let config ← mkAppM name #[inst]
      let configMode ← mkAppM ``CounterexampleConfiguration.mode #[config]
      let configAmount ← mkAppM ``CounterexampleConfiguration.amount #[config]
      unless ← isDefEq configMode (mkConst ``ConfigurationMode.automatic) do
        throwError "reconstructed {name} lost its default mode"
      unless ← isDefEq configAmount (mkNatLit amount) do
        throwError "reconstructed {name} has the wrong amount"
    check traceInst `DefaultedParameterCounterexample.Instantiation.config 7
    for model in counterexamples do
      let cti ← buildCounterexampleExprs model.raw mod `step
      check cti.instExpr `DefaultedParameterCounterexample.Instantiation.config 7
      check cti.instExpr `DefaultedParameterCounterexample.Instantiation.unused 11

end DefaultedParameterCounterexample

veil module ScopedTraceBinders

param _tr1_tag : Nat
immutable individual start : Nat
individual counter : Nat
assumption start = 4 ∧ _tr1_tag = 9
after_init { counter := start }
action add (n : Fin 16) { counter := counter + n.val }
action reset { counter := 0 }
invariant True
#gen_spec

/-- info: ✅ Satisfying trace found -/
#guard_msgs (substring := true) in
sat trace {
  add
  assert (counter = 7)
  any action
  assert (counter = 12)
}

run_cmd do
  let mod ← getCurrentModule
  let model ← traceModel
  let inst ← traceInstantiation
  liftTermElabM do
    let userTag ← mkAppM `ScopedTraceBinders.Instantiation._tr1_tag #[inst]
    unless ← isDefEq userTag (mkNatLit 9) do throwError "incorrect module parameter"
    let tr ← buildTraceFromModel model.raw mod 2
    let start ← mkAppM `ScopedTraceBinders.Theory.start #[tr.theoryExpr]
    unless ← isDefEq start (mkNatLit 4) do throwError "incorrect theory"
    unless tr.steps.size == 2 do throwError "incomplete trace"
    for (state, expected) in (#[tr.initialState] ++ tr.steps.map (·.nextState)).zip #[4, 7, 12] do
      let value ← mkAppM `ScopedTraceBinders.State.counter #[state]
      unless ← isDefEq value (mkNatLit expected) do throwError "incorrect state {expected}"
    for (label, expected) in (tr.steps.map (·.transitionLabel)).zip #[3, 5] do
      let arg ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 16)) expected
      let target ← mkAppOptM `ScopedTraceBinders.Label.add #[some userTag, some arg]
      unless ← isDefEq label target do throwError "incorrect action or argument at {label}"

end ScopedTraceBinders

veil module ScopedInductionBinders

individual counter : Nat
after_init { counter := 1 }
action step (n : Fin 16) (j : Fin (n.val + 1)) {
  require n.val = 3 ∧ j.val = 2
  counter := n.val + j.val
}
invariant [atOne] ∀ n : Nat, n = 7 → counter = 1
#gen_spec

#guard_msgs (drop info, drop warning) in
#check_invariants

/-- info: ✅ Satisfying trace found -/
#guard_msgs (substring := true) in
sat trace {
  step
  assert (counter = 5)
}

run_cmd do
  let mod ← getCurrentModule
  let witness ← traceModel
  let expected ← liftTermElabM do
    let n ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 16)) 3
    let j ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 4)) 2
    mkAppM `ScopedInductionBinders.Label.step #[n, j]
  liftTermElabM do
    let tr ← buildTraceFromModel witness.raw mod 1
    unless tr.steps.size == 1 && (← isDefEq tr.steps[0]!.transitionLabel expected) do
      throwError "incorrect dependent trace arguments"

  for (model, style) in (← stepCounterexamples `atOne).zip #[VCStyle.wp, .tr] do
    let values := model.structuredJson.getObjValD "extraVals"
    unless values.getObjValD "n" == toJson 7 do
      throwError "lost the quantified variable in {values}"
    liftTermElabM do
      let cti ← buildCounterexampleExprs model.raw mod `step
      let some label := cti.labelExpr | throwError "missing action label"
      unless ← isDefEq label expected do throwError "incorrect action argument in {label}"
      let counter ← mkAppM `ScopedInductionBinders.State.counter #[cti.preStateExpr]
      unless ← isDefEq counter (mkNatLit 1) do throwError "incorrect pre-state"
      if style == .tr && cti.postStateExpr.isNone then throwError "missing transition post-state"
      if let some post := cti.postStateExpr then
        let counter ← mkAppM `ScopedInductionBinders.State.counter #[post]
        unless ← isDefEq counter (mkNatLit 5) do throwError "incorrect post-state"

end ScopedInductionBinders
