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

assumption [chosen_value] chosen.val = 1
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
