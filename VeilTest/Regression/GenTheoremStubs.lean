module

public import Veil
public meta import Lean.Util.CollectAxioms

set_option veil.smt.trust false
set_option veil.printCounterexamples false

-- Deliberately install an admitted user stub, without registering it as a
-- verifier proof. The second declaration hides the sorry behind a constant,
-- exercising transitive provenance rather than Expr.hasSorry alone.
open Lean Elab Command in
private meta def installAdmittedVC (vcName : Name) (indirect : Bool) : CommandElabM Unit := do
  let mgr ← Veil.Verifier.vcManager.atomically fun ref => ref.get
  let some (_, vc) := mgr.nodes.toArray.find? (fun (_, vc) => vc.name == vcName)
    | throwError "missing regression VC {vcName}"
  liftTermElabM do
    let statementType ← vc.toVCStatement.type
    let admitted ← Meta.mkSorry statementType false
    if indirect then
      let helper ← Veil.addVeilTheorem `admitted_user_helper statementType admitted
      discard <| Veil.addVeilTheorem vcName statementType (mkConst helper)
    else
      discard <| Veil.addVeilTheorem vcName statementType admitted

veil module ReuseAdmittedVC

individual flag : Bool
after_init { flag := false }
action keep { pure () }
invariant [clear] flag = false
#gen_spec
#check_invariants

/-- warning: declaration uses `sorry` -/
#guard_msgs in
run_cmd installAdmittedVC `keep_clear true

/--
error: cannot reuse VC theorem `ReuseAdmittedVC.keep_clear` because its proof depends on sorryAx while veil.smt.trust is false
-/
#guard_msgs in
#gen_theorems

run_cmd do
  if (← Lean.getEnv).contains `ReuseAdmittedVC.Invariants.is_inv then
    throwError "admitted VC stub enabled an unconditional reachability export"

end ReuseAdmittedVC

veil module FailedVCWithStub

individual flag : Bool
after_init { flag := false }
action set_flag { flag := true }
invariant [clear] flag = false
#gen_spec

/--
error: Initialization must establish the invariant:
  doesNotThrow ... ✅
  clear ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  set_flag
    doesNotThrow ... ✅
    clear ... ❌
-/
#guard_msgs(error, drop info, drop warning) in
#check_invariants

/-- warning: declaration uses `sorry` -/
#guard_msgs in
run_cmd installAdmittedVC `set_flag_clear false

/--
warning: #gen_theorems exported available local lemmas, but omitted reachable-invariant theorems: missing proof obligations [set_flag_clear_tr]
-/
#guard_msgs in
#gen_theorems

run_cmd do
  if (← Lean.getEnv).contains `FailedVCWithStub.Invariants.is_inv then
    throwError "a right-typed stub covered a failed verifier obligation"

end FailedVCWithStub

veil module ReuseAdmittedReachability

individual flag : Bool
after_init { flag := false }
action keep { pure () }
invariant [clear] flag = false
#gen_spec
#check_invariants

open Lean Elab Command in
/-- warning: declaration uses `sorry` -/
#guard_msgs in
run_cmd liftTermElabM do
  let statement ← Term.elabType (← `(term|
    ∀ (th : Theory) (st : State FieldAbstractType),
      relationalTransitionSystem.reachable th st → clear th st))
  Term.synthesizeSyntheticMVarsNoPostponing
  let statement ← instantiateMVars statement
  let admitted ← Meta.mkSorry statement false
  let helper ← Veil.addVeilTheorem `admitted_user_helper statement admitted
  discard <| Veil.addVeilTheorem `Invariants.is_inv statement (mkConst helper)

/--
error: cannot reuse reachable-invariant theorem `ReuseAdmittedReachability.Invariants.is_inv` because its proof depends on sorryAx while veil.smt.trust is false
-/
#guard_msgs in
#gen_theorems

run_cmd do
  if (← Lean.getEnv).contains `ReuseAdmittedReachability.clear.is_inv then
    throwError "an admitted outer theorem enabled projection export"

end ReuseAdmittedReachability
