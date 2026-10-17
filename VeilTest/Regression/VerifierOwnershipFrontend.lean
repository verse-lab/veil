module
public import Veil
meta import Veil.Core.Tools.Verifier.Server

open Lean Elab Command Veil Veil.Verifier

private meta def addGoal (n : Name) : CommandElabM Unit := withVCManager fun ref => do
  let data : VCData VCMetadata := {
    name := n, params := #[], statement := ← `(True)
    metadata := .induction { (default : InductionVCMetadata) with property := n } }
  let (mgr, _) := (← ref.get).addVC data {}
  ref.set mgr

veil module OwnedA
set_option veil.deferVCGeneration true
after_init { pure () }
action step { pure () }
invariant true
#gen_spec
run_cmd addGoal `onlyA
end OwnedA

veil module OwnedB
set_option veil.deferVCGeneration true
after_init { pure () }
action step { pure () }
invariant true
#gen_spec
run_cmd addGoal `onlyB
end OwnedB

veil module OwnedA
run_cmd do
  let mgr ← readVCManager
  unless mgr.nodes.valuesArray.map (·.name) == #[`onlyA] do
    throwError "reopened A read B manager"
@[veil] theorem onlyA : True := True.intro
run_cmd do
  let mgr ← readVCManager
  unless mgr._doneWith[0]? == some .proven do throwError "A attribute wrote wrong owner"
  -- Add a synthetic automatic witness to the shared runtime; never install an
  -- effective checkpoint view back into that runtime.
  withVCManager fun ref => do
    let mgr ← ref.get
    let (mgr, id) := mgr.addVC { (mgr.nodes[0]!).toVCData with name := `generatedA } {}
    let target := { (mgr.nodes[id]!) with successful := some 0 }
    ref.set { mgr with
      nodes := mgr.nodes.insert id target
      _dischargerResults := mgr._dischargerResults.insert (id, 0)
        (.proven (some (mkConst ``True.intro)) none 0) }
  addProvenTheoremsInDependencyOrder (fun _ => true)
  unless (← getEnv).contains `OwnedA.generatedA do throwError "generated theorem used wrong context"
end OwnedA

veil module OwnedB
run_cmd do
  let mgr ← readVCManager
  unless mgr.nodes.valuesArray.map (·.name) == #[`onlyB] do
    throwError "A mutation leaked into reopened B"
  unless mgr._doneWith.isEmpty do throwError "A theorem registration leaked into B"
@[veil] theorem onlyB : True := True.intro
end OwnedB

veil module OwnedA
run_cmd do
  let some b := (vcManagerExt.getState (← getEnv))[`OwnedB]?
    | throwError "missing B owner"
  let bId ← b.manager.atomically fun ref => return (← ref.get)._managerId
  unless (interactiveRegistrationsExt.getState (← getEnv)).contains bId do
    throwError "missing B interactive checkpoint"
  reset bId
  unless (interactiveRegistrationsExt.getState (← getEnv)).contains bId do
    throwError "foreign-owner reset erased B interactive checkpoint"
end OwnedA

veil module OwnedB
run_cmd do
  unless (← readVCManager)._doneWith[0]? == some .proven do
    throwError "foreign-owner reset changed B effective proof"
end OwnedB

veil module UnpreparedC
run_cmd do
  let rejected ← try
    discard <| getVCManagerOwner
    pure false
  catch _ => pure true
  unless rejected do throwError "unprepared C inherited previous manager"
end UnpreparedC
