module

public import Veil
open Lean Meta Elab Command Veil

public class ReplayFlag (α : Type) where
  flag : α → Bool
  mirror : α → Bool
  agree : ∀ x, mirror x = flag x

veil module InstanceReplay

type first
type second
instantiate aFlag : ReplayFlag first
instantiate bFlag : ReplayFlag second
immutable individual a : first
immutable individual b : second
individual seen : Bool
after_init { seen := ReplayFlag.flag a && !ReplayFlag.flag b }
action idle { pure () }
invariant [clear] seen = false
#gen_spec

set_option veil.violationIsError false
#guard_msgs (drop info, drop warning) in
#check_invariants

#guard_msgs (drop info) in
sat trace [opposite] { assert (seen = true) }

run_cmd do
  let mod ← getCurrentModule
  let mut checked := 0
  for vc in (← Verifier.waitFilteredSync (fun _ => true)).vcs do
    let some model := vc.timing.dischargers.findSome? (fun d => match d.result with
      | some (.proven _ (some (.sat ms)) _) | some (.disproven (some (.sat ms)) _) => ms.findSome? id
      | _ => none) | continue
    unless model.structuredJson.getObjValD "witnessCheck" == toJson WitnessCheck.checked do
      throwError "{vc.metadata}: {model.structuredJson.getObjValD "witnessCheck"}"
    if let .trace md := vc.metadata then
      liftTermElabM do
        let (_, q) ← mkTraceQuery mod (← `(traceSpec| assert ($(mkIdent `seen):ident = true)))
        let w ← buildTraceFromModel model.raw mod md.numTransitions
        let vals ← witnessAssignments w.ctx w.extraVals
        let some wrong := vals[modelInstanceName `bFlag.flag]? | throwError "missing bFlag.flag"
        let corrupt (both : Bool) := w.extraVals.mapM fun (k, v) => do
          let n ← getExprName w.ctx k
          return (k, if n == some (modelInstanceName `aFlag.flag) ||
            (both && n == some (modelInstanceName `aFlag.mirror)) then wrong else v)
        let swapped ← q.check { w with extraVals := ← corrupt true }
        unless swapped == .invalid do throwError "swapped instance: {repr swapped}"
        let .unverified _ ← q.check { w with extraVals := ← corrupt false }
          | throwError "accepted a dictionary with a false law"
    checked := checked + 1
  unless checked == 3 do throwError "expected trace, WP and TR counterexamples, got {checked}"

end InstanceReplay
