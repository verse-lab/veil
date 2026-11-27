module

public import VeilTest.Regression.ImportedProofs.Spec

veil module NodeProofs
prove_veil_invariant_goal keep off using wp by
  grind
end NodeProofs

veil module FlagProofs
namespace Alpha
prove_veil_invariant_goal keep off using wp by
  done
end Alpha

-- Only the copy in Completed carries the attribute.
namespace Shared
@[veil] theorem keep_off : True := True.intro
end Shared
end FlagProofs

open Lean Elab Command Veil in
public meta def checkCompetingFlagProofs (expectShared : Bool) : CommandElabM Unit := do
  let mgr ← Verifier.readVCManager
  let some vc := mgr.nodes.valuesArray.find? (·.name == `keep_off) | throwError "missing VC"
  let proofs := vc.effectiveDischargers
  unless proofs.all (·.isInteractive) &&
      proofs.size == (if expectShared then 3 else 2) &&
      proofs.any (fun d => d.term.any (·.raw.getId == ``FlagProofs.Shared.keep_off)) == expectShared do
    throwError "unexpected registrations for keep_off"
  let some (_, witness) := mgr.provenWitness? vc.uid | throwError "no successful proof"
  unless witness.getUsedConstants.contains ``FlagProofs.Alpha.keep_off do
    throwError "unexpected witness {witness}"
