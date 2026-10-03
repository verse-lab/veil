module

public import Veil

open Lean Elab Command Veil Veil.Verifier

run_cmd do
  runManager
  withVCManager fun ref => do
    let mut mgr ← ref.get
    for name in [`sectionProof, `namespaceProof] do
      let data : VCData VCMetadata := {name, params := #[], statement := ← `(term| True), metadata := default}
      let (next, id) := mgr.addVC data {}
      mgr ← next.mkAddDischarger id fun statement id ch => do
        Discharger.fromTermWith (← `(term| by fail)) statement id ch fun _ outcome time =>
          match outcome with
          | .inl witness => pure (.proven witness none time)
          | .inr ex => pure (.error #[(ex, toJson "automatic proof failed")] time)
    ref.set mgr

section
@[veil] public theorem sectionProof : True := by trivial
end

namespace Proofs
@[veil] public theorem namespaceProof : True := by trivial
end Proofs

run_cmd do
  withReader (fun ctx => {ctx with fileMap := FileMap.ofString (ctx.fileMap.source ++ "\n-- edit after scopes")}) do
    let fresh ← getSession
    unless (← fresh.snapshot).nodes.valuesArray.all (·.hasInteractiveDischarger) do
      throwError "scope exit discarded an interactive registration checkpoint"
    let result ← waitFilteredSync (fun _ => true)
    unless result.totalSolved == 2 do throwError "scoped proofs did not survive editor replay"
