import Veil.Core.Tools.Verifier.Manager

open Lean Elab Command Veil

run_cmd do
  let ch ← Std.Channel.new
  let mgr : VCManager Nat Unit ← VCManager.new ch
  let data : VCData Nat := {name := `test, params := #[], statement := ← `(term| True), metadata := 0}
  let (mgr, root) := mgr.addVC data {}
  let (mgr, middle) := mgr.addVC {data with metadata := 1} ((Std.HashSet.emptyWithCapacity).insert root)
  let (mgr, leaf) := mgr.addVC {data with metadata := 2} ((Std.HashSet.emptyWithCapacity).insert middle)
  let (mgr, unrelated) := mgr.addVC {data with metadata := 3} {}
  let selected := mgr.enableMatching (· == 2)
  unless selected.enabledVCs.contains root && selected.enabledVCs.contains middle && selected.enabledVCs.contains leaf do
    throwError "filtered verification failed to enable transitive prerequisites"
  unless !selected.enabledVCs.contains unrelated do throwError "enabled an unrelated VC"
  let selected := selected.enableMatching (· == 3)
  unless selected.enabledVCs.size == 4 do throwError "a later request disabled earlier work"
