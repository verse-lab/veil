module
public import Veil
meta import Veil.Core.Tools.Verifier.Server

veil module OwnerModuleA
individual flag : Bool
after_init { flag := false }
action toggle { flag := !flag }
invariant [safeA] true
#gen_spec
#check_invariants
end OwnerModuleA

veil module OwnerModuleB
individual flag : Bool
after_init { flag := true }
action toggle { flag := !flag }
invariant [safeB] true
#gen_spec
#check_invariants
end OwnerModuleB

-- Reopening the module selects its original runtime for captured-context reads.
veil module OwnerModuleA
run_cmd do
  let mgr ← Veil.Verifier.readVCManager
  unless mgr.nodes.toArray.any (fun (_, vc) => vc.metadata.propertyName? == some `safeA) do
    throwError "reopened A lost original VCs"
  if mgr.nodes.toArray.any (fun (_, vc) => vc.metadata.propertyName? == some `safeB) then
    throwError "reopened A read B's VCs"
end OwnerModuleA
