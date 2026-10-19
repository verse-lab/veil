module
public import Veil
public import Examples.StellarConsensus.SCPTheory
public import Veil.Util.Permutations
set_option Elab.async false
section
open Lean Elab Meta
meta def namespaceAudit (label : String) (path : System.FilePath) : MetaM Unit := do
  let names : Array String := #["AcceptorSet", "CacheState", "ClientsSet", "Color", "CommandSet", "CommittedTupleSet", "DecreeSet", "ENACTORS", "Enactor", "EnactorPC", "Guest", "GuestSet", "InstanceSet", "KeySet", "LogEntrySet", "MsgCmd", "MsgSet", "Occupied", "PCState", "Phase", "Position", "ProcSet", "Process", "ProcessSet", "RM", "RMStateType", "ReplicaSet", "ReplicaStatus", "ResourceSet", "Room", "SeqNumSet", "Status", "TMStateType", "TxIdSet", "VotedSet", "acceptor", "address", "ballot", "ballot_num", "block", "client", "command", "config", "data", "deadline", "destination", "electionSet", "epoch", "key", "keySet", "lease", "logSet", "msetMsg", "node", "nodeSet", "nodeset", "nset", "pcLabel", "pc_state", "position", "prisoner", "procSet", "process", "proposer", "quorum", "replica", "replicaSet", "replica_state", "resource", "round", "seqNum", "seq_t", "server", "serverSet", "serverStates", "signature", "slot", "states", "time", "transaction", "txId", "validator", "value"]
  let mut rows : Array Json := #[]
  for name in names do
    let resolved ← Lean.resolveGlobalName (Name.mkSimple name) false
    let mut entries : Array Json := #[]
    for (constant, fields) in resolved do
      let info ← getConstInfo constant
      let expr ← mkConstWithFreshMVarLevels constant
      let compatibleType ← isType expr
      entries := entries.push <| Json.mkObj [
        ("constant", toJson constant.toString), ("fields", toJson fields),
        ("type", toJson (← ppExpr info.type).pretty),
        ("compatible_type", toJson compatibleType)]
    rows := rows.push <| Json.mkObj [("name", toJson name), ("matches", toJson entries)]
  IO.FS.writeFile path <| (Json.mkObj [("scope", toJson label), ("rows", toJson rows)]).pretty
end
section
open Veil
run_cmd Lean.Elab.Command.liftTermElabM do
  namespaceAudit "model_baseline_open_Veil" "/tmp/veil-symbolic-bmc/namespace-audit/baseline.json"
end
section
open Lean Elab Tactic Meta Veil
run_cmd Lean.Elab.Command.liftTermElabM do
  namespaceAudit "unscoped_helper_opens" "/tmp/veil-symbolic-bmc/namespace-audit/unscoped.json"
end
