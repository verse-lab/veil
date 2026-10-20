import Veil
set_option Elab.async false

open Lean Elab Command in
run_cmd liftTermElabM do
  let event (status : String) (elapsed : Nat) (detail : String := "") : IO Unit := do
    let j := Json.mkObj [
      ("event", toJson "solver"), ("phase", toJson "solver"),
      ("status", toJson status), ("elapsed_ms", toJson elapsed), ("detail", toJson detail)]
    IO.FS.withFile "/tmp/veil-transition-local/solver-controls/extended-30s/events/Ivy_TwoPhaseCommit__d8__early__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-transition-local/results/queries/Ivy_TwoPhaseCommit__d8__early__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 30) false options
  let elapsed := (← IO.monoMsNow) - start
  match result with
  | .ok (.sat _) => event "sat" elapsed
  | .ok (.unsat _ _) => event "unsat" elapsed
  | .ok (.unknown reason) => event "unknown" elapsed reason.toString
  | .error error => event "error" elapsed error.toString

open Lean Elab Command in
run_cmd liftTermElabM do
  let event (status : String) (elapsed : Nat) (detail : String := "") : IO Unit := do
    let j := Json.mkObj [
      ("event", toJson "solver"), ("phase", toJson "solver"),
      ("status", toJson status), ("elapsed_ms", toJson elapsed), ("detail", toJson detail)]
    IO.FS.withFile "/tmp/veil-transition-local/solver-controls/extended-30s/events/Ivy_TwoPhaseCommit__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-transition-local/results/queries/Ivy_TwoPhaseCommit__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 30) false options
  let elapsed := (← IO.monoMsNow) - start
  match result with
  | .ok (.sat _) => event "sat" elapsed
  | .ok (.unsat _ _) => event "unsat" elapsed
  | .ok (.unknown reason) => event "unknown" elapsed reason.toString
  | .error error => event "error" elapsed error.toString

open Lean Elab Command in
run_cmd liftTermElabM do
  let event (status : String) (elapsed : Nat) (detail : String := "") : IO Unit := do
    let j := Json.mkObj [
      ("event", toJson "solver"), ("phase", toJson "solver"),
      ("status", toJson status), ("elapsed_ms", toJson elapsed), ("detail", toJson detail)]
    IO.FS.withFile "/tmp/veil-transition-local/solver-controls/extended-30s/events/Simulate_CheckpointLeaseFailover__d16__early__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-transition-local/results/queries/Simulate_CheckpointLeaseFailover__d16__early__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 30) false options
  let elapsed := (← IO.monoMsNow) - start
  match result with
  | .ok (.sat _) => event "sat" elapsed
  | .ok (.unsat _ _) => event "unsat" elapsed
  | .ok (.unknown reason) => event "unknown" elapsed reason.toString
  | .error error => event "error" elapsed error.toString

open Lean Elab Command in
run_cmd liftTermElabM do
  let event (status : String) (elapsed : Nat) (detail : String := "") : IO Unit := do
    let j := Json.mkObj [
      ("event", toJson "solver"), ("phase", toJson "solver"),
      ("status", toJson status), ("elapsed_ms", toJson elapsed), ("detail", toJson detail)]
    IO.FS.withFile "/tmp/veil-transition-local/solver-controls/extended-30s/events/Simulate_CheckpointLeaseFailover__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-transition-local/results/queries/Simulate_CheckpointLeaseFailover__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 30) false options
  let elapsed := (← IO.monoMsNow) - start
  match result with
  | .ok (.sat _) => event "sat" elapsed
  | .ok (.unsat _ _) => event "unsat" elapsed
  | .ok (.unknown reason) => event "unknown" elapsed reason.toString
  | .error error => event "error" elapsed error.toString

open Lean Elab Command in
run_cmd liftTermElabM do
  let event (status : String) (elapsed : Nat) (detail : String := "") : IO Unit := do
    let j := Json.mkObj [
      ("event", toJson "solver"), ("phase", toJson "solver"),
      ("status", toJson status), ("elapsed_ms", toJson elapsed), ("detail", toJson detail)]
    IO.FS.withFile "/tmp/veil-transition-local/solver-controls/extended-30s/events/TLA_Peterson__d8__early__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-transition-local/results/queries/TLA_Peterson__d8__early__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 30) false options
  let elapsed := (← IO.monoMsNow) - start
  match result with
  | .ok (.sat _) => event "sat" elapsed
  | .ok (.unsat _ _) => event "unsat" elapsed
  | .ok (.unknown reason) => event "unknown" elapsed reason.toString
  | .error error => event "error" elapsed error.toString

open Lean Elab Command in
run_cmd liftTermElabM do
  let event (status : String) (elapsed : Nat) (detail : String := "") : IO Unit := do
    let j := Json.mkObj [
      ("event", toJson "solver"), ("phase", toJson "solver"),
      ("status", toJson status), ("elapsed_ms", toJson elapsed), ("detail", toJson detail)]
    IO.FS.withFile "/tmp/veil-transition-local/solver-controls/extended-30s/events/TLA_Peterson__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-transition-local/results/queries/TLA_Peterson__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 30) false options
  let elapsed := (← IO.monoMsNow) - start
  match result with
  | .ok (.sat _) => event "sat" elapsed
  | .ok (.unsat _ _) => event "unsat" elapsed
  | .ok (.unknown reason) => event "unknown" elapsed reason.toString
  | .error error => event "error" elapsed error.toString
