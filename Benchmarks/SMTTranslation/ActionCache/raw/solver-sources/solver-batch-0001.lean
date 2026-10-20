import Veil
set_option Elab.async false

open Lean Elab Command in
run_cmd liftTermElabM do
  let event (status : String) (elapsed : Nat) (detail : String := "") : IO Unit := do
    let j := Json.mkObj [
      ("event", toJson "solver"), ("phase", toJson "solver"),
      ("status", toJson status), ("elapsed_ms", toJson elapsed), ("detail", toJson detail)]
    IO.FS.withFile "/tmp/veil-action-cache/results/events/AWS_AWSFixed__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/AWS_AWSFixed__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/AWS_AWSFixed__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/AWS_AWSFixed__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/AWS_AWSFixed__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/AWS_AWSFixed__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/AWS_AWSFixed__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/AWS_AWSFixed__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/AWS_AWSFixed__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/AWS_AWSFixed__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/AWS_AWSFixed__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/AWS_AWSFixed__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Blockchain__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Blockchain__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Blockchain__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Blockchain__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Blockchain__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Blockchain__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Blockchain__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Blockchain__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Blockchain__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Blockchain__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Blockchain__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Blockchain__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Blockchain__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Blockchain__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Blockchain__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Blockchain__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Blockchain__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Blockchain__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Blockchain__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Blockchain__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Blockchain__d32__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Blockchain__d32__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_ChordRingMaintenance__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_ChordRingMaintenance__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_ChordRingMaintenance__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_ChordRingMaintenance__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_ChordRingMaintenance__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_ChordRingMaintenance__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_ChordRingMaintenance__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_ChordRingMaintenance__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_ChordRingMaintenance__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_ChordRingMaintenance__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_ChordRingMaintenance__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_ChordRingMaintenance__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_ChordRingMaintenance__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_ChordRingMaintenance__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_ChordRingMaintenance__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_ChordRingMaintenance__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_ChordRingMaintenance__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_ChordRingMaintenance__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_ChordRingMaintenance__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_ChordRingMaintenance__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_ChordRingMaintenance__d32__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_ChordRingMaintenance__d32__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_DecentralizedLock__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_DecentralizedLock__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_DecentralizedLock__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_DecentralizedLock__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_DecentralizedLock__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_DecentralizedLock__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_DecentralizedLock__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_DecentralizedLock__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_DecentralizedLock__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_DecentralizedLock__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_DecentralizedLock__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_DecentralizedLock__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_DecentralizedLock__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_DecentralizedLock__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_DecentralizedLock__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_DecentralizedLock__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_DecentralizedLock__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_DecentralizedLock__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_DecentralizedLock__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_DecentralizedLock__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_DecentralizedLock__d32__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_DecentralizedLock__d32__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_DecentralizedLock__d32__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_DecentralizedLock__d32__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigAll__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigAll__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigAll__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigAll__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigAll__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigAll__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigAll__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigAll__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigAll__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigAll__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigAll__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigAll__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigAll__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigAll__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigAll__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigAll__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigAll__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigAll__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigAll__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigAll__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigAll__d32__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigAll__d32__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigMajority__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigMajority__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigMajority__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigMajority__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigMajority__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigMajority__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigMajority__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigMajority__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigMajority__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigMajority__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigMajority__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigMajority__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigMajority__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigMajority__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigMajority__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigMajority__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigMajority__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigMajority__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigMajority__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigMajority__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_MultiSigMajority__d32__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_MultiSigMajority__d32__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_NOPaxos__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_NOPaxos__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_NOPaxos__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_NOPaxos__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_NOPaxos__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_NOPaxos__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_NOPaxos__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_NOPaxos__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_NOPaxos__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_NOPaxos__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_PaxosFirstOrder__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_PaxosFirstOrder__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_PaxosFirstOrder__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_PaxosFirstOrder__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_PaxosFirstOrder__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_PaxosFirstOrder__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_PaxosFirstOrder__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_PaxosFirstOrder__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_PaxosFirstOrder__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_PaxosFirstOrder__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_PaxosFirstOrder__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_PaxosFirstOrder__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_PaxosFirstOrder__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_PaxosFirstOrder__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_PaxosFirstOrder__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_PaxosFirstOrder__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_PaxosFirstOrder__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_PaxosFirstOrder__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_PaxosFirstOrder__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_PaxosFirstOrder__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_PaxosFirstOrder__d32__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_PaxosFirstOrder__d32__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_PaxosFirstOrder__d32__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_PaxosFirstOrder__d32__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_RicartAgrawala__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_RicartAgrawala__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_RicartAgrawala__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_RicartAgrawala__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_RicartAgrawala__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_RicartAgrawala__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_RicartAgrawala__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_RicartAgrawala__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_RicartAgrawala__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_RicartAgrawala__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_RicartAgrawala__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_RicartAgrawala__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_RicartAgrawala__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_RicartAgrawala__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_RicartAgrawala__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_RicartAgrawala__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_RicartAgrawala__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_RicartAgrawala__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_RicartAgrawala__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_RicartAgrawala__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_RicartAgrawala__d32__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_RicartAgrawala__d32__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_RicartAgrawala__d32__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_RicartAgrawala__d32__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Ring__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Ring__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Ring__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Ring__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Ring__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Ring__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Ring__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Ring__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Ring__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Ring__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Ring__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Ring__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Ring__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Ring__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Ring__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Ring__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Ring__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Ring__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Ring__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Ring__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Ring__d32__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Ring__d32__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_Ring__d32__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_Ring__d32__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_SuzukiKasami__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_SuzukiKasami__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_SuzukiKasami__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_SuzukiKasami__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_SuzukiKasami__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_SuzukiKasami__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_SuzukiKasami__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_SuzukiKasami__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_SuzukiKasami__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_SuzukiKasami__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_SuzukiKasami__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_SuzukiKasami__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_SuzukiKasami__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_SuzukiKasami__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_SuzukiKasami__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_SuzukiKasami__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_SuzukiKasami__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_SuzukiKasami__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_SuzukiKasami__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_SuzukiKasami__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_SuzukiKasami__d32__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_SuzukiKasami__d32__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_TwoPhaseCommit__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_TwoPhaseCommit__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_TwoPhaseCommit__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_TwoPhaseCommit__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_TwoPhaseCommit__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_TwoPhaseCommit__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_TwoPhaseCommit__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_TwoPhaseCommit__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_TwoPhaseCommit__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_TwoPhaseCommit__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_TwoPhaseCommit__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_TwoPhaseCommit__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_TwoPhaseCommit__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_TwoPhaseCommit__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_TwoPhaseCommit__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_TwoPhaseCommit__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_TwoPhaseCommit__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_TwoPhaseCommit__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_TwoPhaseCommit__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_TwoPhaseCommit__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_TwoPhaseCommit__d32__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_TwoPhaseCommit__d32__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Ivy_TwoPhaseCommit__d32__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Ivy_TwoPhaseCommit__d32__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_DieHard__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_DieHard__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_DieHard__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_DieHard__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_DieHard__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_DieHard__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_DieHard__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_DieHard__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_DieHard__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_DieHard__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_DieHard__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_DieHard__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_DieHard__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_DieHard__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_DieHard__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_DieHard__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_DieHard__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_DieHard__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_DieHard__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_DieHard__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_Prisoners__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_Prisoners__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_Prisoners__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_Prisoners__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_Prisoners__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_Prisoners__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_Prisoners__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_Prisoners__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_Prisoners__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_Prisoners__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_Prisoners__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_Prisoners__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_Prisoners__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_Prisoners__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_Prisoners__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_Prisoners__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_Prisoners__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_Prisoners__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_Prisoners__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_Prisoners__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_RiverCrossing__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_RiverCrossing__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_RiverCrossing__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_RiverCrossing__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_RiverCrossing__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_RiverCrossing__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_RiverCrossing__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_RiverCrossing__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_RiverCrossing__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_RiverCrossing__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_RiverCrossing__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_RiverCrossing__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_RiverCrossing__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_RiverCrossing__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_RiverCrossing__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_RiverCrossing__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_RiverCrossing__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_RiverCrossing__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_RiverCrossing__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_RiverCrossing__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_RiverCrossing__d32__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_RiverCrossing__d32__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Puzzles_RiverCrossing__d32__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Puzzles_RiverCrossing__d32__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_CheckpointLeaseFailover__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_CheckpointLeaseFailover__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_CheckpointLeaseFailover__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_CheckpointLeaseFailover__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_CheckpointLeaseFailover__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_CheckpointLeaseFailover__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_CheckpointLeaseFailover__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_CheckpointLeaseFailover__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_CheckpointLeaseFailover__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_CheckpointLeaseFailover__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_CheckpointLeaseFailover__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_CheckpointLeaseFailover__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_CheckpointLeaseFailover__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_CheckpointLeaseFailover__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_CheckpointLeaseFailover__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_CheckpointLeaseFailover__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_CheckpointLeaseFailover__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_CheckpointLeaseFailover__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_CheckpointLeaseFailover__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_CheckpointLeaseFailover__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_CheckpointLeaseFailover__d32__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_CheckpointLeaseFailover__d32__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_CheckpointLeaseFailover__d32__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_CheckpointLeaseFailover__d32__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_LeaseKeepaliveRace__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_LeaseKeepaliveRace__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_LeaseKeepaliveRace__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_LeaseKeepaliveRace__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_LeaseKeepaliveRace__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_LeaseKeepaliveRace__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_LeaseKeepaliveRace__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_LeaseKeepaliveRace__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_LeaseKeepaliveRace__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_LeaseKeepaliveRace__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_LeaseKeepaliveRace__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_LeaseKeepaliveRace__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_LeaseKeepaliveRace__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_LeaseKeepaliveRace__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_LeaseKeepaliveRace__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_LeaseKeepaliveRace__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_LeaseKeepaliveRace__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_LeaseKeepaliveRace__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_LeaseKeepaliveRace__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_LeaseKeepaliveRace__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_LeaseKeepaliveRace__d32__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_LeaseKeepaliveRace__d32__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_LeaseKeepaliveRace__d32__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_LeaseKeepaliveRace__d32__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_ReliableBroadcast__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_ReliableBroadcast__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_ReliableBroadcast__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_ReliableBroadcast__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_ReliableBroadcast__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_ReliableBroadcast__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_ReliableBroadcast__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_ReliableBroadcast__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_ReliableBroadcast__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_ReliableBroadcast__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_ReliableBroadcast__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_ReliableBroadcast__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_ReliableBroadcast__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_ReliableBroadcast__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_ReliableBroadcast__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_ReliableBroadcast__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_ReliableBroadcast__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_ReliableBroadcast__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_ReliableBroadcast__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_ReliableBroadcast__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_ReliableBroadcast__d32__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_ReliableBroadcast__d32__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Simulate_ReliableBroadcast__d32__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Simulate_ReliableBroadcast__d32__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Synchronous_FloodSet__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Synchronous_FloodSet__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Synchronous_FloodSet__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Synchronous_FloodSet__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Synchronous_FloodSet__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Synchronous_FloodSet__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Synchronous_FloodSet__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Synchronous_FloodSet__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Peterson__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Peterson__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Peterson__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Peterson__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Peterson__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Peterson__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Peterson__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Peterson__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Peterson__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Peterson__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Peterson__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Peterson__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Peterson__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Peterson__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Peterson__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Peterson__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Peterson__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Peterson__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Peterson__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Peterson__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Peterson__d32__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Peterson__d32__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Peterson__d32__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Peterson__d32__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Traffic__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Traffic__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Traffic__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Traffic__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Traffic__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Traffic__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Traffic__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Traffic__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Traffic__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Traffic__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Traffic__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Traffic__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Traffic__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Traffic__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Traffic__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Traffic__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Traffic__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Traffic__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Traffic__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Traffic__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Traffic__d32__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Traffic__d32__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_Traffic__d32__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_Traffic__d32__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_TwoPhaseCommit__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_TwoPhaseCommit__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_TwoPhaseCommit__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_TwoPhaseCommit__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_TwoPhaseCommit__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_TwoPhaseCommit__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_TwoPhaseCommit__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_TwoPhaseCommit__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_TwoPhaseCommit__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_TwoPhaseCommit__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_TwoPhaseCommit__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_TwoPhaseCommit__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_TwoPhaseCommit__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_TwoPhaseCommit__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_TwoPhaseCommit__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_TwoPhaseCommit__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_TwoPhaseCommit__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_TwoPhaseCommit__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_TwoPhaseCommit__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_TwoPhaseCommit__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_TwoPhaseCommit__d32__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_TwoPhaseCommit__d32__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/TLA_TwoPhaseCommit__d32__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/TLA_TwoPhaseCommit__d32__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_FloodSet__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_FloodSet__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_FloodSet__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_FloodSet__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_FloodSet__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_FloodSet__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_FloodSet__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_FloodSet__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_POPL26_RingDec__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_POPL26_RingDec__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_POPL26_RingDec__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_POPL26_RingDec__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_POPL26_RingDec__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_POPL26_RingDec__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_POPL26_RingDec__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_POPL26_RingDec__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_POPL26_RingDec__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_POPL26_RingDec__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_POPL26_RingDec__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_POPL26_RingDec__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_POPL26_RingDec__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_POPL26_RingDec__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_POPL26_RingDec__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_POPL26_RingDec__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_POPL26_RingDec__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_POPL26_RingDec__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_POPL26_RingDec__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_POPL26_RingDec__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_POPL26_RingDec__d32__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_POPL26_RingDec__d32__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_POPL26_RingDec__d32__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_POPL26_RingDec__d32__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_Ring__d1__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_Ring__d1__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_Ring__d1__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_Ring__d1__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_Ring__d2__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_Ring__d2__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_Ring__d2__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_Ring__d2__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_Ring__d4__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_Ring__d4__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_Ring__d4__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_Ring__d4__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_Ring__d8__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_Ring__d8__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_Ring__d8__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_Ring__d8__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_Ring__d16__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_Ring__d16__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_Ring__d16__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_Ring__d16__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_Ring__d32__cached__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_Ring__d32__cached__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
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
    IO.FS.withFile "/tmp/veil-action-cache/results/events/Tutorial_Ring__d32__local__default.solver.jsonl" .append fun h => h.putStrLn j.compress
  let query := (← IO.FS.readFile "/tmp/veil-action-cache/results/queries/Tutorial_Ring__d32__local__default.smt2").replace "(check-sat)" ""
  let options := Smt.defaultSolverOptions ++ [
    ("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  event "begin" 0
  let start ← IO.monoMsNow
  let result ← Smt.solve query (some 10) false options
  let elapsed := (← IO.monoMsNow) - start
  match result with
  | .ok (.sat _) => event "sat" elapsed
  | .ok (.unsat _ _) => event "unsat" elapsed
  | .ok (.unknown reason) => event "unknown" elapsed reason.toString
  | .error error => event "error" elapsed error.toString
