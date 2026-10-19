import Veil

set_option Elab.async false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd liftTermElabM do
  let root := System.FilePath.mk "/tmp/veil-early-intro-multi"
  let models := #["Ring"]
  let options := Smt.defaultSolverOptions ++ [("finite-model-find", "true"),
    ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
  for model in models do
    for depth in #[4, 8] do
      for mode in #["old", "early"] do
        let label := s!"{model}_{mode}_{depth}"
        let path := root / (label ++ ".smt2")
        if ← path.pathExists then
          let query := (← IO.FS.readFile path).replace "(check-sat)" ""
          let start ← IO.monoMsNow
          let result ← Smt.solve query (some 10) false options
          let status := match result with
            | .ok (.sat _) => "sat"
            | .ok (.unsat _ _) => "unsat"
            | .ok (.unknown reason) => "unknown:" ++ reason.toString
            | .error err => "error:" ++ err.toString
          IO.println s!"REPLAY_RESULT {label} status={status} solver_ms={(← IO.monoMsNow)-start} bytes={query.utf8ByteSize}"
        else
          IO.println s!"REPLAY_MISSING {label}"
