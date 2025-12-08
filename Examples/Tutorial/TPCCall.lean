import Examples.Tutorial.TPC

-- #time
-- run_elab do
--   let a := TwoPhaseCommit.modelCheckerResult.seen.size
--   Lean.logInfo m!"Number of states explored in TwoPhaseCommit: {a}"

def main : IO Unit := do
  let a := spaceSize TwoPhaseCommit.modelCheckerResult
  IO.println s!"Number of states explored in TwoPhaseCommit: {a}"
