import Examples.Tutorial.KVSnap_opsUsingSet
open Std

-- #time
-- run_elab do
--   let a := TwoPhaseCommit.modelCheckerResult.seen.size
--   Lean.logInfo m!"Number of states explored in TwoPhaseCommit: {a}"
open Veil.ModelChecker


-- #time #eval! modelCheckerResult
def main : IO Unit := do
  let a := KVSnap.modelCheckerResult
  IO.println s!"Number of states explored in KVSnap: {repr a}"
