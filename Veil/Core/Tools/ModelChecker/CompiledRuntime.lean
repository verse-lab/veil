module

public import Veil.Core.Tools.ModelChecker.Concrete.Progress

public section

namespace Veil.ModelChecker.Compilation

open Lean

/-- Entry point shared by the generated model checker executables. `check` runs the model check and
passes the result to its last argument. -/
def runMain (check : Option ModelChecker.ParallelConfig → Nat → IO.CancelToken → (Json → IO Unit) → IO Unit)
    (args : List String) : IO Unit := do
  let _ ← IO.asTask (prio := .dedicated) exitWhenParentDies
  -- Enable progress reporting to stderr for the IDE to read
  Veil.ModelChecker.Concrete.enableCompiledModeProgress
  let pcfg : Option Veil.ModelChecker.ParallelConfig :=
    match args with
    | a :: b :: args' =>
      let numSubSteps := args'.head?.bind String.toNat? |>.getD 1
      match a.toNat?, b.toNat? with
      | some numSubTasks, some thresholdToParallel => some { numSubTasks, thresholdToParallel, numSubSteps : Veil.ModelChecker.ParallelConfig }
      | _, _ => none
    | _ => none
  -- Instance ID is not used in compiled mode, pass 0
  -- Cancel token is created locally; cancellation is handled by killing the process from outside
  let cancelTk ← IO.CancelToken.new
  -- Exit from inside `check`, while it still holds the search's data structures: the OS then
  -- reclaims them at once, instead of the runtime freeing them object by object first.
  check pcfg 0 cancelTk fun res => do
    IO.println s!"{res}"
    flushStdoutAndStderr
    IO.Process.forceExit 0
  throw <| IO.userError "the model check finished without reporting a result"
where
  flushStdoutAndStderr : IO Unit := do
    let stdout ← IO.getStdout
    let stderr ← IO.getStderr
    stdout.flush
    stderr.flush
  exitWhenParentDies : IO Unit := do
    let stdin ← IO.getStdin
    let _ ← stdin.readToEnd
    flushStdoutAndStderr
    IO.Process.forceExit 2


end Veil.ModelChecker.Compilation
