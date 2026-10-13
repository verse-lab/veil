module

public import Veil.Core.Tools.ModelChecker.Concrete.Progress

public section

namespace Veil.ModelChecker.Compilation

open Lean

/-- Command-line arguments of a compiled binary. -/
private structure LaunchArgs where
  /-- The positional parallel settings. -/
  positional : List String := []
  /-- `--handoff-state`: checkpoint from an interpreted run. -/
  handoffState : Option Json := none
  /-- `--property`: the liveness property to check; `none` checks all of them. -/
  property : Option String := none

/-- Parse `--handoff-state` and `--property`, keeping the other arguments in order. -/
private def parseLaunchArgs : List String → Except String LaunchArgs
  | [] => pure {}
  | ["--handoff-state"] => throw "expected one JSON argument after --handoff-state"
  | "--handoff-state" :: state :: rest => do
    let args ← parseLaunchArgs rest
    if args.handoffState.isSome then throw "--handoff-state was given twice"
    return { args with handoffState := some (← Json.parse state) }
  | ["--property"] => throw "expected a property name after --property"
  | "--property" :: name :: rest => do
    let args ← parseLaunchArgs rest
    if args.property.isSome then throw "--property was given twice"
    return { args with property := some name }
  | arg :: rest => do
    let args ← parseLaunchArgs rest
    return { args with positional := arg :: args.positional }

/-- Entry point shared by the generated model checker executables. `check` runs the model check and
passes the result to its last argument. -/
def runMain (check : Option ModelChecker.ParallelConfig → Nat → IO.CancelToken → (Json → IO Unit) → IO Unit)
    (args : List String) : IO Unit := do
  let launch ← IO.ofExcept (parseLaunchArgs args)
  let args := launch.positional
  let _ ← IO.asTask (prio := .dedicated) exitWhenParentDies
  -- Enable progress reporting to stderr for the IDE to read
  Veil.ModelChecker.Concrete.enableCompiledModeProgress launch.handoffState launch.property
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
  try
    check pcfg 0 cancelTk fun res => do
      IO.println s!"{res}"
      flushStdoutAndStderr
      IO.Process.forceExit 0
    die "the model check finished without reporting a result"
  catch e =>
    die (toString e)
where
  /-- Print `msg` to stderr and exit with code 1. -/
  die (msg : String) : IO Unit := do
    let stderr ← IO.getStderr
    stderr.putStrLn s!"error: {msg}"
    flushStdoutAndStderr
    IO.Process.forceExit 1
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
