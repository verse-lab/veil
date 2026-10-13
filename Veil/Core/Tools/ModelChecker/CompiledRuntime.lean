module

public import Veil.Core.Tools.ModelChecker.Concrete.Progress

public section

namespace Veil.ModelChecker.Compilation

open Lean

/-- Launch-time arguments, separated from the positional parallel settings. None of these is part
of the generated program, so none of them changes its cache key: one build serves every way of
launching it. -/
private structure LaunchArgs where
  /-- What is left for the positional parallel configuration, in order. -/
  positional : List String := []
  /-- Checkpoint handed over from an interpreted run, via `--handoff-state`. -/
  handoffState : Option Json := none
  /-- The single liveness property to check, via `--property`. `none` checks all of them. -/
  property : Option String := none

/-- Strip the launch-time flags, keeping the positional arguments in order.

A flag has to be *removed*, not merely recognised: whatever is left is parsed positionally as the
parallel configuration, so a flag left in place would be read as a worker count. -/
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
  /-- Report on stderr and exit non-zero.

  The explicit exit is the point: letting `main` unwind does **not** end this process, because the
  `exitWhenParentDies` task is still blocked reading stdin and a parent that holds the pipe open
  never releases it. An error would then hang until the parent's own timeout fired instead of
  reporting itself -- observed with a misspelled `--property`, which sat for the full budget. -/
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
