module

public import Veil.Core.Tools.ModelChecker.Concrete.Progress

public section

namespace Veil

/-- The version of what the VS Code extension (`editors/vscode`) relies on: the code actions of
`ConfigTemplate.lean`, the `Model checker built: ` message, the arguments and output of model
checker binaries, and the syntax of the commands that it reads or writes (`veil module`,
`#mc_config`, `#model_check`, …). It equals `IDE_PROTOCOL` in `editors/vscode/src/compatibility.ts`;
`editors/vscode/PUBLISHING.md` says when to bump both. -/
def ideProtocolVersion : Nat := 1

end Veil

namespace Veil.ModelChecker.Compilation

open Lean

/-- What a model checker executable reports once, as `{"start": ...}` on the first line of stderr,
before any progress. -/
structure StartReport where
  /-- `ideProtocolVersion`, which saved results keep -/
  ideProtocol : Nat := ideProtocolVersion
  /-- The constructor names of the actions' displayed labels, without arguments, e.g. `send`. The
  progress counts only the actions that were taken, so these tell those never enabled. -/
  actionLabels : List String
  deriving ToJson, FromJson

/-- Entry point shared by the generated model checker executables. `check` runs the model check and
passes the result to its last argument. The executable reports a `StartReport` and then its
progress on stderr, a JSON object per line, and its result on stdout. -/
def runMain (actionLabels : List String)
    (check : Option ModelChecker.ParallelConfig → Nat → IO.CancelToken → (Json → IO Unit) → IO Unit)
    (args : List String) : IO Unit := do
  let _ ← IO.asTask (prio := .dedicated) exitWhenParentDies
  -- Enable progress reporting to stderr for the IDE to read, after what it needs to know once
  IO.eprintln (Json.mkObj [("start", toJson ({ actionLabels } : StartReport))]).compress
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
