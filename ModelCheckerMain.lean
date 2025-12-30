import ToBeImportedByModelCheckerMain

/-!
This file is dedicated to compiling and executing the model checker.
The workflow is as follows:

- The user writes a Veil model and enables the compilation-based
  model checker execution strategy by specifying `after_compilation`.
- The user's Veil model is then slightly modified and copied into a
  temporary file (currently `ToBeImportedByModelCheckerMain.lean`),
  which provides some definitions used by this file (currently
  `modelCheckerResult`).
- Finally, this file is compiled into an executable.
-/

set_option maxHeartbeats 6400000

def main (args : List String) : IO Unit := do
  -- Enable progress reporting to stderr for the IDE to read
  Veil.ModelChecker.Concrete.enableCompiledModeProgress
  let pcfg : Option Veil.ModelChecker.ParallelConfig :=
    match args with
    | [a, b] =>
      match a.toNat?, b.toNat? with
      | some n1, some n2 => some <| Veil.ModelChecker.ParallelConfig.mk n1 n2
      | _, _ => none
    | _ => none
  -- Instance ID is not used in compiled mode, pass 0
  let res ← modelCheckerResult pcfg 0
  IO.println s!"{Lean.toJson res}"
