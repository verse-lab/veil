import Veil

open Veil.ModelChecker.Compilation

#eval do
  let sourceFile := "/tmp/compilation-registry-key.lean"
  let modelCheckCommand : CompiledCommandSpec := {
    exportedName := "modelCheckerResult"
    supportsParallelConfig := true
  }
  let simulateCommand : CompiledCommandSpec := {
    exportedName := "simulateResult"
  }
  let modelCheckFolderA ← generateBuildFolderName sourceFile modelCheckCommand "model-check-a"
  let modelCheckFolderB ← generateBuildFolderName sourceFile modelCheckCommand "model-check-b"
  let simulateFolderA ← generateBuildFolderName sourceFile simulateCommand "simulate-a"
  assert! (toString modelCheckFolderA == toString modelCheckFolderB)
  assert! (toString modelCheckFolderA != toString simulateFolderA)
  let modelCheckBuildDirA := System.FilePath.mk "build/model-check-a"
  let modelCheckBuildDirB := System.FilePath.mk "build/model-check-b"
  let simulateBuildDirA := System.FilePath.mk "build/simulate-a"
  let simulateBuildDirB := System.FilePath.mk "build/simulate-b"
  let simulateBuildDirC := System.FilePath.mk "build/simulate-c"
  markRegistryInProgress sourceFile modelCheckCommand "model-check-a" 1 modelCheckBuildDirA
  markRegistryInProgress sourceFile modelCheckCommand "model-check-b" 2 modelCheckBuildDirB
  markRegistryInProgress sourceFile simulateCommand "simulate-a" 3 simulateBuildDirA
  markRegistryInProgress sourceFile simulateCommand "simulate-b" 4 simulateBuildDirB
  markRegistryInProgress sourceFile simulateCommand "simulate-c" 5 simulateBuildDirC
  assert! (← stillCurrentCont sourceFile modelCheckCommand "model-check-a" 1 (pure ()))
  assert! (← stillCurrentCont sourceFile modelCheckCommand "model-check-b" 2 (pure ()))
  assert! (← stillCurrentCont sourceFile simulateCommand "simulate-a" 3 (pure ()))
  assert! (← stillCurrentCont sourceFile simulateCommand "simulate-b" 4 (pure ()))
  assert! (← stillCurrentCont sourceFile simulateCommand "simulate-c" 5 (pure ()))
  markRegistryFinished sourceFile modelCheckCommand "model-check-a" modelCheckBuildDirA
  markRegistryFinished sourceFile modelCheckCommand "model-check-b" modelCheckBuildDirB
  markRegistryFinished sourceFile simulateCommand "simulate-a" simulateBuildDirA
  markRegistryFinished sourceFile simulateCommand "simulate-b" simulateBuildDirB
  markRegistryFinished sourceFile simulateCommand "simulate-c" simulateBuildDirC
