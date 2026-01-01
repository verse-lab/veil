-- import ToBeImportedByModelCheckerMain
-- import Lean
import Veil

/-!
This file is dedicated to compiling and executing the model checker.
The workflow is as follows:

- The user writes a Veil model and runs `#gen_spec` to trigger compilation.
- `#gen_spec` copies the source with `internal_mode` to `ToBeImportedByModelCheckerMain.lean`,
  which provides the `modelCheckerCall` function.
- This file is then compiled into an executable.
- When `#model_check` is called, it sends the instantiation, theory, and config to this binary.
- The binary parses the input, evaluates `modelCheckerCall`, and returns the result.
-/

set_option maxHeartbeats 6400000

-- The following code is inspired by `https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Trouble.20parsing.20Lean.20code.20from.20string/`

open Lean Meta Elab Term in
/-- Parse and evaluate a model checker call expression. -/
unsafe def parseAndEvalModelCheckerCall (code : String) : IO Json := do
  -- Run elaboration and evaluation
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let imports := #[`Lean, `ToBeImportedByModelCheckerMain]
  let env ← importModules (imports.map (Import.mk · false true false)) Options.empty
    -- Not sure about this ...
    (leakEnv := true)
    -- Required for elaboration
    (loadExts := true)
  let (ioResult, _) ← Core.CoreM.toIO (ctx := { fileName := "<CoreM>", fileMap := default }) (s := { env := env }) do
    -- Parse the code as a term
    let .ok stx := Parser.runParserCategory (← getEnv) `term code "<stdin>"
      | return none
    -- IO.println s!"Parsed syntax: {stx}"
    MetaM.run' do
      TermElabM.run' do
        let stx ← `($(mkIdent ``Functor.map) $(mkIdent ``Lean.toJson) ($(TSyntax.mk stx)))
        let ty := mkApp (mkConst ``IO) (mkConst ``Json)
        let tm ← elabTerm stx ty
        synthesizeSyntheticMVarsNoPostponing
        let tm ← instantiateMVars tm
        -- IO.println s!"{tm}"
        let res ← evalExpr (IO Json) ty tm
        return some res

  -- Run the IO computation to get the actual result
  let some ioResult := ioResult | throw (IO.userError s!"Failed to parse input")
  ioResult

def main : IO Unit := do
  -- Enable progress reporting to stderr for the IDE to read
  Veil.ModelChecker.Concrete.enableCompiledModeProgress

  -- Read the model checker call expression from stdin
  let stdin ← IO.getStdin
  let code ← stdin.readToEnd

  -- Parse and evaluate the model checker call
  let result ← unsafe parseAndEvalModelCheckerCall code

  -- Output the result as JSON
  IO.println s!"{result}"
