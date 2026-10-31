module
meta import all Veil.Frontend.DSL.Module.Elaborators.Verification
meta import all Veil.Core.UI.Verifier.VerificationResults
meta import Batteries.Tactic.OpenPrivate

open Lean Elab Command Veil Veil.Verifier
meta section
open private Veil.addUndischargedTheoremSuggestion from Veil.Frontend.DSL.Module.Elaborators.Verification
open private Veil.Verifier.getTheoremInsertInfo from Veil.Core.UI.Verifier.VerificationResults

private partial def edits : InfoTree → Array Lsp.TextEdit
  | .context _ tree => edits tree
  | .node (.ofCustomInfo info) children =>
      (match info.value.get? Meta.Tactic.TryThis.TryThisInfo with
       | some info => #[info.edit]
       | none => #[]) ++ children.toArray.flatMap edits
  | .node _ children => children.toArray.flatMap edits
  | .hole _ => #[]

private partial def checkSyntax (stx : Syntax) : Option Syntax :=
  if stx.getKind == ``Lean.Parser.Command.check then some stx
  else stx.getArgs.findSome? checkSyntax

private def checkCase (source : String) (expectedLine : Nat) : CommandElabM Unit := do
  let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `command source
  let some checkStx := checkSyntax stx | throwError "test has no #check"
  let theoremText := "@[veil]\ntheorem insertedProof : True := by\n  trivial"
  let results : VerificationResults VCMetadata SmtResult := {
    (default : VerificationResults VCMetadata SmtResult) with
    vcs := #[{ (default : VCResult VCMetadata SmtResult) with
      id := 0, name := `insertedProof, status := some .unknown,
      metadata := .induction { (default : InductionVCMetadata) with property := `insertedProof },
      theoremText := some theoremText }]
  }
  withReader (fun ctx => { ctx with
    fileMap := source.toFileMap
    fileName := "test.lean"
    cmdPos := stx.getPos?.getD 0 }) do
    let (widgetPos, _) ← getTheoremInsertInfo
    unless widgetPos == { line := expectedLine, character := 0 } do
      throwError "widget inserts at {repr widgetPos}, expected line {expectedLine} before outer command"
    let saved ← get
    setInfoState { enabled := true }
    addUndischargedTheoremSuggestion checkStx results
    let generated := (← getInfoState).trees.toArray.flatMap edits
    set saved
    let #[edit] := generated | throwError "expected exactly one actual TryThis code-action edit"
    -- Apply the production edit, checking the complete resulting source. The
    -- outer command's options, indentation, comments, and multiline body survive.
    let map := source.toFileMap
    let start := map.lspPosToUtf8Pos edit.range.start
    let stop := map.lspPosToUtf8Pos edit.range.end
    let actual := String.Pos.Raw.extract source 0 start ++ edit.newText ++
      String.Pos.Raw.extract source stop source.rawEndPos
    let originalStart := map.lineStart (expectedLine + 1)
    let expected := String.Pos.Raw.extract source 0 originalStart ++ theoremText ++ "\n\n" ++
      String.Pos.Raw.extract source originalStart source.rawEndPos
    unless actual == expected do
      throwError "TryThis altered or misplaced the triggering command:\n{actual}"

run_cmd do
  checkCase "#check Nat" 0
  checkCase "-- α 😀\n\n  #check\n    (Nat) -- tail\n" 2
  checkCase "-- 😀\r\n  #check\r\n    (Nat)\r\n" 1
  checkCase "\n\n  #check\n    (Nat)" 2
  checkCase "\nset_option pp.universes true in\n  #check\n    (Nat)" 1
  checkCase "\n#guard_msgs in\n  #check Nat" 1
  checkCase "set_option pp.universes true in #check Nat" 0
  IO.println "stub insertion before ordinary, indented, multiline, and wrapped commands: PASS"
