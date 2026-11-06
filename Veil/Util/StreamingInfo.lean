module

public meta import Lean

public meta section

open Lean Elab Command

namespace Veil

/-- Run the command elaborator `act` for `stx`, and publish the info tree that it leaves, e.g. with a
progress widget, before the work it runs in snapshot tasks has finished.

Since Lean 4.34, the final info tree of a command waits for its asynchronous linters, which wait for
all of its snapshot tasks. A command that shows the progress of such a task in a widget therefore
publishes its info tree here, in its incremental snapshot, which the infoview searches for widgets
before the final info tree. The snapshot tasks move into the same snapshot, so they are reported once,
the linters still wait for them, and editing the command cancels them. Requests that read the final
info tree, such as hovers, go-to-definition and code actions, still wait for these tasks.

The command elaborator must be `@[incremental]`, or there is no snapshot to publish in and `act` runs
as is, as it does under `#guard_msgs` and on the command line. Call this after deciding to elaborate
`stx` (rather than throwing `throwUnsupportedSyntax`): it cancels the previous version of the command,
which it never reuses, and publishes even when `act` fails. `act` runs without the snapshot, so that
the commands it elaborates, e.g. generated declarations, do not resolve it. -/
def withStreamingInfo (stx : Syntax) (act : CommandElabM Unit) : CommandElabM Unit := do
  let some snap := (← read).snap? | act
  if let some old := snap.old? then old.val.cancelRec
  try
    withReader ({ · with snap? := none }) act
  finally
    let s ← get
    let scope := s.scopes.head!
    let ctx : CommandContextInfo := {
      env := s.env, cmdEnv? := some s.env, fileMap := ← getFileMap, mctx := {},
      currNamespace := scope.currNamespace, openDecls := scope.openDecls,
      options := scope.opts, ngen := s.ngen
    }
    let infoTask := (← getInfoState).substituteLazy.map (sync := true) fun info =>
      let tree := InfoTree.context (.commandCtx ctx)
        (.node (.ofCommandInfo { elaborator := decl_name%, stx }) info.trees)
      Language.SnapshotTree.mk { diagnostics := .empty, infoTree? := some tree } #[]
    -- The infoview shows the widget once it also has the goals at the cursor, which Lean looks for
    -- in the next snapshots, up to the final info tree, when the cursor is past the syntax of this
    -- one, e.g. at the end of the line of the command. So this one spans its trailing whitespace too.
    let infoStx := (stx.getRangeWithTrailing? (canonicalOnly := true)).map (Syntax.ofRange ·) |>.getD stx
    -- The tasks are moved rather than copied, so that their diagnostics are reported once. Lean
    -- reports them as being processed at the start of the command only, as it does the other
    -- background tasks of a command: the infoview fetches the info at the cursor again when the
    -- cursor leaves a range being processed, e.g. once the command has been elaborated again.
    let tasks := s.snapshotTasks
    modify ({ · with snapshotTasks := #[] })
    let background : Language.SnapshotTask Language.SnapshotTree := {
      stx? := none, cancelTk? := none, task := .pure (.mk { diagnostics := .empty } tasks)
      reportingRange := .ofOptionInheriting <| (stx.getPos? (canonicalOnly := true)).map fun pos => ⟨pos, pos⟩ }
    snap.new.resolve <| .ofTyped <| Language.SnapshotTree.mk { diagnostics := .empty }
      #[{ stx? := some infoStx, task := infoTask, cancelTk? := none }, background]

end Veil
