module

public import Veil
meta import Lean

/-! The commands that show a widget while their work runs publish it with `Veil.withStreamingInfo`,
which needs their elaborators to be `@[incremental]`. `scripts/tests/test-streaming-widgets.py`
checks the rest through the language server, with elaborators of its own in front of these. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  -- The trace commands have no named syntax kind
  let traceKind ← match Parser.runParserCategory env `command "sat trace { }" with
    | .ok stx => pure stx.getKind
    | .error e => throwError e
  for kind in [``Veil.modelCheck, ``Veil.simulate, ``Veil.livenessCheck, ``Veil.checkInvariants,
      ``Veil.checkAction, ``Veil.Synthesizer.updr, traceKind] do
    let elabs := commandElabAttribute.getEntries env kind
    if elabs.isEmpty then throwError "no elaborator for `{kind}`"
    for e in elabs do
      unless ← isIncrementalElab e.declName do
        throwError "`{e.declName}`, the elaborator of `{kind}`, is not `@[incremental]`"
