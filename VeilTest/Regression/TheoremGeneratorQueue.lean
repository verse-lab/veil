module

public import Veil

veil module GeneratorQueue
individual flag : Bool
after_init { flag := false }
action keep { flag := false }
invariant [off] flag = false
#gen_spec

open Lean Elab Command in
run_cmd do
  let enqueue := Veil.registerTheoremGenerator `GeneratorQueue
  enqueue (Lean.logInfo "prefix")
  enqueue do
    unless (← Lean.getEnv).contains `GeneratorQueue.ready do
      enqueue (Lean.logInfo "child from failed attempt")
      throwError "waiting for ready"
    unless (← Lean.getEnv).contains `GeneratorQueue.syntaxReady do
      throwUnsupportedSyntax
    unless (← Lean.getEnv).contains `GeneratorQueue.abortReady do
      throwAbortCommand
    Lean.logInfo "retried"
    elabCommand (← `(command| #gen_theorems))
    enqueue (Lean.logInfo "child")
  enqueue (Lean.logInfo "tail")

/--
info: prefix
---
error: waiting for ready
-/
#guard_msgs in
#gen_theorems

-- An unsuccessful close keeps the scope open and the FIFO available for retry.
/-- error: waiting for ready -/
#guard_msgs in
end GeneratorQueue

theorem ready : True := True.intro

/-- error: a theorem generator for `GeneratorQueue` encountered unsupported syntax -/
#guard_msgs in
end GeneratorQueue

theorem syntaxReady : True := True.intro

/-- error: a theorem generator for `GeneratorQueue` aborted publication -/
#guard_msgs in
end GeneratorQueue

theorem abortReady : True := True.intro

-- The successful prefix stays committed. The failed attempt's child is rolled
-- back. The child from the retry goes behind the already registered tail.
/--
info: retried
---
info: tail
---
info: child
-/
#guard_msgs in
end GeneratorQueue
