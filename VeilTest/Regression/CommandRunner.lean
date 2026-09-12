import Veil.Frontend.DSL.Module.Util.CommandRunner

/-! Exercise the actual shared drivers with controlled IO computations. Barriers
select the ordering; deadlines turn a lost handoff/result into a test failure. -/

open Lean Elab Command Veil.CommandRunner Veil.ModelChecker.Concrete
open Veil.ModelChecker.Compilation (BuildResult cancelledJson)

private def expect (message : String) (condition : Bool) : CommandElabM Unit :=
  unless condition do throwError message

private def awaitTask (task : Task α) : IO α := do
  let start ← IO.monoMsNow
  while !(← IO.hasFinished task) do
    if (← IO.monoMsNow) - start > 5000 then throw (IO.userError "runner test timed out")
    IO.sleep 1
  IO.wait task

private def awaitHandoff (id : Nat) : IO Unit := do
  let start ← IO.monoMsNow
  while !(← checkHandoffRequested id) do
    if (← IO.monoMsNow) - start > 5000 then throw (IO.userError "handoff was never requested")
    IO.sleep 1

private def awaitStop (token : IO.CancelToken) : IO Unit := do
  let start ← IO.monoMsNow
  while !(← token.isSet) do
    if (← IO.monoMsNow) - start > 5000 then throw (IO.userError "worker never observed cancellation")
    IO.sleep 1

private def verdict (traces : Nat) : Json := Json.mkObj [
  ("result", "no_violation_found"), ("traces_run", toJson traces), ("seed", toJson (7 : Nat))]

private def cancelled : Json := Json.mkObj [
  ("result", "cancelled"), ("traces_run", toJson (3 : Nat)), ("seed", toJson (7 : Nat))]

elab "test_command_runner " scenario:num : command => do
  let (id, token) ← allocProgressInstance (.simulation {})
  let ctx : Veil.CommandRunner.Context := { stx := ← getRef, instanceId := id, cancelToken := token, resultKind := .simulate }
  let nativeCalls ← IO.mkRef (0 : Nat)
  let started ← IO.Promise.new (α := Unit)
  let release ← IO.Promise.new (α := Unit)
  let binary : System.FilePath → IO Json := fun _ => do
    nativeCalls.modify (· + 1)
    if (← token.isSet) || (← checkHandoffRequested id) then
      throw (IO.userError "binary started with a cancelled token or pending handoff")
    return verdict 9
  let expectFinal (json : Json) : CommandElabM Unit := do
    expect "unexpected final result" ((← getResultJson id) == some json)
    expect "final result must stop progress" (!(← getProgress id).isRunning)
  match scenario.getNat with
  | 0 => -- Interpreted completes first; compilation still finishes, without a restart.
      let (interpreted, compiled) ← runWithHandoff ctx (pure (verdict 2))
        (do let _ ← awaitTask release.result!; return .built "unused") binary
      try
        let _ ← awaitTask interpreted
        expectFinal (verdict 2)
      finally
        release.resolve ()
      let _ ← awaitTask compiled
      expect "completed interpretation must not restart" ((← nativeCalls.get) == 0)
  | 1 | 2 | 4 | 5 | 8 =>
      let n := scenario.getNat
      let interpret : IO Json := do
        started.resolve ()
        awaitHandoff id
        if n == 4 then requestCancellation id
        return if n == 2 then verdict 2 else cancelled
      let run : System.FilePath → IO Json := fun path => do
        if n == 8 then throw (IO.userError "binary test failure")
        let result ← binary path
        if n == 5 then
          release.resolve ()
          awaitStop token
          return cancelledJson
        return result
      let (interpreted, compiled) ← runWithHandoff ctx interpret
        (do let _ ← awaitTask started.result!; return .built "unused") run
      if n == 5 then
        let _ ← awaitTask release.result!
        requestCancellation id
      let _ ← awaitTask compiled
      let _ ← awaitTask interpreted
      match n with
      | 1 => expectFinal (verdict 9)
      | 2 => expectFinal (verdict 2)
      | 4 => expectFinal cancelled
      | 5 => expectFinal cancelledJson
      | _ =>
          expect "binary exception must publish an error" (((← getResultJson id).getD .null).getObjValD "error" != .null)
          expect "binary exception must finish progress" (!(← getProgress id).isRunning)
          expect "binary exception is not a compilation failure" <|
            match (← getProgress id).compilationStatus with | .succeeded => true | _ => false
      if n == 2 || n == 4 then
        expect "handoff must not replace a verdict or ignore Stop" ((← nativeCalls.get) == 0)
      if n == 1 || n == 5 then
        expect "binary must run exactly once" ((← nativeCalls.get) == 1)
  | 3 => -- Both workers observe the same token when Stop interrupts compilation.
      let interpret : IO Json := do
        started.resolve ()
        awaitStop token
        return cancelled
      let (interpreted, compiled) ← runWithHandoff ctx interpret
        (do awaitStop token; return .interrupted) binary
      let _ ← awaitTask started.result!
      requestCancellation id
      let _ ← awaitTask interpreted
      let _ ← awaitTask compiled
      expectFinal cancelled
      expect "Stop during compilation must prevent binary execution" ((← nativeCalls.get) == 0)
  | 6 => -- Failed background compilation must leave interpreted execution alive.
      let (interpreted, compiled) ← runWithHandoff ctx
        (do let _ ← awaitTask release.result!; return verdict 2)
        (pure (.failed "background build failure")) binary
      try
        let _ ← awaitTask compiled
        expect "background failure must not publish a final result" ((← getResultJson id).isNone)
        expect "interpretation must remain running" (← getProgress id).isRunning
      finally
        release.resolve ()
      let _ ← awaitTask interpreted
      expectFinal (verdict 2)
  | 7 =>
      let task ← runCompiled ctx (pure (.failed "test compilation failure")) binary
      let _ ← awaitTask task
      expectFinal (Json.mkObj [("error", "test compilation failure")])
      expect "failed compilation must not execute a binary" ((← nativeCalls.get) == 0)
  | _ => throwError "unknown runner test"

#guard_msgs(drop info) in test_command_runner 0
#guard_msgs(drop info) in test_command_runner 1
#guard_msgs(drop info) in test_command_runner 2
#guard_msgs(drop info) in test_command_runner 3
#guard_msgs(drop info) in test_command_runner 4
#guard_msgs(drop info) in test_command_runner 5
#guard_msgs(drop info) in test_command_runner 6
/-- error: 💥 Error: test compilation failure -/
#guard_msgs in test_command_runner 7
/-- error: 💥 Error: binary test failure -/
#guard_msgs in test_command_runner 8
