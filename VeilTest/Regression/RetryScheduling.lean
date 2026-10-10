import Veil

/-!
Regression test for retry-attempt scheduling (`veil.smt.retries`).

`VerificationCondition.nextDischarger?` must schedule a retry discharger
(`Discharger.attempt > 0`) if and only if an earlier attempt of the same VC
*timed out*. After `sat`/`unsat` results, genuine `unknown`s, or non-timeout
errors, retries must be skipped (permanently: the VC exhausts without them).
-/

open Lean Veil

private def mkTestDischarger (attempt : Nat) (result? : Option (DischargerResult Unit)) :
    BaseIO (Discharger Unit) := do
  let startTimePromise : IO.Promise Nat ← IO.Promise.new
  let resultPromise : IO.Promise (DischargerResult Unit) ← IO.Promise.new
  if let some res := result? then
    resultPromise.resolve res
  return {
    id := { managerId := 0, vcId := 0, dischargerId := attempt, name := `test }
    attempt := attempt
    cancelTk := ← IO.CancelToken.new
    task := none
    startTimePromise := startTimePromise
    resultPromise := resultPromise
    mkTask := pure (Task.pure default)
  }

private def mkTestVC (dischargers : Array (Discharger Unit)) :
    VerificationCondition Unit Unit :=
  { uid := 0, name := `testVC, params := #[], statement := ⟨.missing⟩,
    metadata := (), dischargers := dischargers, successful := none }

/-- Mirrors how solver timeouts surface in practice: an exception whose
message carries the solver's TIMEOUT marker (see `DischargerResult.isTimeout`). -/
private def timeoutResult : DischargerResult Unit :=
  .error #[(.error .missing m!"timed out", .str "unable to prove goal. Reason: TIMEOUT")] 100

private def incompleteResult : DischargerResult Unit :=
  .unknown (some ()) 100

private def nonTimeoutError : DischargerResult Unit :=
  .error #[(.error .missing m!"boom", .str "translation failure")] 100

private def disprovenResult : DischargerResult Unit :=
  .disproven (some ()) 100

/-- The attempt index `nextDischarger?` would schedule next for a VC whose
first attempt finished with `first` (if `some`) and that has one pending
retry discharger. -/
private def nextAttemptAfter (first : Option (DischargerResult Unit)) :
    IO (Option Nat) := do
  let d0 ← mkTestDischarger 0 first
  let d1 ← mkTestDischarger 1 none
  let vc := mkTestVC #[d0, d1]
  return (← vc.nextDischarger?).map (·.attempt)

-- Primary attempt not yet started: schedule it (not the retry).
/-- info: some 0 -/
#guard_msgs in #eval nextAttemptAfter none

-- Primary attempt timed out: schedule the retry.
/-- info: some 1 -/
#guard_msgs in #eval nextAttemptAfter (some timeoutResult)

-- Primary attempt was a genuine `unknown` (e.g. INCOMPLETE): skip the retry.
/-- info: none -/
#guard_msgs in #eval nextAttemptAfter (some incompleteResult)

-- Primary attempt failed with a non-timeout error: skip the retry.
/-- info: none -/
#guard_msgs in #eval nextAttemptAfter (some nonTimeoutError)

-- Primary attempt disproved the VC: no retry (the result is conclusive).
/-- info: none -/
#guard_msgs in #eval nextAttemptAfter (some disprovenResult)
