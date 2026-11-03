module
meta import VeilTest.Regression.VerifierGenerationSupport
meta import all Veil.Core.Tools.Verifier.Server
meta import Batteries.Tactic.OpenPrivate
open Lean Elab Command Veil Veil.Verifier VeilTest.VerifierGeneration
meta section

-- Frontend requests now execute atomically, so an inline channel continuation
-- cannot safely interpose during applyFrontendRequest. Exercise the exact production request
-- and waiter across an explicit prelaunch replacement boundary instead.
open private Veil.Verifier.requestFiltered Veil.Verifier.awaitFilteredWithLogging
  in Veil.Verifier.runFilteredAsyncWithManagerId in
run_cmd do
  runManager
  let _ ← fresh #[`original]
  let captured ← requestFiltered (fun _ => true)
  let _ ← fresh #[`replacement] true
  let calls ← IO.mkRef 0
  let tk ← IO.CancelToken.new
  let wrapped ← Command.wrapAsyncAsSnapshot (fun () => do
    try
      discard <| awaitFilteredWithLogging captured (fun _ => true)
      calls.modify (· + 1)
    catch _ => pure ()) tk
  let task ← (wrapped ()).asTask (prio := .dedicated)
  try
    await "prelaunch stale waiter exits" (IO.hasFinished task)
    check ((← calls.get) == 0) "waiter adopted replacement before first poll"
  finally
    tk.set
    await "capture cleanup" (IO.hasFinished task)
  IO.println "production request captures generation before waiter launch: PASS"
