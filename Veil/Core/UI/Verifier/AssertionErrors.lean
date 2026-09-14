import Veil.Frontend.DSL.Module.AssertionInfo
import Veil.Core.Tools.Verifier.Results
import Veil.Core.UI.Verifier.VerificationResults

open Lean Elab Command
namespace Veil

/-- Log errors for assertions that might fail based on doesNotThrow verification results. -/
def logDoesNotThrowErrors (results : VerificationResults VCMetadata SmtResult) : CommandElabM Unit := do
  let actx := (← globalEnv.get).assertions
  for vc in results.vcs do
    let .induction m := vc.metadata | continue  -- Only induction VCs have doesNotThrow
    if m.property != `doesNotThrow then continue
    for d in vc.timing.dischargers do
      let .some (.disproven (.some (.sat ces)) _) := d.result | continue
      for ce in ces.filterMap id do
        let .ok extraVals := ce.structuredJson.getObjVal? "extraVals" | continue
        let .ok exVal := extraVals.getObjVal? "__veil_ex" | continue
        let .ok exId := exVal.getInt? | continue
        let .some a := actx.find[exId]?
          | throwError s!"Assertion {exId} not found (from {m.action})"; continue
        veilLogErrorAt a.ctx.stx s!"This assertion might fail when called from {m.action}"

end Veil
