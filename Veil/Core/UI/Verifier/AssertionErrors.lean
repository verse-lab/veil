module

public meta import Veil.Frontend.DSL.Module.AssertionInfo
public meta import Veil.Core.Tools.Verifier.Results
public meta import Veil.Core.UI.Verifier.VerificationResults

public meta section

open Lean Elab Command
namespace Veil

/-- Warn at each assertion that a `doesNotThrow` counterexample identifies. -/
def logDoesNotThrowWarnings (results : VerificationResults VCMetadata SmtResult) : CommandElabM Unit := do
  let actx := (← globalEnv.get).assertions
  for vc in results.vcs do
    let .induction m := vc.metadata | continue  -- Only induction VCs have doesNotThrow
    unless m.isAssertionCheck do continue
    for d in vc.timing.dischargers do
      let .some (.disproven (.some (.sat ces)) _) := d.result | continue
      for ce in ces.filterMap id do
        let .ok extraVals := ce.structuredJson.getObjVal? "extraVals" | continue
        let .ok exVal := extraVals.getObjVal? "__veil_ex" | continue
        let .ok exId := exVal.getInt? | continue
        let .some a := actx.find[exId]?
          | throwError s!"Assertion {exId} not found (from {m.action})"; continue
        if m.action == `initializer then
          logWarningAt a.ctx.stx "This assertion can fail during initialization."
        else
          logWarningAt a.ctx.stx m!"This assertion can fail even if the module's invariants hold when `{m.action}` starts."

end Veil
