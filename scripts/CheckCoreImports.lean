import Lean
import Lean.Util.FoldConsts

open Lean

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Veil.Core }] {}
  let forbidden := #[`Smt, `cvc5, `Auto, `Veil.Backend.SMT,
    `Veil.Core.Tools.Verifier, `Veil.Core.UI.Verifier,
    `Veil.Frontend.DSL.Module.VCGen, `Veil.Frontend.DSL.Infra.Metadata,
    `Veil.Core.Tools.ModelChecker.Symbolic.TraceLang,
    `Veil.Frontend.DSL.Module.Elaborators.Verification]
  for n in env.header.moduleNames do
    if forbidden.any (·.isPrefixOf n) then
      throw <| IO.userError s!"Veil.Core imports verification module {n}"
  for n in #[`Veil.fullVerificationSupport, `Veil.vcManagerCh,
      `Veil.Verifier.vcManager, `Veil.vcServerStarted] do
    if env.contains n then throw <| IO.userError s!"Veil.Core contains verifier state {n}"
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if (`Veil).isPrefixOf env.header.moduleNames[idx.toNat]! then
        if info.getUsedConstantsAsSet.contains `sorryAx then
          throw <| IO.userError s!"unfinished Core declaration: {name}"
  IO.println s!"Veil.Core: {env.header.moduleNames.size} imported modules; no SMT, CVC5, VC generation, or verifier state."
