import Lean
import Lean.Util.FoldConsts

/-! Audit compiled imports after `lake build Veil`. -/
open Lean

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Veil }] {}
  let forbidden := env.header.moduleNames.filter fun n =>
    (`Mathlib).isPrefixOf n || (`LoomMathlib).isPrefixOf n
  unless forbidden.isEmpty do
    throw <| IO.userError s!"Veil imports mathlib modules: {forbidden}"
  let mut checked := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if (`Veil).isPrefixOf env.header.moduleNames[idx.toNat]! then
        checked := checked + 1
        if info.getUsedConstantsAsSet.contains `sorryAx then
          throw <| IO.userError s!"unfinished Veil declaration: {name}"
  IO.println s!"Checked {checked} Veil declarations: no mathlib imports or unfinished proofs."
