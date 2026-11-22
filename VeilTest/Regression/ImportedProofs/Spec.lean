module

public import Veil

veil module NodeProofs
set_option veil.deferVCGeneration true
type node
relation flag : node → Bool
after_init { flag N := false }
action keep (n : node) { require ¬ flag n }
invariant [off] ¬ flag N
#gen_spec
end NodeProofs

-- The source file can reopen the same spec and extract its executable once.
veil module NodeProofs
#gen_executable
end NodeProofs

veil module FlagProofs
individual flag : Bool
after_init { flag := false }
action keep { flag := false }
invariant [off] flag = false
temporal (only := check) [offBefore] □ ⌜ ¬ flag ⌝
temporal [selfImplied] ⌜ ¬ flag ⌝ → ⌜ ¬ flag ⌝
#gen_spec
/-- error: The specification of module FlagProofs has already been finalized. You can no longer add procedures or assertions! -/
#guard_msgs in
invariant [lateInline] False

run_cmd do
  let mod ← Veil.getCurrentModule
  unless mod.checkableTemporalProperties.map (·.name) == #[`offBefore, `selfImplied] &&
      mod.checkableInvariants.map (·.name) == #[`off] do
    throwError "unexpected properties in the defining file"
end FlagProofs
