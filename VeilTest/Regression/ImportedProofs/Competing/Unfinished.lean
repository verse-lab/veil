module

public import VeilTest.Regression.ImportedProofs.Spec

veil module NodeProofs
/-- warning: declaration uses `sorry` -/
#guard_msgs in
prove_veil_invariant_goal keep off using wp by
  sorry
end NodeProofs

veil module FlagProofs
namespace Zulu
@[veil] theorem keep_off : True := True.intro
end Zulu

-- Only the copy in Completed carries the attribute.
namespace Shared
theorem keep_off : True := True.intro
end Shared
end FlagProofs
