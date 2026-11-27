module

public import VeilTest.Regression.ImportedProofs.Spec

veil module NodeProofs
#gen_spec
-- A theorem that shares a VC name still has to prove the generated statement.
@[veil] theorem keep_off : True := True.intro

/-- warning: declaration uses `sorry` -/
#guard_msgs in
prove_veil_invariant_goal initializer off using tr by
  sorry
end NodeProofs
