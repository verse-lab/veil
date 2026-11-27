module

public import VeilTest.Regression.ImportedProofs.ScopeReplaySpec

veil module ImportedScopedNotation
-- The spec already enabled the scoped notation used by the action parameter.
prove_veil_invariant_goal keep off using wp by
  done
#check_invariants
end ImportedScopedNotation
