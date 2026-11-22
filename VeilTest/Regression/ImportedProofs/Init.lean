module

public import VeilTest.Regression.ImportedProofs.Spec

veil module NodeProofs
prove_veil_invariant_goal initializer off using tr by
  grind
end NodeProofs

veil module FlagProofs
prove_veil_invariant_goal initializer off using tr by
  grind
end FlagProofs
