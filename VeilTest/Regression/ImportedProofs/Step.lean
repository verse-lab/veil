module

public import VeilTest.Regression.ImportedProofs.Spec

veil module NodeProofs
prove_veil_invariant_goal keep off using wp by
  grind
end NodeProofs

veil module FlagProofs
prove_veil_invariant_goal keep off using wp by
  done
end FlagProofs
