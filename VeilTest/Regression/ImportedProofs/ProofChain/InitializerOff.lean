module

public import VeilTest.Regression.ImportedProofs.ProofChain.InitializerDoesNotThrow

veil module NodeProofs
prove_veil_invariant_goal initializer off using tr by
  grind
end NodeProofs
