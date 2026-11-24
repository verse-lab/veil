module

public import VeilTest.Regression.ImportedProofs.ProofChain.KeepOff
meta import VeilTest.Regression.ImportedProofs.ProofChain.KeepOff

veil module NodeProofs
-- Check all four registrations before any automatic dischargers can run.
run_cmd ImportedProofChain.checkProofs [
  `initializer_doesNotThrow, `initializer_off_tr, `keep_doesNotThrow, `keep_off]
#check_invariants
end NodeProofs
