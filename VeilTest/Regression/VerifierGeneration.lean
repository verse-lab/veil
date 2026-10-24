module
meta import VeilTest.Regression.VerifierGenerationSupport
run_cmd VeilTest.VerifierGeneration.currentWaits
run_cmd VeilTest.VerifierGeneration.staleWait false 0
run_cmd VeilTest.VerifierGeneration.staleWait false 1
run_cmd VeilTest.VerifierGeneration.staleWait false 2
run_cmd VeilTest.VerifierGeneration.staleWait true 0
run_cmd VeilTest.VerifierGeneration.staleWait true 1
run_cmd VeilTest.VerifierGeneration.staleWait true 2
