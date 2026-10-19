Functional diagnostics after timed work

These are isolated reproductions and candidate experiments, not performance observations.
No production dependency source or .olean was edited. Only early introduction is shipped.
Trusted UNSAT probes legitimately warn that the declaration uses sorry; they do not claim
kernel proof reconstruction. Minimal simp checks verify expressions/equality proofs and
absence of escaped locals, but are not substitutes for a full untrusted regression suite.

AWSBuggyDependentOnly (exit 1; timeout=False)
  Candidate active/original disabled; advances to cannot translate 0; no solver answer.
AWSBuggyFixedNat (exit 1; timeout=False)
  Candidate active/original disabled; advances to cannot translate 0; no solver answer.
AWSBuggyWithDefaultOnly (exit 1; timeout=False)
  Candidate active/original disabled; original congruence mismatch remains.
ActionFormMinimal (exit 0; timeout=False)
  Equivalent imperative self-loop reaches trusted native UNSAT.
BuggyCircularBufferFixedNat (exit 1; timeout=False)
  Advances to unsupported lambda fun n => n in BUFFER_ELEMS; no solver answer.
BuggyCircularBufferOriginal (exit 1; timeout=False)
  Actual production tactic reproduces congruence mismatch at depth 1.
ChordRingMaintenanceProduction (exit 1; timeout=False)
  Actual production tactic reproduces native SMT parser error at depth 1.
ChordRingMaintenanceTranslateDecide (exit 0; timeout=False)
  Trusted native UNSAT at depth 1 after direct decide lowering.
MinimalDependentOnly (exit 0; timeout=False)
  All three checks pass; dependency handling resolves the minimized defect.
MinimalFixedNat (exit 0; timeout=False)
  All three expression/equality-proof and escaped-local checks pass.
MinimalOriginal (exit 1; timeout=False)
  Scalar control passes; both dependent Fin cases reproduce congruence type mismatch.
MinimalWithDefaultOnly (exit 1; timeout=False)
  Dependent cases still fail: transparency alone is insufficient.
PaxosEPRDiagnostic (exit 1; timeout=False)
  Persistent trace confirms residual decide and a valid incoming DecidableEq.{1}.
PaxosEPRProduction (exit 1; timeout=False)
  Actual production tactic reproduces DecidableEq universe-count error at depth 1.
PaxosEPRTranslateDecide (exit 0; timeout=False)
  Trusted native UNSAT at depth 1; candidate not validated for untrusted reconstruction.
ProductionAWSBuggy (exit 1; timeout=False)
  Actual production tactic reproduces congruence mismatch at depth 1.
ReliableBroadcastDiagnostic (exit 1; timeout=False)
  Persistent trace exposes enclosing byz.ext.toTransitionDerived wrapper.
ReliableBroadcastProduction (exit 1; timeout=False)
  Actual production tactic reproduces unsupported DecidableEq lambda at depth 1.
ReliableBroadcastTranslateDecide (exit 1; timeout=False)
  Same lambda failure remains; residual action wrapper is a distinct problem.
SuzukiKasamiProduction (exit 1; timeout=False)
  Actual production tactic reproduces native SMT parser error at depth 1.
SuzukiKasamiTranslateDecide (exit 0; timeout=False)
  Trusted native UNSAT at depth 1 after direct decide lowering.
TransitionFormMinimal (exit 1; timeout=False)
  Self-loop retains toTransitionDerived and fails on a field-representation lambda.
UniverseDependencyProbe (exit 0; timeout=False)
  Valid DecidableEq.{1} loses its universe levels through NameSet dependency reconstruction.

Unrun: AWSBuggyFixedNatRat and the optional Rat/Real helper. No Rat failure is claimed.
Candidate prototype fixes still need kernel-checked proof reconstruction, trusted SAT
model decoding, broader dependent-type coverage, and complete end-to-end regressions.

Probe preparation corrections: the first module-local simproc declaration lacked public
visibility; a later helper section restored the original simproc erasure on exit. Retained
full-model Nat probes erase the original outside that section and explicitly check both
original absence and candidate activation. Earlier invalid probes are excluded. The
observer uses persistent query tracing because ordinary logInfo can roll back on failure.
The minimal trace probe was corrected to avoid a reserved trace name and uses multiline
trace syntax. Only corrected execution records are included here.

Self-contained .lean files are the tested artifacts. Some source comments retain their
original preparation wording; this README and the hashed JSON execution records state
what actually ran. Headerless include files are design templates; use the complete tested
module files for reproduction, including visibility/scope and candidate-activation checks.

Launch from the recorded worktree (or matching checkout):
  lake env lean -D Elab.async=false --plugin=.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so PATH_TO_PROBE
Whole-process times in checkpoints include imports/setup/printing and must not be mixed
with stage benchmarks. The wrapper caps a functional probe at 90 seconds.
