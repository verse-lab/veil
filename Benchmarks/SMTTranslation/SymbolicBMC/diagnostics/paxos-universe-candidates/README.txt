Standalone translation diagnostics and trusted-only candidates

See the root PAXOS_UNIVERSE_FINDINGS.txt, SMT_PARSER_FINDINGS.txt,
TRANSITION_FORM_FINDINGS.txt and DIAGNOSTICS_README.txt for final findings.
UniverseDependencyProbe confirms lost universe levels. Production/observer probes
confirm PaxosEPR's residual decide and ReliableBroadcast's residual transition
wrapper. Direct decide lowering gives trusted UNSAT at depth1 for PaxosEPR,
ChordRingMaintenance and SuzukiKasami, but does not fix ReliableBroadcast.
The minimal transition-form self-loop fails where its imperative equivalent
reaches UNSAT. No transition-bridge repair is implemented here.

These are the actual self-contained sources used in the hashed execution records.
Observer files use persistent query tracing; the original headerless observer
include retains its preparation version. Source comments saying prepared/not run
record preparation history, not final execution status. The trusted successes
warn that the declaration uses sorry; they do not establish kernel reconstruction
or SAT model decoding. None of these candidates is in implementation.patch.

Launch from a matching checkout with its native plugin:
  lake env lean -D Elab.async=false --plugin=.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so PROBE.lean
These functional whole-process times are not benchmark samples.
