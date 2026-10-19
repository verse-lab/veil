Nat/Fin standalone repair experiments

The final results are in ../BACKEND_FINDINGS.txt, ../AWS_EMBEDDING_REPAIR_PLAN.txt
and ../DIAGNOSTICS_README.txt (or the corresponding root files in the package).
MinimalOriginal and WithDefaultOnly fail on dependent Fin cases; FixedNat and
DependentOnly pass expression/equality-proof and escaped-local checks. On the
complete AWS model, dependency-aware candidates remove the congruence error but
leave a later literal translation error. The circular-buffer candidate leaves
a later subtype-predicate lambda error. These are not complete backend fixes.

The tested full-model files contain public helper definitions and erase the
original simproc outside their helper section, with explicit activation checks.
Use these complete files for reproduction. Headerless include files retain the
initial design templates; source preparation comments do not override the actual
hashed execution records. Optional AWSBuggyFixedNatRat / FixedRat were NOT run.
No production dependency was edited. The candidate needs kernel reconstruction,
SAT model-decoding and broader regression coverage before shipping.

Run from a matching checkout with the recorded native cvc5 plugin:
  lake env lean -D Elab.async=false --plugin=.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so PROBE.lean
Keep diagnostic times separate from the primary benchmark.
