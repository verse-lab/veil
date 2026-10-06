module

public import Veil

/-
Multi-module regression fixture for VC manager snapshot consistency.

Open this file, wait for elaboration, then insert `skip` before `done` in the
first module's proof. Currently, `@[veil]` cannot find the verification condition
`VCManagerMultiModuleFirst.keep_trivial`: Lean restores the first module's
environment, but the global manager still holds the second module's VCs.

Batch compilation alone cannot reproduce the edit. Run the LSP regression:
  python3 scripts/tests/test-invariant-goal-incrementality.py --multi-module
This mode is expected to fail until the manager's incremental state is fixed.
-/

veil module VCManagerMultiModuleFirst

after_init { pure () }
action keep { pure () }
invariant [trivial] True
#gen_spec

prove_veil_invariant_goal keep trivial using wp by
  done

end VCManagerMultiModuleFirst

veil module VCManagerMultiModuleSecond

after_init { pure () }
action other { pure () }
invariant [later] True
#gen_spec

end VCManagerMultiModuleSecond

-- The original theorem remains usable after switching modules.
example := @VCManagerMultiModuleFirst.keep_trivial
