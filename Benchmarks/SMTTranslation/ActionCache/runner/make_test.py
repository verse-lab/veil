from pathlib import Path
r=Path('/home/george/src/veil-issue-123');s=(r/'VeilTest/Regression/TraceLocalNormalization.lean').read_text()
s=s.replace('public section','public section\nset_option veil.experimental.bmcCache true')
s=s.replace('section LogicalScopes','namespace CacheLogicalScopes').replace('end LogicalScopes','end CacheLogicalScopes')
s=s.replace("'shadowed_constraints' depends", "'CacheLogicalScopes.shadowed_constraints' depends")
s=s.replace('TraceLocalNormalization','TraceCachedNormalization')
s=s.replace('/-! Semantic regressions for per-transition normalization.', '/-! Semantic regressions for exact cached transition normalization.')
s=s.replace('#gen_spec\n\nsection TrustedChecks', '''#gen_spec

-- Inspect the actual cache artifacts, not just a successful solver result.
#guard_msgs (drop info) in
#print axioms __bmc_any_eq
#guard_msgs (drop info) in
#print axioms __bmc_action.fill.eq

section TrustedChecks''')
(r/'VeilTest/Regression/TraceCachedNormalization.lean').write_text(s)
