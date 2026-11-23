module

public import Veil

veil module PublicationWarnings
set_option veil.smt.trust true
type node
relation r : node → Bool
after_init { r N := false }
action early { pure () }
action quiet { pure () }
action keep { pure () }
action other { pure () }
invariant [excluded] r N ∨ ¬ r N
#gen_spec

#guard_msgs (drop info, drop warning) in
#check_action early

/--
warning: Published VC theorems using `sorryAx`
  PublicationWarnings.early_excluded
  PublicationWarnings.early_excluded_tr
-/
#guard_msgs in
#gen_theorems

#guard_msgs in
#gen_theorems

#guard_msgs (drop info, drop warning) in
#check_action quiet
#guard_msgs in
set_option warn.sorry false in
#gen_theorems

-- Request in reverse order. Publication groups only newly added declarations
-- whose proof uses the admitted witness, and reports them in deterministic name order.
#guard_msgs (drop info, drop warning) in
#check_action other
#guard_msgs (drop info, drop warning) in
#check_action keep
/--
warning: Published VC theorems using `sorryAx`
  PublicationWarnings.keep_excluded
  PublicationWarnings.keep_excluded_tr
  PublicationWarnings.other_excluded
  PublicationWarnings.other_excluded_tr
-/
#guard_msgs in
end PublicationWarnings

run_meta do
  for name in [``PublicationWarnings.early_excluded, ``PublicationWarnings.quiet_excluded,
      ``PublicationWarnings.keep_excluded, ``PublicationWarnings.other_excluded] do
    unless (← Lean.collectAxioms name).contains ``sorryAx do
      throwError "expected an admitted witness for {name}"
  if (← Lean.collectAxioms ``PublicationWarnings.keep_doesNotThrow).contains ``sorryAx then
    throwError "unexpected admitted witness"

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem outsidePublication : True := by sorry
