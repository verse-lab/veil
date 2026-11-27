module

public import Veil

veil module PublicationWarnings
-- Exercise publication of admitted SMT witnesses.
set_option veil.frame false
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

veil module IndependentWitness
set_option veil.smt.trust false
individual flag : Bool
after_init { flag := false }
action keep { flag := false }
invariant [off] ¬ flag
#gen_spec
namespace Finished
prove_veil_invariant_goal keep off using wp by
  done
end Finished

-- The canonical name is occupied, but the check has an independent completed proof.
set_option warn.sorry false in
theorem keep_off : type_of% @Finished.keep_off := by sorry
#check_action keep
#guard_msgs in
end IndependentWitness

run_meta do
  unless (← Lean.collectAxioms ``IndependentWitness.keep_off).contains ``sorryAx do
    throwError "expected the existing canonical proof to depend on sorryAx"
  for name in [``IndependentWitness.Finished.keep_off, ``IndependentWitness.keep_off_tr] do
    if (← Lean.collectAxioms name).contains ``sorryAx then
      throwError "{name} depends on the unfinished proof"
