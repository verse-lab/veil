import Veil

set_option veil.printCounterexamples false

veil module InvSetDefaultSupport

individual p : Bool
individual q : Bool

#gen_state

after_init {
  p := true
  q := true
}

action copy_p {
  q := p
}

invset Base {
  invariant [p_true] p
}

invset NeedsBase {
  invariant [q_true] q
}

#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  p_true ... ✅
  q_true ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  copy_p
    doesNotThrow ... ✅
    p_true ... ✅
    q_true ... ✅
-/
#guard_msgs in
#check_invariants

run_cmd do
  let mgr ← Veil.Verifier.vcManager.atomically fun ref => ref.get
  let mut foundRestrictedQTrue := false
  for (_, vc) in mgr.nodes.toArray do
    match vc.metadata with
    | .induction m =>
      if m.action == `copy_p && m.property == `q_true && m.style == .wp then
        for discharger in vc.dischargers do
          if let some term := discharger.term then
            if (toString term.raw).contains "veil_enforce_invset_support" then
              foundRestrictedQTrue := true
    | .trace _ => pure ()
  unless foundRestrictedQTrue do
    throwError "expected default #check_invariants to attach an invset-restricted discharger for q_true"

end InvSetDefaultSupport

veil module GenTheoremsOmitUncheckedInvSet

individual p : Bool
individual q : Bool

#gen_state

after_init {
  p := true
  q := true
}

action copy_p {
  q := p
}

invset Base {
  invariant [p_true] p
}

invset Unchecked {
  invariant [q_true] q
}

#gen_spec

#check_invariants Base

#gen_theorems

run_cmd do
  let env ← Lean.getEnv
  for decl in #[
    `GenTheoremsOmitUncheckedInvSet.copy_p_p_true,
    `GenTheoremsOmitUncheckedInvSet.copy_p_p_true_tr
  ] do
    unless env.contains decl do
      throwError "expected checked invset theorem declaration `{decl}`"
  for decl in #[
    `GenTheoremsOmitUncheckedInvSet.copy_p_q_true,
    `GenTheoremsOmitUncheckedInvSet.copy_p_q_true_tr
  ] do
    if env.contains decl then
      throwError "did not expect unchecked invset theorem declaration `{decl}`"

end GenTheoremsOmitUncheckedInvSet
