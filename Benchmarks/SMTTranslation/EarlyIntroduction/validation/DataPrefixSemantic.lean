module

public import Veil

/-!
Introducing trace binders before normalization must preserve both SAT and UNSAT
results, including actions with function-valued nondeterministic choices.
These checks exercise the production `veil_bmc` tactic without an override.
-/

open Lean Meta Elab Tactic Veil

meta section

partial def introDataPrefix (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let .forallE _ domain _ _ := target.consumeMData | return goal
  if ← isProp domain then return goal
  let (_, goal') ← withOptions (fun opts => opts.setBool `tactic.hygienic false) goal.intro1
  introDataPrefix goal'

elab "intro_data_prefix" : tactic => do
  liftMetaTactic1 fun goal => return some (← introDataPrefix goal)

def bmcDataPrefix : DesugarTacticM Unit := veilWithMainContext do
  let dsimpLemmas := #[mkIdent ``Inhabited.default, fieldAbstractDispatcher,
    fieldLabelToDomain stateName, fieldLabelToCodomain stateName]
  let dsimpTac ← `(tactic| try dsimp +$(mkIdent `instances) [$[$dsimpLemmas:ident],*])
  let inferNonemptyTac ← if veil.smt.trust.get (← getOptions) then
    `(tactic| skip)
  else `(tactic| veil_infer_nonempty)
  let tac ← `(tacticSeq|
    intro_data_prefix
    $inferNonemptyTac:tactic
    veil_simp +$(mkIdent `instances) only [$(mkIdent `nextSimp):ident]
    veil_simp +$(mkIdent `instances) only [↓ $(mkIdent ``existsQuantifierSimpGuarded):ident]
    veil_intros
    $inferNonemptyTac:tactic
    veil_destruct
    $dsimpTac:tactic
    veil_simp +$(mkIdent `instances) only [$(mkIdent `smtSimp):ident]
    $dsimpTac:tactic
    veil_smt)
  veilEvalTactic tac

elab_rules : tactic
  | `(tactic| veil_bmc) => do
    Veil.DesugarTacticM.runByOption (← getRef) bmcDataPrefix

end

veil module TraceEarlyIntroduction

type node
relation marked : node → Bool

after_init { marked N := false }

action fill {
  let f ← pick (node → Bool)
  require ∀ n, f n
  marked N := f N
}

action clear { marked N := false }

invariant True

#gen_spec

section TrustedChecks

set_option veil.smt.trust true

-- A real higher-order choice must remain available to the solver.
#guard_msgs(drop info, drop warning) in
sat trace [fill_all] {
  fill
  assert (∀ n, marked n)
}

#guard_msgs(drop info, drop warning) in
unsat trace [fill_cannot_leave_unmarked] {
  fill
  assert (∃ n, ¬ marked n)
}

#guard_msgs(drop info, drop warning) in
sat trace [choose_fill] {
  any 3 actions
  assert (∃ n, marked n)
}

#guard_msgs(drop info, drop warning) in
unsat trace [always_uniform] {
  any 3 actions
  assert ((∃ n, marked n) ∧ (∃ n, ¬ marked n))
}

end TrustedChecks

-- Repeat with proof reconstruction enabled for UNSAT results.
section UntrustedChecks

set_option veil.smt.trust false

#guard_msgs(drop info, drop warning) in
sat trace [fill_all_untrusted] {
  fill
  assert (∀ n, marked n)
}

#guard_msgs(drop info, drop warning) in
unsat trace [fill_cannot_leave_unmarked_untrusted] {
  fill
  assert (∃ n, ¬ marked n)
}

#guard_msgs(drop info, drop warning) in
sat trace [choose_fill_untrusted] {
  any 3 actions
  assert (∃ n, marked n)
}

#guard_msgs(drop info, drop warning) in
unsat trace [always_uniform_untrusted] {
  any 3 actions
  assert ((∃ n, marked n) ∧ (∃ n, ¬ marked n))
}

-- A manual trace proof must close every goal. The automatic trace discharger
-- can report an SMT result without retaining a complete Lean proof.
unsat trace [fill_cannot_leave_unmarked_checked] {
  fill
  assert (∃ n, ¬ marked n)
} by
  veil_bmc

/-- info: 'TraceEarlyIntroduction.fill_cannot_leave_unmarked_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fill_cannot_leave_unmarked_checked

end UntrustedChecks

end TraceEarlyIntroduction
