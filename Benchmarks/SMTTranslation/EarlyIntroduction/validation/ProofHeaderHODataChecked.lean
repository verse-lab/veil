module
public import Veil

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

veil module TraceProofHeaderHO

type node
individual flag : Bool
#gen_state
after_init { flag := false }
action stay { pure () }
invariant True
#gen_spec

set_option veil.smt.trust false

unsat trace [header_unsat]
    (h : (∃ f : node → Bool, ∀ n, f n) ∨ (∃ g : node → Bool, ∀ n, ¬ g n)) {
  stay
  assert flag
} by
  veil_bmc

#print axioms header_unsat

end TraceProofHeaderHO
