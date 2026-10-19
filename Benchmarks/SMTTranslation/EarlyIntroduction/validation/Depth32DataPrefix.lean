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

veil module DeepBmcTranslation

type node
relation marked : node → Bool
relation edge : node → node → Bool
individual failed : Bool

#gen_state

after_init {
  marked N := false
  edge N M := false
  failed := false
}

action mark (n m : node) {
  marked n := true
  edge n m := true
}

action clear (n m : node) {
  marked n := false
  edge n m := false
}

invariant ¬ failed
#gen_spec

-- This checks that the ordinary BMC pipeline reaches a real UNSAT solver result
-- at a larger depth. Before the early-introduction fix, global normalization
-- under the state binders exhausted simp's default 100,000-step budget here.
-- The two actions change the relations but preserve `failed = false`, keeping
-- solving easy even though preprocessing must traverse every transition.
-- Use the default trusted solver path for this scaling regression; separate
-- semantic tests cover proof reconstruction. No resource limit is raised.
set_option veil.smt.trust true
#guard_msgs(drop info, drop warning) in
unsat trace [failed_unreachable] {
  any 32 actions
  assert failed
}

end DeepBmcTranslation
